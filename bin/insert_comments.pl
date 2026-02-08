#!/usr/bin/env perl
use strict;
use warnings;
use utf8;
use open qw(:std :utf8);

# Usage:
#   perl insert_comments.pl source.txt input.html output.html [start|next] [offset]
#
# start|next:
#   start = attach to the line where the comment begins
#   next  = attach to the next line (useful if comment is above what it describes)
#
# offset:
#   integer added to computed source line numbers (for excerpt alignment)

my ($srcfile, $htmlin, $htmlout, $attach, $offset) = @ARGV;
die "Usage: $0 source.txt input.html output.html [start|next] [offset]\n"
  unless defined $htmlout;

$attach ||= "start";
$offset ||= 0;
die "attach must be 'start' or 'next'\n"
  unless $attach eq "start" || $attach eq "next";

sub slurp {
  my ($path) = @_;
  open my $fh, "<:raw", $path or die "Can't open $path: $!";
  local $/;
  my $data = <$fh>;
  close $fh;
  return $data;
}

sub html_escape {
  my ($s) = @_;
  $s =~ s/&/&amp;/g;
  $s =~ s/</&lt;/g;
  $s =~ s/>/&gt;/g;
  $s =~ s/"/&quot;/g;
  $s =~ s/'/&#39;/g;
  return $s;
}

sub comment_html {
  my ($c) = @_;
  my $safe = html_escape($c);
  $safe =~ s/\R/<br\/>/g;
  return qq{<div class="proof-comment" style="color:#666; font-style:italic; margin:0.25em 0 0.45em 2.2em;">(*** $safe ***)</div>\n};
}

# Block-ish tags we are willing to insert AFTER to ensure "below"
my %BLOCK = map { $_ => 1 } qw(
  div p li ul ol pre section article header footer nav aside
  table thead tbody tfoot tr td th
  blockquote figure figcaption
);

my $src  = slurp($srcfile);
my $html = slurp($htmlin);

# ------------------------------------------------------------
# 1) Collect multiline comments keyed by desired line number
#    Supports (** ... **), (*** ... ***), etc.
# ------------------------------------------------------------
my %comments_by_line;
while ($src =~ m/\(\*{2,}(.*?)\*{2,}\)/sg) {
  my $inner = $1;

  my $start_pos  = $-[0];
  my $start_line = (substr($src, 0, $start_pos) =~ tr/\n/\n/) + 1;

  my $line = ($attach eq "start") ? $start_line : ($start_line + 1);
  $line += $offset;

  $inner =~ s/^\s+//;
  $inner =~ s/\s+$//;
  push @{ $comments_by_line{$line} }, $inner if length $inner;
}

# If no comments, copy through
if (!keys %comments_by_line) {
  open my $out, ">:raw", $htmlout or die "Can't write $htmlout: $!";
  print {$out} $html;
  close $out;
  exit 0;
}

# ------------------------------------------------------------
# 2) Parse HTML tags with a stack to find srcline anchors and their enclosing block
#    We build "nodes" for tags with start/end positions for block tags.
# ------------------------------------------------------------
my @stack;  # each elem: { tag => 'div', start => pos, end => pos (later), id => idx }
my @nodes;  # nodes by id: { tag,start,end,parent }
my @anchors;# anchors: { line => N, container_id => nodeid, container_start => pos, container_end => pos }

sub push_node {
  my ($tag, $start, $parent) = @_;
  my $id = scalar(@nodes);
  $nodes[$id] = { tag => $tag, start => $start, end => undef, parent => $parent };
  push @stack, { tag => $tag, start => $start, id => $id };
  return $id;
}

sub pop_node {
  my ($tag, $endpos) = @_;
  # pop until matching tag (HTML can be messy; do best-effort)
  for (my $i = $#stack; $i >= 0; $i--) {
    if (lc($stack[$i]{tag}) eq lc($tag)) {
      my $id = $stack[$i]{id};
      $nodes[$id]{end} = $endpos;
      splice(@stack, $i); # remove this and anything after (should be top)
      return $id;
    }
  }
  return undef;
}

sub current_parent_id {
  return @stack ? $stack[-1]{id} : undef;
}

sub find_enclosing_block_id {
  # Walk up from current parent, pick nearest BLOCK tag if possible
  my ($from_id) = @_;
  my $id = $from_id;
  while (defined $id) {
    my $tag = lc($nodes[$id]{tag});
    return $id if $BLOCK{$tag};
    $id = $nodes[$id]{parent};
  }
  return $from_id; # fallback: whatever we had (may be undef)
}

# Regex to iterate tags; captures:
#  $1 = '/' if closing, else ''
#  $2 = tag name
#  $3 = attributes (optional)
#  $4 = '/' if self-closing, else ''
my $tagre = qr{<\s*(/?)\s*([A-Za-z0-9]+)([^>]*?)(/?)\s*>}s;

pos($html) = 0;
while ($html =~ /$tagre/g) {
  my $is_close = $1;
  my $tag      = $2;
  my $attrs    = $3 // '';
  my $self     = $4;

  my $tag_start = $-[0];
  my $tag_end   = $+[0];

  my $ltag = lc($tag);

  if ($is_close) {
    pop_node($ltag, $tag_end);
    next;
  }

  # opening tag
  my $parent = current_parent_id();
  my $id = push_node($ltag, $tag_start, $parent);

  # Detect srcline span
  if ($ltag eq 'span') {
    # tolerant attribute matching: class contains srcline, data-line is number
    if ($attrs =~ /class\s*=\s*(['"])(.*?)\1/is) {
      my $class = $2;
      if ($class =~ /\bsrcline\b/i && $attrs =~ /data-line\s*=\s*(['"])(\d+)\1/is) {
        my $ln = $2;

        # choose enclosing block: nearest BLOCK ancestor (prefer div etc.)
        my $container_id = find_enclosing_block_id($parent);

        # If we didn't find any container, fall back to this span itself
        $container_id = $id unless defined $container_id;

        push @anchors, { line => $ln, container_id => $container_id };
      }
    }
  }

  # self-closing tags: immediately close
  if ($self && $self eq '/') {
    pop_node($ltag, $tag_end);
  }
}

# Fill container start/end for anchors; discard anchors whose container has no end
my @containers;
for my $a (@anchors) {
  my $cid = $a->{container_id};
  next unless defined $cid;
  my $st = $nodes[$cid]{start};
  my $en = $nodes[$cid]{end};
  next unless defined $st && defined $en;
  push @containers, { line => $a->{line}, start => $st, end => $en };
}

die "No srcline containers found in HTML (couldn't locate span.srcline data-line)\n"
  unless @containers;

# Sort by line (and start position as tie-break)
@containers = sort {
  $a->{line} <=> $b->{line} || $a->{start} <=> $b->{start}
} @containers;

# Map: exact line -> insertion pos AFTER container
my %exact_after;
for my $c (@containers) {
  $exact_after{$c->{line}} = $c->{end}; # last wins if duplicates
}

sub first_container_with_line_gt {
  my ($L) = @_;
  my ($lo, $hi) = (0, $#containers);
  my $ans;
  while ($lo <= $hi) {
    my $mid = int(($lo + $hi) / 2);
    if ($containers[$mid]{line} > $L) {
      $ans = $containers[$mid];
      $hi = $mid - 1;
    } else {
      $lo = $mid + 1;
    }
  }
  return $ans;
}

# ------------------------------------------------------------
# 3) Decide insertion positions (never drop comments):
#    exact match => after container end (so comment is below)
#    else        => before first container with greater line (at container start)
#    else        => before </body> or EOF
# ------------------------------------------------------------
my %insert_at; # pos -> [snippets...]

for my $L (sort { $a <=> $b } keys %comments_by_line) {
  my $pos;
  if (exists $exact_after{$L}) {
    $pos = $exact_after{$L};
  } else {
    my $next = first_container_with_line_gt($L);
    if ($next) {
      $pos = $next->{start};  # before the next block
    } else {
      if ($html =~ m{</body>}i) {
        $pos = $-[0];
      } else {
        $pos = length($html);
      }
    }
  }

  for my $c (@{ $comments_by_line{$L} }) {
    push @{ $insert_at{$pos} }, comment_html($c);
  }
}

# ------------------------------------------------------------
# 4) Apply insertions in one pass
# ------------------------------------------------------------
my @positions = sort { $a <=> $b } keys %insert_at;
my $out = "";
my $cursor = 0;

for my $p (@positions) {
  $p = 0 if $p < 0;
  $p = length($html) if $p > length($html);

  $out .= substr($html, $cursor, $p - $cursor);
  $out .= join("", @{ $insert_at{$p} });
  $cursor = $p;
}
$out .= substr($html, $cursor);

open my $fh, ">:raw", $htmlout or die "Can't write $htmlout: $!";
print {$fh} $out;
close $fh;
