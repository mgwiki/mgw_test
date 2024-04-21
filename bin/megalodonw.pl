#!/usr/bin/perl -w
use strict;

my $mgbinary = "./bin/megalodon"; # location of megalodon

my $tl = 1 + shift @ARGV; # the first argument is the time limit
my $mgfile = shift @ARGV; # the second argument is the .mg file to be checked (it may be repeated later in the regular megalodon command)
my $mginclude = ""; # the includes we will collect from $mgfile - can be empty or contain multiple -I .mgs

open(F,$mgfile) or die "File not readable: $mgfile";

# collect the includes
while(<F>)
  {
    if(m/^\s*\(\*\*\s+\$I\s+(\S+)\s+\*\*\)\s*/) { $mginclude = $mginclude . "-I $1 ";}
  }

exec("timeout -k1 $tl  $mgbinary $mginclude @ARGV ");
