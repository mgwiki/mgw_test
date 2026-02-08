#!/usr/bin/env python3
"""
mk_ajax.py — Extract Proofgold proofs into external HTML files + replace inline proofs with an AJAX loader.

This version supports the *new* layout where proof steps are NOT inside `.proofpres`,
but instead appear as siblings inside the `.proof` div (e.g. `div.pftacwrap` with `span.srcline`).

Key behaviors:
- For each <div class="proof" id="pfNNN"> ... </div>, find the surrounding theorem id and write
  the proof payload to:  proofs/<docprefix>/<theorem-id>.html
- Replace the inline proof content with a small "Load proof" button.
- Remove extracted proof payload nodes from the main HTML to shrink it.
- Remove any `div.proofcodehidden` blocks (they're usually placeholders now).
- Avoid overwriting an existing proof file with empty content (important if run twice).

Requires: lxml
  pip3 install lxml
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from lxml import html, etree

SAFE_NAME_RE = re.compile(r"[^A-Za-z0-9._-]+")

AJAX_JS = r"""
<script>
(function(){
  async function loadProof(btn){
    const proof = btn.closest('.proof');
    if (!proof) return;
    const src = proof.getAttribute('data-proof-src');
    if (!src) return;

    const status = proof.querySelector('.proofstatus');
    const target = proof.querySelector('.proofcontent');
    if (!target) return;

    if (proof.getAttribute('data-proof-loaded') === '1') {
      const isHidden = target.style.display === 'none';
      target.style.display = isHidden ? '' : 'none';
      if (status) status.textContent = isHidden ? 'Proof loaded.' : 'Proof hidden.';
      btn.textContent = isHidden ? 'Hide proof' : 'Show proof';
      return;
    }

    btn.disabled = true;
    if (status) status.textContent = 'Loading…';
    try {
      const r = await fetch(src, {cache: 'force-cache'});
      if (!r.ok) throw new Error('HTTP ' + r.status);
      const t = await r.text();
      target.innerHTML = t;
      proof.setAttribute('data-proof-loaded', '1');
      btn.textContent = 'Hide proof';
      if (status) status.textContent = 'Proof loaded.';
    } catch(e) {
      if (status) status.textContent = 'Failed to load proof: ' + e;
    } finally {
      btn.disabled = false;
    }
  }
  window.loadProof = loadProof;
})();
</script>
""".strip()


def ensure_dir(p: Path) -> None:
    p.mkdir(parents=True, exist_ok=True)


def sanitize(s: str) -> str:
    s = (s or "").strip()
    s = SAFE_NAME_RE.sub("_", s)
    s = s.strip("._-")
    return s or "x"


def merge_classes(existing: str | None, add: str | None) -> str:
    ex = (existing or "").split()
    ad = (add or "").split()
    merged = []
    seen = set()
    for c in ex + ad:
        if c and c not in seen:
            merged.append(c)
            seen.add(c)
    return " ".join(merged)


def has_class(el: etree._Element, cls: str) -> bool:
    return cls in ((el.get("class") or "").split())


def serialize_inner_html(el: etree._Element) -> str:
    """Serialize el.innerHTML (text + children) to a string."""
    parts: list[str] = []
    if el.text:
        parts.append(el.text)
    for ch in el:
        parts.append(html.tostring(ch, encoding="unicode", method="html"))
    return "".join(parts)


def serialize_nodes(nodes: list[etree._Element]) -> str:
    return "".join(html.tostring(n, encoding="unicode", method="html") for n in nodes)


def drop_all_children(el: etree._Element) -> None:
    for ch in list(el):
        el.remove(ch)
    el.text = None


def inject_ajax_js_once(doc_root: etree._Element) -> None:
    """Inject the loader JS at end of <body> (or root if no body), only once."""
    if doc_root.xpath(".//script[contains(., 'window.loadProof')]"):
        return
    bodies = doc_root.xpath(".//body")
    target = bodies[0] if bodies else doc_root
    for node in html.fragments_fromstring(AJAX_JS):
        if isinstance(node, etree._Element):
            target.append(node)


def nearest_theorem_id(proof_div: etree._Element) -> str | None:
    """
    Find a stable theorem identifier for this proof.

    Preferred: nearest ancestor .thmandproof's anchor: <a name="..."></a> or <a name="..."/>
    Fallback: first internal href="#..." in the theorem declaration.
    """
    thm_blocks = proof_div.xpath(
        "ancestor::div[contains(concat(' ', normalize-space(@class), ' '), ' thmandproof ')][1]"
    )
    if not thm_blocks:
        return None
    thm = thm_blocks[0]

    # <a name="..."></a> or <a name="..."/>
    name_anchors = thm.xpath(".//a[@name]")
    if name_anchors:
        # Usually the first is the theorem id; last is safer if multiple anchors exist
        return name_anchors[-1].get("name")

    # fallback: first <a href="#..."> in declaration
    decls = thm.xpath(".//div[contains(concat(' ', normalize-space(@class), ' '), ' thmdecl ')]")
    scope = decls[0] if decls else thm
    a = scope.xpath(".//a[starts-with(@href, '#')][1]")
    if a:
        href = (a[0].get("href") or "").lstrip("#")
        return href or (a[0].text or None)

    return None


def ensure_loader_stub(pres: etree._Element) -> None:
    """
    Replace proofpres content with loader UI (small).
    """
    drop_all_children(pres)
    pres.attrib.pop("onclick", None)

    label = etree.Element("b")
    label.text = "Proof:"
    br = etree.Element("br")

    btn = etree.Element("button")
    btn.set("type", "button")
    btn.set("class", "proofload")
    btn.set("onclick", "loadProof(this)")
    btn.text = "Load proof"

    status = etree.Element("span")
    status.set("class", "proofstatus")
    status.text = " Proof not loaded."

    content = etree.Element("div")
    content.set("class", "proofcontent")

    pres.append(label)
    pres.append(br)
    pres.append(btn)
    pres.append(status)
    pres.append(content)


def main() -> int:
    if len(sys.argv) < 2 or len(sys.argv) > 3:
        print("Usage: python3 mk_ajax.py docs/Part1.mg.html [docs/proofs]", file=sys.stderr)
        return 2

    in_path = Path(sys.argv[1])
    proofs_root = Path(sys.argv[2]) if len(sys.argv) == 3 else (in_path.parent / "proofs")

    # doc prefix: "Part10.mg" from "Part10.mg.html" (strip trailing .html)
    doc_prefix = sanitize(in_path.name[:-5] if in_path.name.endswith(".html") else in_path.stem)
    out_dir = proofs_root / doc_prefix
    ensure_dir(out_dir)

    data = in_path.read_bytes()
    parser = html.HTMLParser(encoding="utf-8", huge_tree=True)
    doc = html.fromstring(data, parser=parser)

    # Optional: fix bogus attribute "classname" -> merge into "class"
    for el in doc.xpath(".//*[@classname]"):
        cn = el.get("classname")
        if cn:
            el.set("class", merge_classes(el.get("class"), cn))
        del el.attrib["classname"]

    proofs = doc.xpath(".//div[contains(concat(' ', normalize-space(@class), ' '), ' proof ')][@id]")
    used_names: dict[str, int] = {}

    extracted = 0
    skipped_empty = 0
    removed_pfcode = 0
    rewritten = 0

    for proof in proofs:
        pfid = (proof.get("id") or "").strip()
        if not pfid:
            continue

        # find proofpres (should exist)
        pres_list = proof.xpath(".//div[contains(concat(' ', normalize-space(@class), ' '), ' proofpres ')]")
        if not pres_list:
            continue
        pres = pres_list[0]

        # Choose stable theorem id
        thm_id = nearest_theorem_id(proof) or pfid
        base = sanitize(thm_id)

        # avoid collisions within same doc
        k = used_names.get(base, 0)
        used_names[base] = k + 1
        filename = f"{base}.html" if k == 0 else f"{base}__{k+1}.html"
        proof_file = out_dir / filename

        # Ensure data-proof-src points to proofs/<docprefix>/<filename>
        rel = proof_file.relative_to(in_path.parent).as_posix()
        proof.set("data-proof-src", rel)
        proof.set("data-proof-loaded", proof.get("data-proof-loaded") or "0")

        # --- NEW EXTRACTION LOGIC ---
        # Prefer: everything inside `.proof` that is NOT `.proofpres` and NOT `.proofcodehidden`.
        payload_nodes = [ch for ch in list(proof) if ch is not pres and not has_class(ch, "proofcodehidden")]
        payload_html = serialize_nodes(payload_nodes).strip()

        # Fallback: old layout (payload inside pres)
        if not payload_html:
            payload_html = serialize_inner_html(pres)
            payload_html = re.sub(
                r"^\s*<b>\s*Proof:\s*</b>\s*(?:<br\s*/?>)?\s*",
                "",
                payload_html,
                flags=re.IGNORECASE,
            ).strip()

        # Don't overwrite existing proof files with empty content (important if script runs twice)
        if payload_html:
            proof_file.write_text(payload_html, encoding="utf-8")
            extracted += 1
        else:
            skipped_empty += 1

        # Remove extracted siblings from main doc so it shrinks
        for ch in payload_nodes:
            proof.remove(ch)

        # Remove any proofcodehidden blocks (now useless placeholders) anywhere inside this proof
        for code_div in proof.xpath(".//div[contains(concat(' ', normalize-space(@class), ' '), ' proofcodehidden ')]"):
            parent = code_div.getparent()
            if parent is not None:
                parent.remove(code_div)
                removed_pfcode += 1

        # Replace proofpres with loader UI
        ensure_loader_stub(pres)
        rewritten += 1

    inject_ajax_js_once(doc)

    out_bytes = html.tostring(doc, encoding="utf-8", method="html", with_tail=False)
    in_path.write_bytes(out_bytes)

    print(
        f"Rewrote {rewritten} proofs; wrote {extracted} external files to {out_dir}; "
        f"skipped {skipped_empty} empty payloads; removed {removed_pfcode} proofcodehidden blocks.",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
