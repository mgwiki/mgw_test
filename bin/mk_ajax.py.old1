#!/usr/bin/env python3
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
"""

def ensure_dir(p: Path) -> None:
    p.mkdir(parents=True, exist_ok=True)

def sanitize(s: str) -> str:
    s = (s or "").strip()
    s = SAFE_NAME_RE.sub("_", s)
    s = s.strip("._-")
    return s or "x"

def serialize_inner_html(el: etree._Element) -> str:
    parts: list[str] = []
    if el.text:
        parts.append(el.text)
    for ch in el:
        parts.append(html.tostring(ch, encoding="unicode", method="html"))
    return "".join(parts)

def drop_all_children(el: etree._Element) -> None:
    for ch in list(el):
        el.remove(ch)
    el.text = None

def inject_ajax_js_once(doc_root: etree._Element) -> None:
    if doc_root.xpath(".//script[contains(., 'window.loadProof')]"):
        return
    bodies = doc_root.xpath(".//body")
    target = bodies[0] if bodies else doc_root
    for node in html.fragments_fromstring(AJAX_JS):
        if isinstance(node, etree._Element):
            target.append(node)

def nearest_theorem_id(proof_div: etree._Element) -> str | None:
    """
    Find a stable theorem id for this proof.
    Prefer: nearest ancestor .thmandproof's <a name="..."> (usually right above).
    Fallback: first href="#..." in the theorem declaration.
    """
    thm_blocks = proof_div.xpath(
        "ancestor::div[contains(concat(' ', normalize-space(@class), ' '), ' thmandproof ')][1]"
    )
    if not thm_blocks:
        return None
    thm = thm_blocks[0]

    name_anchors = thm.xpath(".//a[@name]")
    if name_anchors:
        # in your structure this is typically exactly the theorem id
        return name_anchors[-1].get("name")

    decls = thm.xpath(".//div[contains(concat(' ', normalize-space(@class), ' '), ' thmdecl ')]")
    scope = decls[0] if decls else thm
    a = scope.xpath(".//a[starts-with(@href, '#')][1]")
    if a:
        href = (a[0].get("href") or "").lstrip("#")
        return href or (a[0].text or None)

    return None

def main() -> int:
    if len(sys.argv) < 2 or len(sys.argv) > 3:
        print("Usage: python3 tools/proofs_to_ajax_docprefixed.py docs/topology.mg.html [docs/proofs]", file=sys.stderr)
        return 2

    in_path = Path(sys.argv[1])
    proofs_root = Path(sys.argv[2]) if len(sys.argv) == 3 else (in_path.parent / "proofs")

    # doc prefix: "topology.mg" from "topology.mg.html"
    doc_prefix = sanitize(in_path.name[:-5] if in_path.name.endswith(".html") else in_path.stem)

    out_dir = proofs_root / doc_prefix
    ensure_dir(out_dir)

    data = in_path.read_bytes()
    parser = html.HTMLParser(encoding="utf-8", huge_tree=True)
    doc = html.fromstring(data, parser=parser)

    proofs = doc.xpath(".//div[contains(concat(' ', normalize-space(@class), ' '), ' proof ')][@id]")
    extracted = 0
    used_names: dict[str, int] = {}

    for proof in proofs:
        pres_list = proof.xpath(".//div[contains(concat(' ', normalize-space(@class), ' '), ' proofpres ')]")
        if not pres_list:
            continue
        pres = pres_list[0]

        inner = serialize_inner_html(pres)
        inner = re.sub(
            r"^\s*<b>\s*Proof:\s*</b>\s*(?:<br\s*/?>)?\s*",
            "",
            inner,
            flags=re.IGNORECASE,
        )

        thm_id = nearest_theorem_id(proof) or proof.get("id") or "proof"
        base = sanitize(thm_id)

        # avoid collisions within same doc
        k = used_names.get(base, 0)
        used_names[base] = k + 1
        filename = f"{base}.html" if k == 0 else f"{base}__{k+1}.html"

        proof_file = out_dir / filename
        proof_file.write_text(inner, encoding="utf-8")

        # rewrite to loader stub
        drop_all_children(pres)
        pres.attrib.pop("onclick", None)

        # IMPORTANT: src should be relative to the HTML file location
        # HTML is in docs/, proof files in docs/proofs/<doc_prefix>/...
        rel = proof_file.relative_to(in_path.parent).as_posix()
        proof.set("data-proof-src", rel)
        proof.set("data-proof-loaded", "0")

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

        extracted += 1

    inject_ajax_js_once(doc)

    out_bytes = html.tostring(doc, encoding="utf-8", method="html", with_tail=False)
    in_path.write_bytes(out_bytes)

    print(f"Extracted {extracted} proofs into: {out_dir}", file=sys.stderr)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
