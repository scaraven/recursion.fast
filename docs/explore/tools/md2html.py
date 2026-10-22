#!/usr/bin/env python3
"""Convert the exploration report's Markdown subset to an HTML fragment plus a table of contents.

Supported: ATX headings (#, ##, ###), paragraphs, '---' rules, fenced code blocks, pipe tables,
bullet and numbered lists nested by indentation (continuation lines join the item), inline code,
**bold**, *italic*, [text](url). Evidence words in bold (kernel, paper, measured, estimate) become
chips. Usage: md2html.py REPORT.md OUT_BODY.html OUT_TOC.html
"""
import html
import re
import sys

EVIDENCE = {"kernel", "paper", "measured", "estimate"}


def slug(text):
    s = re.sub(r"<[^>]+>", "", text)
    s = re.sub(r"[^a-z0-9]+", "-", s.lower()).strip("-")
    return "s-" + (s[:48] or "x")


def inline(text):
    parts = re.split(r"(`[^`]*`)", text)
    out = []
    for p in parts:
        if p.startswith("`") and p.endswith("`") and len(p) >= 2:
            out.append("<code>" + html.escape(p[1:-1]) + "</code>")
            continue
        t = html.escape(p, quote=False)
        t = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", r'<a href="\2">\1</a>', t)

        def bold(m):
            inner = m.group(1)
            if inner.lower() in EVIDENCE:
                return f'<span class="ev ev-{inner.lower()}">{inner}</span>'
            return f"<strong>{inner}</strong>"

        t = re.sub(r"\*\*(.+?)\*\*", bold, t)
        t = re.sub(r"(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])", r"<em>\1</em>", t)
        out.append(t)
    return "".join(out)


def split_row(line):
    line = line.strip()
    if line.startswith("|"):
        line = line[1:]
    if line.endswith("|"):
        line = line[:-1]
    cells, cur, in_code = [], "", False
    i = 0
    while i < len(line):
        ch = line[i]
        if ch == "`":
            in_code = not in_code
        if ch == "|" and not in_code:
            cells.append(cur.strip())
            cur = ""
        else:
            cur += ch
        i += 1
    cells.append(cur.strip())
    return cells


LIST_RE = re.compile(r"^(\s*)([-*]|\d+\.)\s+(.*)$")


def render_list(lines):
    """lines: list of (indent, marker, text) items with continuation already joined."""
    out = []
    stack = []  # (indent, tag)
    for indent, marker, text in lines:
        tag = "ol" if marker[0].isdigit() else "ul"
        while stack and indent < stack[-1][0]:
            out.append("</li></%s>" % stack.pop()[1])
        if stack and indent == stack[-1][0]:
            out.append("</li>")
            if tag != stack[-1][1]:
                out.append("</%s><%s>" % (stack[-1][1], tag))
                stack[-1] = (indent, tag)
        elif not stack or indent > stack[-1][0]:
            start = ""
            if tag == "ol" and marker.rstrip(".") != "1":
                start = ' start="%s"' % marker.rstrip(".")
            out.append("<%s%s>" % (tag, start))
            stack.append((indent, tag))
        out.append("<li>" + inline(text))
    while stack:
        out.append("</li></%s>" % stack.pop()[1])
    return "".join(out)


def convert(md):
    lines = md.split("\n")
    out, toc = [], []
    i = 0
    title_done = False
    while i < len(lines):
        line = lines[i]
        if not line.strip():
            i += 1
            continue
        if line.startswith("```"):
            lang = line[3:].strip()
            j = i + 1
            buf = []
            while j < len(lines) and not lines[j].startswith("```"):
                buf.append(lines[j])
                j += 1
            out.append('<pre class="code" data-lang="%s"><code>%s</code></pre>'
                       % (html.escape(lang), html.escape("\n".join(buf))))
            i = j + 1
            continue
        m = re.match(r"^(#{1,3})\s+(.*)$", line)
        if m:
            level = len(m.group(1))
            text = inline(m.group(2))
            if level == 1 and not title_done:
                out.append('<h1 id="top">%s</h1>' % text)
                title_done = True
            else:
                sid = slug(text)
                out.append('<h%d id="%s">%s</h%d>' % (level, sid, text, level))
                if level in (2, 3):
                    toc.append((level, sid, re.sub(r"<[^>]+>", "", text)))
            i += 1
            continue
        if line.strip() == "---":
            out.append("<hr>")
            i += 1
            continue
        if line.lstrip().startswith("|"):
            rows = []
            while i < len(lines) and lines[i].lstrip().startswith("|"):
                rows.append(lines[i])
                i += 1
            header = split_row(rows[0])
            body = [split_row(r) for r in rows[2:]]
            t = ['<div class="table-wrap"><table><thead><tr>']
            t += ["<th>%s</th>" % inline(c) for c in header]
            t.append("</tr></thead><tbody>")
            for r in body:
                t.append("<tr>" + "".join("<td>%s</td>" % inline(c) for c in r) + "</tr>")
            t.append("</tbody></table></div>")
            out.append("".join(t))
            continue
        if LIST_RE.match(line):
            items = []
            while i < len(lines):
                l = lines[i]
                if not l.strip():
                    # a blank line ends the list unless the next line continues it
                    if i + 1 < len(lines) and LIST_RE.match(lines[i + 1]) and \
                            len(lines[i + 1]) - len(lines[i + 1].lstrip()) > 0:
                        i += 1
                        continue
                    break
                lm = LIST_RE.match(l)
                if lm:
                    items.append([len(lm.group(1)), lm.group(2), lm.group(3)])
                elif items and (l.startswith(" ") or l.startswith("\t")):
                    items[-1][2] += " " + l.strip()
                else:
                    break
                i += 1
            out.append(render_list([tuple(x) for x in items]))
            continue
        buf = []
        while i < len(lines) and lines[i].strip() and not lines[i].startswith("#") \
                and not lines[i].startswith("```") and not lines[i].lstrip().startswith("|") \
                and not LIST_RE.match(lines[i]) and lines[i].strip() != "---":
            buf.append(lines[i].strip())
            i += 1
        out.append("<p>%s</p>" % inline(" ".join(buf)))
    toc_html = ['<ol class="toc">']
    open_sub = False
    for level, sid, text in toc:
        if level == 2:
            if open_sub:
                toc_html.append("</ol></li>")
                open_sub = False
            elif len(toc_html) > 1:
                toc_html.append("</li>")
            toc_html.append('<li><a href="#%s">%s</a>' % (sid, text))
        else:
            if not open_sub:
                toc_html.append("<ol>")
                open_sub = True
            toc_html.append('<li><a href="#%s">%s</a></li>' % (sid, text))
    if open_sub:
        toc_html.append("</ol>")
    toc_html.append("</li></ol>")
    return "\n".join(out), "".join(toc_html)


if __name__ == "__main__":
    src, out_body, out_toc = sys.argv[1:4]
    with open(src, encoding="utf-8") as f:
        body, toc = convert(f.read())
    with open(out_body, "w", encoding="utf-8") as f:
        f.write(body)
    with open(out_toc, "w", encoding="utf-8") as f:
        f.write(toc)
