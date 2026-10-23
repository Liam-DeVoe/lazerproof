#!/usr/bin/env python3
"""Render project status (STATE.md, DECISIONS.md, metrics, git log) into status/www/index.html."""
import html, json, os, re, subprocess, datetime, pathlib
ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "status" / "www" / "index.html"

def md(text):
    out, in_code, in_list = [], False, False
    for line in text.splitlines():
        if line.startswith("```"):
            out.append("</pre>" if in_code else "<pre>"); in_code = not in_code; continue
        if in_code: out.append(html.escape(line)); continue
        esc = html.escape(line)
        esc = re.sub(r"`([^`]+)`", r"<code>\1</code>", esc)
        esc = re.sub(r"\*\*([^*]+)\*\*", r"<b>\1</b>", esc)
        m = re.match(r"^(#+) (.*)", esc)
        is_item = re.match(r"^\s*([-*]|\d+\.) ", line)
        if in_list and not is_item and not line.startswith("  "):
            out.append("</ul>"); in_list = False
        if m: out.append(f"<h{len(m.group(1))+1}>{m.group(2)}</h{len(m.group(1))+1}>")
        elif is_item:
            if not in_list: out.append("<ul>"); in_list = True
            out.append("<li>" + re.sub(r"^\s*([-*]|\d+\.) ", "", esc) + "</li>")
        elif line.strip(): out.append(f"<p>{esc}</p>")
    if in_list: out.append("</ul>")
    return "\n".join(out)

def read(p):
    p = ROOT / p
    return p.read_text() if p.exists() else ""

def sh(cmd):
    try: return subprocess.run(cmd, shell=True, cwd=ROOT, capture_output=True, text=True, timeout=20).stdout
    except Exception as e: return str(e)

metrics = {}
mp = ROOT / "status" / "metrics.json"
if mp.exists():
    try: metrics = json.loads(mp.read_text())
    except Exception: pass

try:
    metrics["replays on disk"] = len(list((ROOT/"data"/"replays").glob("*.osr")))
    metrics["beatmaps on disk"] = len(list((ROOT/"data"/"beatmaps").glob("*.osu")))
    out = sh("vmstat 3 2 | tail -1").split()
    if len(out) >= 17:
        metrics["cpu (3s sample): user/sys/idle/iowait/steal %"] = "/".join(out[12:17])
    metrics["crawler running"] = "yes" if "fetch_v1.py" in sh("pgrep -af fetch_v1.py") else "no"
except Exception: pass
now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
rows = "".join(f"<tr><td>{html.escape(str(k))}</td><td>{html.escape(str(v))}</td></tr>" for k, v in metrics.items())
docs = sorted((ROOT / "docs").glob("*.md")) if (ROOT / "docs").exists() else []
doc_html = "".join(f"<details><summary>docs/{d.name}</summary>{md(d.read_text())}</details>" for d in docs)
page = f"""<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="refresh" content="300"><title>lazerproof status</title>
<style>
:root{{--bg:#fbfaf8;--fg:#1d1d1f;--mut:#6b6b70;--line:#e3e1dc;--acc:#c2185b}}
@media (prefers-color-scheme:dark){{:root{{--bg:#16161a;--fg:#e9e9ec;--mut:#9a9aa3;--line:#2c2c33;--acc:#f06292}}}}
body{{background:var(--bg);color:var(--fg);font:15px/1.55 system-ui,sans-serif;margin:0;padding:24px 16px}}
main{{max-width:920px;margin:auto}} h1{{margin:0 0 4px}} .mut{{color:var(--mut)}}
h2,h3{{border-bottom:1px solid var(--line);padding-bottom:4px;margin-top:28px}}
code,pre{{font:13px ui-monospace,monospace;background:color-mix(in srgb,var(--fg) 6%,transparent);border-radius:4px}}
code{{padding:1px 4px}} pre{{padding:10px;overflow-x:auto}}
table{{border-collapse:collapse}} td{{border-bottom:1px solid var(--line);padding:4px 14px 4px 0}}
details{{border:1px solid var(--line);border-radius:6px;padding:6px 12px;margin:8px 0}} summary{{cursor:pointer;font-weight:600}}
</style></head><body><main>
<h1>lazerproof</h1><div class="mut">Formally verified osu!lazer replay evaluator — status as of {now} (auto-refreshes)</div>
<h2>Metrics</h2>{('<table>'+rows+'</table>') if rows else '<p class="mut">No metrics yet.</p>'}
<h2>Recent commits</h2><pre>{html.escape(sh("git log --oneline -25"))}</pre>
<h2>STATE.md</h2>{md(read("STATE.md"))}
<h2>DECISIONS.md</h2>{md(read("DECISIONS.md"))}
<h2>Docs</h2>{doc_html or '<p class="mut">None yet.</p>'}
<h2>Machine</h2><pre>{html.escape(sh("uptime; free -h; df -h / | tail -1"))}</pre>
</main></body></html>"""
tmp = OUT.with_suffix(".tmp"); tmp.write_text(page); os.replace(tmp, OUT)
