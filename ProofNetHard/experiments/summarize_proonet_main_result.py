import argparse
import json
import re
import shutil
import subprocess
from pathlib import Path
from collections import defaultdict, OrderedDict


def parse_dirname(name: str):
    """Parse a run directory name like:
    '<model>_<stage_num>_<stage_name>_<knowledge>_<nshot>'

    Returns a dict with fields or None if not matched.
    """
    m = re.match(r"^(?P<model>.+)_(?P<stage_num>[1234])_(?P<stage_name>[A-Za-z\-]+)_(?P<knowledge>[^_]+)_(?P<nshot>[01])$",
                 name)
    if not m:
        return None
    d = m.groupdict()
    d["stage_num"] = int(d["stage_num"])  # to int
    d["nshot"] = int(d["nshot"])  # to int
    return d


def map_setting(knowledge: str, stage_num: int):
    """Map (knowledge, stage) into the table Setting columns.

    We keep distinct columns for 1/2/3/4 Stage under each knowledge type.
    Only known knowledge tags are mapped; others return None to skip.
    """
    # Normalize knowledge tag
    k = knowledge.lower()
    if "oracle" in k:
        k_norm = "Oracle"
    elif "learn" in k:
        k_norm = "Learned"
    elif any(tag in k for tag in ["barebone", "barebones", "bare", "none", "no", "vanilla", "base"]):
        k_norm = "Barebone"
    else:
        # Unknown category; skip for the screenshot-style table
        return None

    # Keep stage number explicit: 1/2/3/4
    if stage_num not in {1, 2, 3, 4}:
        return None
    s_norm = f"{stage_num}-Stage"
    return f"{k_norm} + {s_norm}"


def load_metric(path: Path, metric: str) -> float | None:
    try:
        obj = json.loads(path.read_text())
        val = obj.get("summary", {}).get(metric)
        if isinstance(val, (int, float)):
            return float(val)
    except Exception:
        pass
    return None


def format_pct(x: float | None) -> str:
    if x is None:
        return ""
    return f"{x*100:.1f}%"


def load_pcts_tuple(path: Path) -> tuple[float, float, float] | None:
    """Return percentage tuple (type_pct, likely_pct, eq_pct).

    type_pct comes from `acc_type` (type checking accuracy),
    not the sum of likely+eq. Parentheses show the decomposition
    (likely_pct + eq_pct) for reference.
    """
    try:
        obj = json.loads(path.read_text())
        s = obj.get("summary", {})
        type_acc = s.get("acc_type")
        likely = s.get("acc_likelybeq")
        eq = s.get("acc_beq")
        if not all(isinstance(v, (int, float)) for v in [type_acc, likely, eq]):
            return None
        type_acc = float(type_acc)
        likely = float(likely)
        eq = float(eq)
        return type_acc, likely, eq
    except Exception:
        return None


def build_table_metric(base_dir: Path, metric: str) -> str:
    # Desired columns: Expert/Learned/None x 1..4 stage
    knowledge_groups = ["Oracle", "Learned", "Barebone"]
    stage_cols = [f"{k} + {s}-Stage" for k in knowledge_groups for s in (1, 2, 3, 4)]

    columns = ["Model", "Examples", *stage_cols]

    # Gather rows keyed by (model, nshot)
    # Each value is a dict {setting -> metric_value}
    rows: dict[tuple[str, int], dict[str, float]] = {}

    for run_dir in sorted(p for p in base_dir.iterdir() if p.is_dir()):
        parsed = parse_dirname(run_dir.name)
        if not parsed:
            continue
        merged = run_dir / "equiv_summary_merged.json"
        if not merged.exists():
            continue

        setting = map_setting(parsed["knowledge"], parsed["stage_num"])
        if setting is None:
            # Not part of the requested table
            continue

        value = load_metric(merged, metric)
        if value is None:
            continue

        key = (parsed["model"], parsed["nshot"])  # e.g., ("gpt-4.1-2025-04-14", 0)
        rows.setdefault(key, {})[setting] = value

    # Order models alphabetically by name, but keep gpt-* before qwen-* for readability
    def model_sort_key(model: str):
        pri = 0 if model.lower().startswith("gpt") else 1
        return (pri, model.lower())

    ordered_keys = sorted(rows.keys(), key=lambda k: (model_sort_key(k[0]), k[1]))

    # Compute averages by nshot for each setting
    settings = columns[2:]
    avg_by_shot = {0: {s: [] for s in settings}, 1: {s: [] for s in settings}}
    for (model, nshot), vals in rows.items():
        for s in settings:
            if s in vals:
                avg_by_shot[nshot][s].append(vals[s])

    avg_rows = {}
    for nshot in (0, 1):
        avg_rows[nshot] = {s: (sum(v) / len(v) if v else None) for s, v in avg_by_shot[nshot].items()}

    # Render Markdown table
    lines = []
    lines.append(f"Metric: `{metric}` from `equiv_summary_merged.json`\n")
    header = " | ".join(columns)
    sep = " | ".join(["---"] * len(columns))
    lines.append(header)
    lines.append(sep)

    # Emit rows
    for (model, nshot) in ordered_keys:
        vals = rows[(model, nshot)]
        row = [
            model,
            f"{nshot}-Shot",
        ]
        for s in settings:
            row.append(format_pct(vals.get(s)))
        lines.append(" | ".join(row))

    # Average rows
    for nshot in (0, 1):
        row = [
            "Average",
            f"{nshot}-Shot",
        ]
        for s in settings:
            row.append(format_pct(avg_rows[nshot][s]))
        lines.append(" | ".join(row))

    return "\n".join(lines) + "\n"


def build_table_composite(base_dir: Path) -> str:
    """Build table with cells like 'type% = (likely% + eq%)'."""
    knowledge_groups = ["Oracle", "Learned", "Barebone"]
    stage_cols = [f"{k} + {s}-Stage" for k in knowledge_groups for s in (1, 2, 3, 4)]

    columns = ["Model", "Examples", *stage_cols]

    # Store values as (type_pct, likely_pct, eq_pct)
    rows: dict[tuple[str, int], dict[str, tuple[float, float, float]]] = {}

    for run_dir in sorted(p for p in base_dir.iterdir() if p.is_dir()):
        parsed = parse_dirname(run_dir.name)
        if not parsed:
            continue
        merged = run_dir / "equiv_summary_merged.json"
        if not merged.exists():
            continue
        setting = map_setting(parsed["knowledge"], parsed["stage_num"])
        if setting is None:
            continue
        tpl = load_pcts_tuple(merged)
        if tpl is None:
            continue
        key = (parsed["model"], parsed["nshot"])  # e.g., (model, 0/1)
        rows.setdefault(key, {})[setting] = tpl

    def model_sort_key(model: str):
        pri = 0 if model.lower().startswith("gpt") else 1
        return (pri, model.lower())

    ordered_keys = sorted(rows.keys(), key=lambda k: (model_sort_key(k[0]), k[1]))

    settings = columns[2:]

    # Averages of percentages across models
    avg_by_shot: dict[int, dict[str, list[tuple[float, float, float]]]] = {0: {s: [] for s in settings}, 1: {s: [] for s in settings}}
    for (model, nshot), vals in rows.items():
        for s in settings:
            if s in vals:
                avg_by_shot[nshot][s].append(vals[s])

    def fmt_triplet(tpl: tuple[float, float, float] | None) -> str:
        if not tpl:
            return ""
        type_p, likely_p, eq_p = tpl
        return f"{type_p*100:.2f}% ({likely_p*100:.2f}% + {eq_p*100:.2f}%)"

    lines = []
    lines.append("Composite: type% (likely% + eq%) [percentages]\n")
    header = " | ".join(columns)
    sep = " | ".join(["---"] * len(columns))
    lines.append(header)
    lines.append(sep)

    for (model, nshot) in ordered_keys:
        vals = rows[(model, nshot)]
        row = [model, f"{nshot}-Shot"]
        for s in settings:
            row.append(fmt_triplet(vals.get(s)))
        lines.append(" | ".join(row))

    for nshot in (0, 1):
        row_vals = []
        for s in settings:
            lst = avg_by_shot[nshot][s]
            if lst:
                t = (sum(v[0] for v in lst) / len(lst))
                l = (sum(v[1] for v in lst) / len(lst))
                e = (sum(v[2] for v in lst) / len(lst))
                row_vals.append((t, l, e))
            else:
                row_vals.append(None)
        row = ["Average", f"{nshot}-Shot"]
        for tpl in row_vals:
            row.append(fmt_triplet(tpl))
        lines.append(" | ".join(row))

    return "\n".join(lines) + "\n"


def _collect_triplets(base_dir: Path):
    """Collect (type, likely, eq) percentage triplets per (model, shot, setting)."""
    knowledge_groups = ["Oracle", "Learned", "Barebone"]
    stage_cols = [f"{k} + {s}-Stage" for k in knowledge_groups for s in (1, 2, 3, 4)]

    rows: dict[tuple[str, int], dict[str, tuple[float, float, float]]] = {}
    settings_seen = set()

    for run_dir in sorted(p for p in base_dir.iterdir() if p.is_dir()):
        parsed = parse_dirname(run_dir.name)
        if not parsed:
            continue
        merged = run_dir / "equiv_summary_merged.json"
        if not merged.exists():
            continue
        setting = map_setting(parsed["knowledge"], parsed["stage_num"])
        if setting is None:
            continue
        tpl = load_pcts_tuple(merged)
        if tpl is None:
            continue
        key = (parsed["model"], parsed["nshot"])  # (model, shot)
        rows.setdefault(key, {})[setting] = tpl
        settings_seen.add(setting)

    # consistent ordering of settings (only those present)
    settings = [s for s in stage_cols if s in settings_seen]

    # consistent ordering of keys
    def model_sort_key(model: str):
        pri = 0 if model.lower().startswith("gpt") else 1
        return (pri, model.lower())
    ordered_keys = sorted(rows.keys(), key=lambda k: (model_sort_key(k[0]), k[1]))

    return rows, ordered_keys, settings


def write_csv_slim(base_dir: Path, out_csv: Path) -> None:
    """Write compact CSV with columns:
    Model, Examples, Oracle + 4-Stage, Learned + 4-Stage, Learned + 1-Stage, None + 4-Stage, None + 1-Stage
    Values are formatted as 'type% (likely% + eq%)'.
    """
    import csv

    rows, ordered_keys, _ = _collect_triplets(base_dir)

    def relabel(setting: str) -> str:
        # Replace Barebone -> None to match the spreadsheet
        return setting.replace("Barebone", "None")

    target_settings = [
        "Oracle + 4-Stage",
        "Learned + 4-Stage",
        "Learned + 1-Stage",
        "None + 4-Stage",
        "None + 1-Stage",
    ]

    header = ["Model", "Examples", *target_settings]

    def fmt_triplet(tpl: tuple[float, float, float] | None) -> str:
        if not tpl:
            return ""
        t, l, e = tpl
        return f"{t*100:.2f}% ({l*100:.2f}% + {e*100:.2f}%)"

    with out_csv.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(header)

        for (model, shot) in ordered_keys:
            vals = rows[(model, shot)]
            conv = {relabel(k): v for k, v in vals.items()}
            row = [model, f"{shot}-Shot"]
            for s in target_settings:
                row.append(fmt_triplet(conv.get(s)))
            w.writerow(row)

        # Averages per shot across models
        for shot in (0, 1):
            row = ["Average", f"{shot}-Shot"]
            for s in target_settings:
                lst = []
                for (m, sh), vals in rows.items():
                    if sh != shot:
                        continue
                    conv = {relabel(k): v for k, v in vals.items()}
                    if s in conv:
                        lst.append(conv[s])
                if lst:
                    t = sum(v[0] for v in lst) / len(lst)
                    l = sum(v[1] for v in lst) / len(lst)
                    e = sum(v[2] for v in lst) / len(lst)
                    row.append(fmt_triplet((t, l, e)))
                else:
                    row.append("")
            w.writerow(row)


def write_csv_grouped(base_dir: Path, out_csv: Path) -> None:
    """Write a grouped CSV with two blocks (Non-Reasoning Models / Reasoning Models)
    and the following columns:
    Model, Examples, Oracle + 4-Stage, Learned + 4-Stage, Learned + 1-Stage, Barebone + 4-Stage, Barebone + 1-Stage

    Display names follow the user's requested labels, and settings keep 'Barebone'
    (no conversion to 'None').
    """
    import csv

    rows, _, _ = _collect_triplets(base_dir)

    target_settings = [
        "Oracle + 4-Stage",
        "Learned + 4-Stage",
        "Learned + 1-Stage",
        "Barebone + 4-Stage",
        "Barebone + 1-Stage",
    ]

    header = ["Model", "Examples", *target_settings]

    def fmt_triplet(tpl: tuple[float, float, float] | None) -> str:
        if not tpl:
            return ""
        t, l, e = tpl
        return f"{t*100:.2f}% ({l*100:.2f}% + {e*100:.2f}%)"

    # Map display rows to canonical model keys inside our collection
    non_reasoning = [
        ("gpt-4.1-mini-2025-04-14", "gpt-4.1-mini-2025-04-14"),
        ("gpt-4.1-2025-04-14", "gpt-4.1-2025-04-14"),
        ("Claude-4-Sonnet-20250514", None),  # may be absent
        ("Qwen3-14B", "qwen_qwen3-14b"),
        ("Qwen3-32B", "qwen_qwen3-32b"),
        ("Qwen3-235B-A22B-Instruct-2507", "qwen_qwen3-235b-a22b-2507"),
    ]

    reasoning = [
        ("gpt-5-mini-2025-08-07 (Reasoning Effort: Medium)", "gpt-5-mini-2025-08-07"),
        ("gpt-5-2025-08-07 (Reasoning Effort: Medium)", "gpt-5-2025-08-07"),
        ("Claude-4-Sonnet-20250514 (Thinking Budget: 12,288)", None),  # may be absent
        ("Qwen3-14B (Thinking Budget: 12_288)", "qwen_qwen3-14b-thinking"),
        ("Qwen3-32B (Thinking Budget: 12_288)", "qwen_qwen3-32b-thinking"),
        ("Qwen3-235B-A22B-2507-Thinking (Thinking Budget: 12_288)", "qwen_qwen3-235b-a22b-thinking-2507"),
    ]

    def emit_group(w, title: str, items: list[tuple[str, str | None]]):
        # Section title row
        w.writerow([title])

        # Emit rows for each model and Examples (0/1 Shot)
        for disp, key in items:
            for shot in (0, 1):
                label = disp if shot == 0 else ""
                row = [label or disp, f"{shot}-Shot"]
                if key is None:
                    row.extend([""] * len(target_settings))
                else:
                    vals = rows.get((key, shot), {})
                    for s in target_settings:
                        row.append(fmt_triplet(vals.get(s)))
                w.writerow(row)

        # Averages for the group
        for shot in (0, 1):
            avg_cells = []
            for s in target_settings:
                lst: list[tuple[float, float, float]] = []
                for _, key in items:
                    if key is None:
                        continue
                    vals = rows.get((key, shot))
                    if vals and s in vals:
                        lst.append(vals[s])
                if lst:
                    t = sum(v[0] for v in lst) / len(lst)
                    l = sum(v[1] for v in lst) / len(lst)
                    e = sum(v[2] for v in lst) / len(lst)
                    avg_cells.append(fmt_triplet((t, l, e)))
                else:
                    avg_cells.append("")
            w.writerow(["Average", f"{shot}-Shot", *avg_cells])

    with out_csv.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(header)
        emit_group(w, "Non-Reasoning Models", non_reasoning)
        # blank separator row
        w.writerow([])
        emit_group(w, "Reasoning Models", reasoning)

def try_export_pdf(md_path: Path, pdf_path: Path) -> str:
    """Attempt to export Markdown to PDF using available tools.

    Order: pandoc (CLI) -> wkhtmltopdf (CLI, via minimal HTML) -> weasyprint (python).
    Returns a short status message describing what happened.
    """
    # 1) pandoc
    if shutil.which("pandoc"):
        try:
            subprocess.run([
                "pandoc", str(md_path), "-o", str(pdf_path),
                "--from", "gfm", "--pdf-engine=xelatex"
            ], check=True)
            return f"PDF written via pandoc: {pdf_path}"
        except Exception as e:
            pass

    # Helper: very simple Markdown->HTML wrapper (keeps table pipes as preformatted text)
    def md_to_basic_html(md_text: str) -> str:
        # If python-markdown is available, prefer it
        try:
            import markdown  # type: ignore
            html_body = markdown.markdown(md_text, extensions=['tables'])
        except Exception:
            # Fallback: preformatted block to preserve content
            from html import escape
            html_body = f"<pre style='font-family: monospace; white-space: pre-wrap'>{escape(md_text)}</pre>"
        return f"""
<!doctype html>
<html>
<head>
  <meta charset='utf-8'/>
  <style>
    body {{ font-family: sans-serif; margin: 20px; }}
    table {{ border-collapse: collapse; width: 100%; }}
    th, td {{ border: 1px solid #999; padding: 6px 8px; text-align: left; }}
    code, pre {{ font-family: monospace; }}
  </style>
  <title>Summary</title>
  </head>
  <body>
  {html_body}
  </body>
  </html>
"""

    # 2) wkhtmltopdf
    if shutil.which("wkhtmltopdf"):
        try:
            html = md_to_basic_html(md_path.read_text())
            html_path = pdf_path.with_suffix('.html')
            html_path.write_text(html)
            subprocess.run(["wkhtmltopdf", str(html_path), str(pdf_path)], check=True)
            return f"PDF written via wkhtmltopdf: {pdf_path}"
        except Exception:
            pass

    # 3) weasyprint (python)
    try:
        from weasyprint import HTML  # type: ignore
        html = md_to_basic_html(md_path.read_text())
        HTML(string=html).write_pdf(str(pdf_path))
        return f"PDF written via weasyprint: {pdf_path}"
    except Exception:
        return "No PDF engine available (pandoc/wkhtmltopdf/weasyprint). Saved Markdown only."


def main():
    ap = argparse.ArgumentParser(
        description=(
            "Summarize equiv_summary_merged.json files. By default, generates Markdown, PDF, and CSV"
            " inside the specified base directory."
        )
    )
    ap.add_argument(
        "--base-dir",
        type=Path,
        default=Path("outputs/proofnet_main_result_2"),
        help="Directory that contains per-run subfolders; outputs are created here.",
    )
    # Keep flexibility, but not required: user can still choose table content for Markdown
    ap.add_argument(
        "--mode",
        type=str,
        default="composite",
        choices=["composite", "metric"],
        help=(
            "Markdown content: 'composite' shows type=(likely+eq); 'metric' shows a single metric percentage table."
        ),
    )
    ap.add_argument(
        "--metric",
        type=str,
        default="acc_likelybeq",
        choices=["acc_type", "acc_pq", "acc_qp", "acc_beq", "acc_likelybeq"],
        help="Metric to report when --mode=metric.",
    )

    args = ap.parse_args()

    base_dir: Path = args.base_dir
    if not base_dir.exists() or not base_dir.is_dir():
        # Do not create directories automatically; fail with a clear error.
        raise SystemExit(f"--base-dir does not exist or is not a directory: {base_dir}")

    # Default output filenames live under the base directory
    md_out = base_dir / "summary_table.md"
    pdf_out = base_dir / "summary_table.pdf"
    csv_out = base_dir / "summary_table.csv"

    # Build Markdown (composite or metric) and write it
    if args.mode == "composite":
        table_md = build_table_composite(base_dir)
    else:
        table_md = build_table_metric(base_dir, args.metric)

    md_out.write_text(table_md)
    print(table_md, end="")

    # Always try to export a PDF next to the Markdown
    status = try_export_pdf(md_out, pdf_out)
    print(f"\n{status}")

    # Always write the compact CSV
    write_csv_slim(base_dir, csv_out)
    print(f"CSV written: {csv_out}")

    # Also write the grouped CSV requested by users for presentation
    csv_grouped = base_dir / "summary_table_grouped.csv"
    write_csv_grouped(base_dir, csv_grouped)
    print(f"Grouped CSV written: {csv_grouped}")


if __name__ == "__main__":
    main()
