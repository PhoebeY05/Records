#!/usr/bin/env python3

from pathlib import Path
import sys

from playwright.sync_api import sync_playwright


def main():
    if len(sys.argv) != 3:
        print(
            "Usage: render_analytics_report_pdf.py <input_html> <output_pdf>",
            file=sys.stderr,
        )
        return 2

    html_path = Path(sys.argv[1])
    pdf_path = Path(sys.argv[2])
    html = html_path.read_text(encoding="utf-8")

    with sync_playwright() as p:
        browser = p.chromium.launch()
        page = browser.new_page(viewport={"width": 1280, "height": 1800})
        page.set_content(html, wait_until="load")
        page.pdf(
            path=str(pdf_path),
            print_background=True,
            prefer_css_page_size=True,
        )
        browser.close()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
