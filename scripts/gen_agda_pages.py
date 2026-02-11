import mkdocs_gen_files

from pathlib import Path
import os
from typing import TextIO


def main():
    html_source_dir = get_html_source_dir()

    print("Copying hightlighted Markdown files...")
    for md in html_source_dir.glob("*.md"):
        prepare_md(md)

    print("Wrapping raw HTML files as Markdown...")
    for html in html_source_dir.glob("*.html"):
        prepare_html(html)


def get_html_source_dir() -> Path:
    dir = os.environ.get("AGDA_HTML_DIR")
    if dir is not None:
        print(f"Overriding HTML source directory: AGDA_HTML_DIR={dir}")
        return Path(dir)
    else:
        return Path("html")


def prepare_md(md: Path):
    print(f"Markdown: '{md}'")
    if not md.is_file():
        print(f"!!! '{md}' is not a regular file")
        return

    target: TextIO
    with mkdocs_gen_files.open(md.name, "w+", encoding="utf-8") as target:
        target.write(md.read_text(encoding="utf-8"))


def prepare_html(html: Path):
    print(f"HTML: '{html}'")

    if not html.is_file():
        print(f"!!! '{html}' is not a regular file")
        return

    target_name = f"{html.stem}.md"
    with mkdocs_gen_files.open(target_name, "w+", encoding="utf-8") as target:
        target.write('<pre class="Agda">\n')
        target.write(html.read_text(encoding="utf-8"))
        target.write("</pre>\n")


main()
