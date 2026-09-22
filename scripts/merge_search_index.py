import json
import logging
import os
from pathlib import Path

log = logging.getLogger("mkdocs.hooks.merge_search_index")


def on_post_build(config, **kwargs):
    index_path = get_identifier_index_path()
    if index_path is None:
        return

    definitions = json.loads(index_path.read_text(encoding="utf-8"))["definitions"]

    search_index_path = Path(config["site_dir"]) / "search" / "search_index.json"
    search_index = json.loads(search_index_path.read_text(encoding="utf-8"))

    added = 0
    for definition in definitions:
        if definition.get("visibility") == "private":
            continue

        # MkDocs treats `README.md` as the index file for the final rendered site:
        # the compiled `README.md` is served at `/index.html`, not `/README.html`.
        # The search index is not aware of this, so any entries will link to
        # `/README.html` (which 404's), unless we redirect them here.
        #
        # For any definition in the `README` module (or any of its submodules),
        # patch the location to point to `index.html#{position}` instead of
        # `README.html#{position}`.
        module = definition["module"]
        name = definition["name"]
        toplevel_module, *_ = module.split(".", maxsplit=1)

        location = (
            definition["path"]
            if toplevel_module != "README"
            else f"index.html#{definition['position']}"
        )

        search_index["docs"].append(
            {
                "location": location,
                "title": name,
                "text": f"{module}.{name}",
            }
        )
        added += 1

    search_index_path.write_text(
        json.dumps(search_index, ensure_ascii=False), encoding="utf-8"
    )
    log.info(f"Added {added} Agda identifier(s) to the search index")


def get_identifier_index_path() -> Path | None:
    path = os.environ.get("AGDA_SEARCH_INDEX_FILE")
    if not path:
        log.info("AGDA_SEARCH_INDEX_FILE not set, skipping identifier search index")
        return None

    index_path = Path(path)
    if not index_path.is_file():
        log.warning(f"AGDA_SEARCH_INDEX_FILE='{path}' is not a regular file")
        return None

    return index_path
