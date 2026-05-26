# tlaplus-playground

Scratch space for **[TLA+](https://lamport.azurewebsites.net/tla/tla.html)** specs and TLC runs.

## Prerequisites

- **Java** (for TLC and the PlusCal translator)
- **[tla2tools.jar](https://github.com/tlaplus/tlaplus/releases)** (pre-included in `tools/tla2tools.jar`)
- **Graphviz** for generating graphs (optional)

## Usage

```sh
make check SPEC=petersonlock    # run TLC
make translate SPEC=pluscal     # translate PlusCal in the .tla file
make graph SPEC=petersonlock    # emit build/graphs/<SPEC>.png
make clean                      # remove build/
```

## Editor

This repo includes **VS Code** tasks (see `.vscode/tasks.json`) that call the `make` targets for the currently open spec.

## Layout

- **`specs/`** — `.tla` modules and matching `.cfg` TLC config files
- **`build/`** — generated state dirs and graph output (not committed)
