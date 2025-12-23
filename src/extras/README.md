# Extras

This folder contains supplementary materials for the category theory exercises.

## Compiling TikZ diagrams

TikZ diagrams (`.tikz` files) can be compiled to PNG using the `compile_tikz.sh` script.

### Prerequisites

- TeX Live with `tikz-cd`, `preview`, and `amssymb` packages
- `poppler` for PDF to PNG conversion (`brew install poppler` on macOS)

### Usage

```bash
./compile_tikz.sh input.tikz [output.png]
```

If no output path is specified, it creates `input.png` in the same directory.

### Example

```bash
./compile_tikz.sh part1_chapter10_challenge5.tikz
```

### Notes

- The script includes `quiver.sty` for diagrams exported from [quiver](https://q.uiver.app/)
- Some quiver features like `scaling nfold` may produce warnings but the output is still usable
