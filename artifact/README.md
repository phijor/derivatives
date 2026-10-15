# Derivatives of Containers in Univalent Foundations

Artifact accompanying the paper

> Philipp Joram and Niccolò Veltri.
> _Derivatives of Containers in Univalent Foundations_.
> [arXiv:2512.17484](https://arxiv.org/abs/2512.17484)

The canonical upstream repository is hosted on Codeberg at
<https://codeberg.org/phijor/derivatives>,
with a mirror on GitHub at <https://github.com/phijor/derivatives>.

## Contents

- `source.tar.gz` contains the Cubical Agda library (`agda/`) and the LaTeX sources of the paper (`paper/`).
- `documentation.tar.gz` contains the rendered, cross-linked documentation of the Agda library.

This artifact has been built from @ARTIFACT_ORIGIN@.

## Reading the Documentation

Unpack `documentation.tar.gz` and open `documentation/index.html` in a web browser.
All assets are included; no network access or web server is required.

The overview page mirrors the structure of the paper:
it lists each numbered result and links it to the corresponding definition in the library.

## Building from Source

Unpack `source.tar.gz`.
The library type-checks with Agda 2.8.0 against version 0.9 of the [`cubical`](https://github.com/agda/cubical) library.

The recommended way to build it is via [Nix](https://nixos.org/download/),
which pins every dependency to a working version in `flake.lock`:

```console
$ cd source
$ nix build    # type-check the entire library
$ nix develop  # enter a shell providing Agda and cubical
```

Without Nix, install the two dependencies above by hand and run `agda --build-library` in `source/`.

Further details are in `source/README.md`;
`source/agda/README.lagda.md` is the entry point into the library.

## License

The Agda code is licensed under the MIT license (`source/LICENSE`).
The rendered documentation (`documentation.tar.gz`) and the contents of `source/paper/` are licensed under CC BY 4.0 (`source/paper/LICENSE`).
