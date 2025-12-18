# Derivatives of Containers in Univalent Foundations

## Abstract

Containers conveniently represent a wide class of inductive data types.
Their derivatives compute representations of types of one-hole contexts,
useful for implementing tree-traversal algorithms.
In the category of containers and cartesian morphisms,
derivatives of discrete containers (whose positions have decidable equality) satisfy a universal property.

Working in Univalent Foundations, we extend the derivative operation to _untruncated_ containers (whose shapes and positions are arbitrary types).
We prove that this derivative, defined in terms of a set of _isolated positions_,
satisfies an appropriate universal property in the (wild) category of untruncated containers and cartesian morphisms,
as well as basic laws with respect to constants, sums and products.
A chain rule exists, but is in general non-invertible.
In fact, a globally invertible chain rule is inconsistent in the presence of non-set types,
and equivalent to a classical principle when restricted to set-truncated containers.
We derive a rule for derivatives of smallest fixed points from the chain rule,
and characterize its invertibility.

## Agda formalization

This repository contains an Agda library demonstrating our results.
The module [`README.agda`](./README.agda) provides an overwiev of the library, and links it to the claims in the paper.

This library depends on Agda (version 2.8.0) and the [`cubical`](https://github.com/agda/cubical) library (v0.8).
The recommended way to type-check and investigate this library is via [Nix](https://nixos.org/download/).
All dependencies are pinned to working versions, hopefully aiding reproducibility.

To type check all modules, run:

```console
$ nix build
```

To enter a shell, with all dependencies available:

```console
$ nix shell
nix-shell> # Get current version of Agda
nix-shell> which agda
/nix/store/[...]-agdaWithPackages-2.8.0/bin/agda
nix-shell> agda --version
Agda version 2.8.0
```

To interactively type-check all source modules in a development shell:

```console
nix-shell> agda --build-library
```

## License

All Agda code in this repository is licensed under the terms of the _MIT license_, see [`LICENSE`](./LICENSE).
The contents of the `doc/` directory are licensed under the terms of the _CC BY 4.0 license_, see [`doc/LICENSE`](./doc/LICENSE).
