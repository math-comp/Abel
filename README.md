<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Abel - Ruffini Theorem as a Mathematical Component

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/abel/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/abel/actions?query=workflow:"Docker%20CI"




This repository contains a proof of Abel Ruffini Theorem in the
Coq proof-assistant and using the Mathematical Components library.

## Meta

- Author(s):
  - Sophie Bernard
  - Cyril Cohen (initial)
  - Assia Mahboubi (initial)
  - Pierre-Yves Strub (initial)
- Compatible Coq versions: Coq 8.10 and 8.11
- Additional dependencies:
  - [MathComp ssreflect 1.11](https://math-comp.github.io)
  - [MathComp fingroup 1.11](https://math-comp.github.io)
  - [MathComp algebra 1.11](https://math-comp.github.io)
  - [MathComp solvable 1.11](https://math-comp.github.io)
  - [MathComp field 1.11](https://math-comp.github.io)
  - [MathComp real closed 1.11.1](https://github.com/math-comp/real-closed)
- Coq namespace: `mathcomp.abel`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Abel - Ruffini Theorem as a Mathematical Component
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-abel
```

To instead build and install manually, do:

``` shell
git clone https://github.com/math-comp/abel.git
cd abel
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Development information

[Developping with nix](NIX.md)
