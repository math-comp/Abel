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
- Compatible Coq versions: Coq 8.10 to 8.12
- Additional dependencies:
  - [MathComp ssreflect 1.11](https://math-comp.github.io)
  - [MathComp fingroup 1.11](https://math-comp.github.io)
  - [MathComp algebra 1.11](https://math-comp.github.io)
  - [MathComp solvable 1.11](https://math-comp.github.io)
  - [MathComp field 1.11](https://math-comp.github.io)
  - [MathComp real closed 1.11.1](https://github.com/math-comp/real-closed)
- Coq namespace: `Abel`
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


## Organization of the code

- `abel.v` itself contains the main theorems:
  + `galois_solvable_by_radical` (requires explicit roots of unity),
  + `ext_solvable_by_radical` (equivalent, and still requires roots of unity),
  + `radical_solvable_ext` (no mention of roots of unity),
  + `AbelGalois`, (equivalence obtained from the above to, requires  roots of unity)
  + and their consequence `example_not_solvable_by_radicals` (with one admit)

- `xmathcomp/various.v` contains various (rather straightforward)
  extensions that should be added to various mathcomp packages asap
  with potential minor modifications,

- `xmathcomp/char0.v` contains 0 characteristic specific results,
  that could use a refactoring for a smoother integration with
  mathcomp. e.g. ratr could get a canonical structure or rmorphism
  when the target field is a `lmodType ratr`, and we could provide a
  wrapper`NullCharType` akin to `PrimeCharType` (from `finfield.v`),

- `xmathcomp/cyclotomic.v` contains complementary results about
  cyclotomic polynomials, (there is still one admit),

- `xmathcomp/map_gal.v` contains complementary results about galois
  groups and galois extensions, including various isomorphisms,
  minimal galois extensions, solvable extensions, and mapping galois
  groups and galois extensions from a splitting field to
  another. This last construction is essential in switching to
  fields with roots of unity when we do not have them yet,

- `xmathcomp/classic_ext.v` contains the theory of classic
  extensions by arbitrary polynomials, most of the results there are
  in the classically monad, making the results available either for
  a boolean goal or a classical goal. This was instrumental in
  eliminating references to some embarrassing roots of the unity.

- `xmathcomp/diag.v` contains the theory of diagonalisation and
  codiagonalisation with the standard criterions.

- `xmathcomp/mxgal.v` represents elements of a Galois group as
  matrices, this enables the use of `diag` to find eigenvectors and
  eigenvalues.

- `xmathcomp/mxextra.v` is a matrix <-> `'Hom(_, _)` correspondence
   which is unused in the current development, we use `mxgal`
   instead.

## Development information

[Developping with nix](NIX.md)
