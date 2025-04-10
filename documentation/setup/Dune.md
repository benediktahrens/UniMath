# Building UniMath using Dune

This document describes how to build UniMath using [Dune](https://dune.build/),
a build system for the OCaml ecosystem.

There are many advantages to using Dune over make, but one of the main
advantages for UniMath is that Dune has better support for incremental builds,
and also the functionality to cache builds. Rebuilding UniMath is a
time-consuming operation and Dune does a lot to keep rebuilds to a minimum.

- [Installing Dune](#installing-dune)
- [Building UniMath](#building-unimath)
- [Dune with Coqtop](#dune-with-coqtop)
  - [Proof General](#proof-general)
- [Generating documentation](#generating-documentation)

## Installing Dune

The [recommended](https://dune.build/install) way to install Dune is by using
opam, but it is also possible to compile and install it by following the
instructions on [GitHub/Dune](https://github.com/ocaml/dune). Make sure that the
version of dune installed is at least 3.5.0.

## Building UniMath

If you have previously compiled UniMath using `make` you need to clean up your
repository or else dune will complain about files that it does not know how to
compile. Running `make clean` should be enough.

Assuming coq is installed (otherwise see for example [Install.md](./Install.md))
and in your `PATH` you should now be able to build UniMath with the command
`dune build`. **Note** that dune by default does not have caching enabled. To
enable this once give the flag `--cache=enabled` to dune:

```bash
$ dune build --cache=enabled
```

To always have caching enabled you need to find where dune keeps it
configuration file. See the man-page `dune-config(5)`. On many systems it's the
file `~/.config/dune/config`. Change the contents of this file to something
like:

```
(lang dune 3.5)
(cache enabled)
(display short)
```

This enables caching and also tells dune to be more verbose during building (by
default dune is very quiet). This configuration corresponds to giving the flags
`--display=short --cache=enabled` when calling `dune build`. So now to build
UniMath (with cache enabled) all you have to do is:

```bash
$ dune build
```

To build a specific subsystem of UniMath, for example Algebra, you can do
```bash
$ dune build UniMath/Algebra
```

## Dune with Coqtop
Dune stores all the `.vo` files it produces in the `_build/` folder as opposed
to in the source tree. For `coqtop` to find these you need to give it the `-R`
flag, e.g

```
-R /your/path/to/UniMath/_build/default/UniMath UniMath
```

There is a very nice command `dune coq top` that will call `coqtop` with the
correct flags.

### Proof General
Unfortunately, Proof General currently does not support it (see issue [477](https://github.com/ProofGeneral/PG/issues/477)).
We hope this issue gets resolved soon as this would remove any need to configure PG/coqtop beyond telling it to call `dune coq top`.

## Generating documentation
To generate documentation with Dune for UniMath (or another theory like SetHITs or TypeTheory), perform the following steps:
1. Navigate to the [`UniMath`](../../UniMath/) directory *inside* the repository. This is the root directory of the code: the directory with the [`dune`](../../UniMath/dune) file that contains the `coq.theory` stanza. For other theories, this is for example [`SetHITs/code`](../../SetHITs/code) or [`TypeTheory/TypeTheory`](../../TypeTheory/TypeTheory/).
2. Execute the command `$ dune build UniMath.html` (adjust accordingly for your theory of choice, like `$ dune build SetHITs.html`).
3. Your documentation will be located in [`_build/default/UniMath/UniMath.html`](../../_build/default/UniMath/UniMath.html/) (or something similar for another theory, like [`_build/default/TypeTheory/TypeTheory/TypeTheory.html/`](../../_build/default/TypeTheory/TypeTheory/TypeTheory.html)).
