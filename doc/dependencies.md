# Minuska - dependencies

To build Minuska, you need Coq as well as a bunch of Coq and OCaml libraries.
The autoritative source of information about these is the [`flake.nix`](../flake.nix) file in the root of this repository.
Using Nix with Flakes enabled, you can get all the dependencies by running:
```sh
nix develop '.#minuska'
```

However, to support building Minuska without Nix, we list the required dependencies here:
- [Dune](https://dune.readthedocs.io/en/stable/):
- [Coq](https://coq.inria.fr/) 8.19
- [stdpp](https://gitlab.mpi-sws.org/iris/stdpp) >= 1.10.0
- [equations](https://mattam82.github.io/Coq-Equations/) 1.3
- OCaml findlib
- ocamlc
- zarith


[Here](../dist/vagrant) we provide (TODO!) a Vagrant configuration for a Ubuntu machine with all the dependencies installed.
Inside the machines, the [`minuska` directory](../minuska) is mounted as `/minuska-src`.
