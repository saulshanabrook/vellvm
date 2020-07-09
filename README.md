# TODO

- Write a Readme that maps concepts from the paper to definitions from the development

# Vir

This contains the bulk of VIR, anonymized for submission. For the
purposes of anonymization, most documentation and comments have been
removed, and there may be some whitespace artifacts as a
result. Should the paper be accepted a clean, fully documented
artifact will be submitted for review.

# Helix

“The formalization of a Helix front-end for VIR, of which we report in Section 7, being an ongoing work whose details are outside the scope of this submission, we have chosen not to include it as part of the artifact submitted. A public link will be made available after the end of the anonimization phase that will attest of any claim made in the paper” 


# Structure of the repository

TODO point out handlers.

/src/coq  - Coq formalization (see Denotation.v and TopLevel.v most notably)

/src/ml   - OCaml glue code for working with ollvm

/src/ml/extracted - OCaml code extracted from the files in /src/coq directory

/src/doc - coqdoq  [not useful yet]

/lib  - for 3rd party libraries [as git submodules]

/tests - various LLVM source code tests

# Installing / Compiling Vir

### Assumes: 
  - coqc   : version 8.9.1 or 8.10.0 (and coqdep, etc.) 
  - Coq packages: 
    - ext-lib    (installed via, e.g. opam install coq-ext-lib)
    - paco       (installed via, e.g. opam install coq-paco)
    - flocq      (installed via, e.g. opam install coq-flocq, see note below) 
    - itree      ~~(installed via, e.g. opam install coq-itree)~~
      - Currently you should actually just use the submodule (lib/InteractionTrees): see the instructions for compilation below.
    - ceres      (installed via, e.g. opam install coq-ceres)
- ocamlc : version 4.04    (probably works with 4.03 or later)
  - OPAM packages: dune, menhir, [optional: llvm  (for llvm v. 3.8)]

Compilation:

1. clone the vir git repo with `--recurse-submodule` option (`git clone --recurse-submodules`)
2. run `make` in the /src directory

# Running

Do `src/vir -help` from the command line.

Try `src/vir -interpret tests/ll/factorial.ll`.


# Notes

### coq-flocq

On some OSX configurations the opam installation for coq-flocq fails with a
permissions error `# Failed to create server: Operation not permitted` caused by
opam's sandboxing scripts.  The solution is to temporarily disable opam's
sandboxing by editing ~/.opam/config to remove the lines having to do with
`wrap-*-commands:`.

