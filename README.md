# Vir

This contains the bulk of VIR, anonymized for submission. For the
purposes of anonymization, most documentation and comments have been
removed, and there may be some whitespace artifacts as a
result. Should the paper be accepted, a clean, fully documented
artifact will be submitted for review.

# Helix

The formalization of the Helix front-end for VIR, reported on in
Section 7, is ongoing work, and since the details are outside of the
scope of this submission, we have chosen not to include it as port of
the artifact submission. A public link will be made available after
the end of the anonimization phase, which will naturally support any
claim made throughout the paper.

# The Structure of this Repository

The interesting files are all in the `src/` directory, with the bulk
of the files that you might want to look at being in `src/coq/`
specifically.

- `lib/InteractionTrees` contains the version of the ITrees library that we have used in our development. 
   Most of it is orthogonal to the material described in this paper. The content of Section 5.1 can be found in more details in `theories/Eq/Eq.v` and `theories/Eq/UpToTaus.v`.
- `src/coq/` contains the core of VIR's formal development in Coq.
- `src/coq/LLVMAst.v` contains the full VIR AST.
- `src/coq/DynamicValues.v` contains the code relating to dynamic values and underdefined values discussed in Section 2.2.
- `src/coq/DynamicTypes.v` provides inductive types for representing LLVM types.
- `src/coq/InterpreterMCFG.v` provides the layers of interpretation shown in Figure 6 and some of their metatheory.
- `src/coq/LLVMEvents.v` is the inventory of events seen in Section 4.1.
- `src/coq/Denotation.v` provides the representation of VIR programs as ITrees from Section 4.2.
- `src/coq/Handlers` includes the code for all of the handlers described in Section 4.3. They are broken up into files based on the type of event, each file hence corresponding to a subsection.
- `src/coq/TopLevel.v` provides the full model / interpreter, the final result of Section 4.4.
- `src/coq/Refinement.v` defines refinement relations between layers of interpretations.
- `src/coq/TopLevelRefinements.v` proves the refinement relations between layers of interpretations, including the interpreter soundness proof from Section 5.
- `src/ml/` contains OCaml glue for the Vir executable.
- `src/ml/libvir/interpreter.ml` includes the OCaml driver for running the interpreter, the `step` function is what walks over the ITree.
- `src/ml/libvir/llvm_parser.mly` contains the parser adapter from Vellvm, as discussed in Section 4.5.
- `tests/` is our directory containing the test suite of LLVM IR programs discussed in Section 4.5

# Installing / Compiling Vir

### Assumes: 
  - coqc   : version 8.9.1 or 8.10.0 (and coqdep, etc.) 
  - Coq packages: 
    - ext-lib    (installed via, e.g. opam install coq-ext-lib)
    - paco       (installed via, e.g. opam install coq-paco)
    - flocq      (installed via, e.g. opam install coq-flocq, see note below) 
    - itree      (provided in lib/InteractionTrees)
    - ceres      (installed via, e.g. opam install coq-ceres)
- ocamlc : version 4.04    (probably works with 4.03 or later)
  - OPAM packages: dune, menhir, [optional: llvm  (for llvm v. 3.8)]

Compilation:

1. run `make` in the /src directory

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

