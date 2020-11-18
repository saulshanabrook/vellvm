# Vir

This anonymous artifact contains the formal VIR development, as described in the
PLDI'21 submission entitled: "Modular, Compositional, and Executable Formal
Semantics for LLVM IR". For the purposes of anonymization, some documentation
and comments have been removed, and there may be some whitespace artifacts as a
result. Should the paper be accepted, a clean, fully documented artifact will be
submitted for review.

# Structure of the development

The development is organized as follows.

## Local libraries

Stored in the `lib` folder. Currently the only dependency that needs to be installed locally is the itree one:
- `lib/InteractionTrees` contains the version of the ITrees library that we have used in our development. 

Although we have made significant contributions to the itree library for the sake of this project, most of it
is orthogonal to the material described in this paper, and can be treated entirely as an external library to understand this project.

The content of Section 5.1 that gives a taste of how the underlying equational theory works  can be found in more details in
the files`lib/InteractionTrees/theories/Eq/Eq.v` and `lib/InteractionTrees/theories/Eq/UpToTaus.v`.

## Coq formalization

The core of the project is encompassed by the Coq formalization of LLVM IR and the proof of its metatheory. 
This formalization is entirely contained in the `src/coq` folder. 

More specifically, the following files are among the most important to understand the development:
Syntax, in `src/coq/Syntax/`
- `LLVMAst.v` contains the front VIR internal AST. Our parser of native llvm syntax returns an element of this AST.
- `CFG.v`     contains the VIR internal AST as used for the semantics. 

Semantics, in `src/coq/Semantics/`:
- `DynamicValues.v` contains the code relating to dynamic values and underdefined values discussed in Section 2.2.
- `LLVMEvents.v` contains the inventory of all events as described in Section 4.1.
- `Denotation.v` definitions of the representation of VIR programs as ITrees as described in Section 4.2.
- `Handlers/` includes the code for all of the handlers described in Section 4.3. They are broken up into files 
   based on the nature of the event handled, each file hence corresponding to a subsection.
- `TopLevel.v` provides the full model and the full interpreter, by plugging all components together, 
   i.e. the final result of Section 4.4.

Theory, in `src/coq/Theory/`:
- `src/coq/PropT.v` metatheory required to reason about sets of itrees, i.e. about the propositional monad transformer.
- `src/coq/InterpreterMCFG.v` provides the layers of interpretation shown in Figure 6 and some of their metatheory.
- `src/coq/Refinement.v` defines refinement relations between layers of interpretations.
- `src/coq/TopLevelRefinements.v` proves the refinement relations between layers of interpretations, including the interpreter soundness proof from Section 5.


- `src/ml/` contains OCaml glue for the Vir executable.
- `src/ml/libvir/interpreter.ml` includes the OCaml driver for running the interpreter, the `step` function is what walks over the ITree.
- `src/ml/libvir/llvm_parser.mly` contains the parser adapter from Vellvm, as discussed in Section 4.5.
- `tests/` is our directory containing the test suite of LLVM IR programs discussed in Section 4.5

# Installing / Compiling Vir


# Vellvm
[![Build Status](https://travis-ci.com/vellvm/vellvm.svg?branch=master)](https://travis-ci.com/vellvm/vellvm)

Vellvm is a Coq formalization of the semantics of (a subset of) the
LLVM compiler IR that is intended for _formal verification_ of
LLVM-based software.  It is being developed at the
University of Pennsylvania as part of the DeepSpec project.

### See:
 - [Vellvm](http://www.cis.upenn.edu/~stevez/vellvm/)
 - [DeepSpec](http://deepspec.org)
 - [LLVM](http://llvm.org)

# Participants
 - Steve Zdancewic
 - Yannick Zakowski
 - Calvin Beck
 - Irene Yoon
 
## Past Contributors
 - Vivien Durey 
 - Dmitri Garbuzov 
 - Olek Gierczak
 - William Mansky
 - Milo Martin
 - Santosh Nagarakatte 
 - Emmett Neyman 
 - Christine Rizkallah 
 - Robert Zajac
 - Richard Zhang 
 - Jianzhou Zhao

---

# Structure of the repository

/src/ci   - travis configuration

/src/coq  - Coq formalization (see Denotation.v and TopLevel.v most notably)

/src/ml   - OCaml glue code for working with ollvm

/src/ml/extracted - OCaml code extracted from the files in /src/coq directory

/src/doc - coqdoq  [not useful yet]

/lib  - for 3rd party libraries [as git submodules]

/tests - various LLVM source code tests

# Installing / Compiling Vellvm

### Assumes: 
  - coqc   : version 8.11.2 (and coqdep, etc.)
  - Coq packages: 
    - ext-lib    (installed via, e.g. opam install coq-ext-lib)
    - paco       (installed via, e.g. opam install coq-paco)
    - flocq      (installed via, e.g. opam install coq-flocq, see note below) 
    - itree      (provided in lib/InteractionTrees)
    - ceres      (installed via, e.g. opam install coq-ceres)
- ocamlc : version 4.09.1+flambda    (probably works with 4.03 or later)
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

