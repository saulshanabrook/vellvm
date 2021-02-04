# Artifact for the ITP'21 submission: "Compositional Compiler Correctness for HELIX" 

  The supplementary material submitted with our paper is constituted of two frozen branches:
  - The branch `itp21` of the HELIX project:  https://github.com/vzaliva/helix/tree/itp21/
  - The branch `itp21` of the Vellvm project: https://github.com/vellvm/vellvm/tree/itp21
  Installation instructions can be found below.

## Connection with the results described in the paper

### Helix side
  
   The repository https://github.com/vzaliva/helix/tree/itp21/ contains the HELIX development over-viewed in Section 2. Here the following may be found:
   
   - the abstract syntax of DHCOL, of which FHCOL is a specialization, described in Section 3: [DSigmaHCOL](./coq/DSigmaHCOL/DSigmaHCOL.v).
   - the big-step interpreter, also described in Section 3: [DSigmaHCOLEval](./coq/DSigmaHCOL/DSigmaHCOLEval.v).
   - the itree-based denotation, described in Section 5: [DSigmaHCOLITree](./coq/DSigmaHCOL/DSigmaHCOLITree.v).
   - the proof of correctness of this new semantics, stated in Section 5: [EvalDenoteEquiv](./coq/LLVMGen/EvalDenoteEquiv.v).
   - the compilation pass from FHCOL down to LLVM IR, described through Section 4: [Compiler](./coq/LLVMGen/Compiler.v).
   - all the other files contained in [LLVMGen](./coq/LLVMGen/) are part of the proof of correctness for the compilation of operators,
     stated in Section 5.
     
     The state invariant sketched in Section 7 can be found in [Correctness_Invariants](./coq/LLVMGen/Correctness_Invariants.v).
     
     The result itself is stated in [Correctness_GenIR](./coq/LLVMGen/Correctness_GenIR.v).
     
     *Note on admits*: This file contains three admits. These correspond to three operators that we have not yet proved.
     We emphasize that these operators have a similar structure to the cases of IMap and Power that we have proved:
     they use "genWhileLoop" to iterate some operation over a vector.
     As such, we are confident that while these proofs will require some non-trivial effort, they will not require
     any new meta-theory nor significant invariant, and hence will not be an obstacle. We intend to tackle them
     in the upcoming weeks.

   
### Vellvm side

   The repository https://github.com/vellvm/vellvm/tree/itp21 as a whole
   contains the Vellvm development. In here can be found:

   - the abstract syntax of the language, omitted from the paper: [LLVMAst.v](./src/coq/Syntax/LLVMAst.v).
   - the semantics, the focus of another paper under submission and cited as such
     in the present submission, can be found primarily within
     the folders [Semantics](./src/coq/Semantics) and [Handlers](./src/coq/Handlers).
   - the new extended meta-theory, described in Section 6, can be found in the folder [Theory](./src/coq/Theory).
   - the symbolic interpreter, described in Section 6, is defined in [SymbolicInterpreter](./src/coq/Theory/SymbolicInterpreter.v).
     We fine-tune it on the Helix side in the Prelude to enforce it to run on the right hand-side of
     refinement proofs, and to pair it with the shallow symbolic interpreter for the FHCOL denotation.
   - although as mentioned in Section 6 we work with the relation program logic at a shallow level in
     the current proof for HELIX, we have drafted a more formal take on it in [RelLog](./src/coq/Utils/RelLog.v).
   - we have not found the space to detail it in the paper, but the theoretical tools used to
     express the well-definedness of the source semantics in an itree-world is developed in [NoFailure](./src/coq/Utils/NoFailure.v).
   - we have not found the space to detail it in the paper, but the [tfor] itree combinator we
     introduce to help reason generically about [genWhileLoop] is defined in [TFor](./src/coq/Utils/TFor.v).


# Vellvm
[![Build Status](https://travis-ci.com/vellvm/vellvm.svg?branch=master)](https://travis-ci.com/vellvm/vellvm)

Vellvm is an ongoing project aiming at the formal verification in the Coq proof
assistant of a compilation infrastructure inspired by the LLVM compiler.

As such, its central piece is Verified IR (VIR), a Coq formalization of the
semantics of (a subset of) the LLVM IR that is intended for _formal
verification_ of LLVM-based software. 
It is being developed at the University of Pennsylvania as part of the DeepSpec project.

After VIR, the second component whose development is reaching maturity is the verification of 
a verified front-end for the [Helix](https://github.com/vzaliva/helix) chain of compilation.

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

# Structure of the development

The development is organized as follows.

## Local libraries

Stored in the `lib` folder. Currently the only dependency that needs to be installed locally is the itree one:
- `lib/InteractionTrees` contains the version of the ITrees library that we have used in our development. 

The library will be built as the same time as the Vir development via the Makefile.

Although we have made significant contributions to the itree library for the sake of this project, most of it
is orthogonal to the material described in this paper, and can be treated entirely as an external library to understand this project.

The content of Section 5.1 that gives a taste of how the underlying equational theory works can be found in more details in
the files`lib/InteractionTrees/theories/Eq/Eq.v` and `lib/InteractionTrees/theories/Eq/UpToTaus.v`.

## Coq formalization

The core of the project is encompassed by the Coq formalization of LLVM IR and the proof of its metatheory. 
This formalization is entirely contained in the `src/coq` folder. 

More specifically, the following selection of files are among the most important to understand the development:

Syntax, in `src/coq/Syntax/`
- `LLVMAst.v` the front VIR internal AST. Our parser of native llvm syntax returns an element of this AST.
- `CFG.v`     the VIR internal AST as used for the semantics. 

Semantics, in `src/coq/Semantics/`:
- `DynamicValues.v` definition of the dynamic values and underdefined values discussed in Section 2.2.
- `LLVMEvents.v`    inventory of all events as described in Section 4.1.
- `Denotation.v`    definitions of the representation of VIR programs as ITrees as described in Section 4.2.
- `Handlers/`       includes the code for all of the handlers described in Section 4.3. They are broken up into files 
                    based on the nature of the event handled, each file hence corresponding to a subsection.
- `TopLevel.v`      provides the full model and the full interpreter, by plugging all components together, 
                    i.e. the final result of Section 4.4.

Theory, in `src/coq/Theory/`:
- `src/coq/Utils/PropT.v` metatheory required to reason about sets of itrees, i.e. about the propositional monad transformer.
- `InterpreterMCFG.v`     the layers of interpretation shown in Figure 6 and some of their metatheory
- `InterpreterCFG.v`      the same layers of interpretation and metatheory, but when reasoning about single functions (i.e. single cfg)
- `Refinement.v`          definition of the refinement relations between layers of interpretations
- `TopLevelRefinements.v` proof of inclusion of the refinement relations between layers of interpretations;
                          proof of soundness of the interpreter as described in Section 5
- `DenotationTheory`      Equational theory to reason directly about the structure of vir programs;
                          in particular, reasoning principles about open control-flow-graphs.

## OCmal front-end and driver for execution and testing

On the OCaml side, we provide a parser for legal LLVM IR syntax as well as an
infrastructure to run differential tests between our interpreter and llc.
These unverified parts of the development live in the `src/ml` folder.

- `extracted/Extract.v`    instructions for the extraction of the development to OCaml
- `libvir/interpreter.ml`  OCaml driver for running the interpreter; the `step` function 
                                 walks over the ITree that remains after complete interpretation of the denotation of a program
- `libvir/llvm_parser.mly` the parser, adapted from Vellvm, as discussed in Section 4.5.
- `testing/assertion.ml`   custom annotations of llvm programs as comments used to define our tests.
- `main.ml`                top-level from which our executable is obtained.

## Test suite

Our current test-suite of LLVM programs for which we compare our semantics against llc is stored in `tests/`

- `tests/` directory containing the test suite of LLVM IR programs discussed in Section 6

# Installing / Compiling Vir

### Assumes: 
  - coq   : version 8.12 
  - External Coq libraries: 
    * ext-lib    (installed via, e.g. opam install coq-ext-lib)
    * paco       (installed via, e.g. opam install coq-paco)
    * flocq      (installed via, e.g. opam install coq-flocq, see note below) 
    * ceres      (installed via, e.g. opam install coq-ceres)
    WARNING: you should not have the itree opam package in your switch to avoid conflict with the extended version of the library we provide locally
  - Additional opam packages: 
    * dune       (installed via, e.g. opam install dune)
    * menhir     (installed via, e.g. opam install menhir)
    * qcheck     (installed via, e.g. opam install qcheck)
  - llvm (not required for compiling, only for differential testing)

Compilation:

1. Install all external dependencies
2. Clone the vellvm git repo with the `--recurse-submodule` option
1. Run `make` in the /src directory: it will first compile the itree libraries, then vir, and finally extract the OCaml executable

# Running

The executable `vir` will be found in `src/`.
Do `src/vir -help` from the command line to see all available options.
In particular:
- `src/vir -interpret tests/ll/factorial.ll` to run our interpreter on a given file.
- `src/vir --test` to run the test suite against llc
- `src/vir --test-file tests/ll/factorial.ll` to test a specific file against llc



