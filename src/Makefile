# Coq sources
COQDIR = coq
COQLIBDIR = ../lib

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted

# Cerberus
CERBERUS = cerberus-private/src
CERBERUSGENERATED =cerberus-private/ocaml_generated
LEMLIB = lem
LEMOCAMLLIB = lem/num_impl_zarith


COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Vellvm) -R $(EXTRACTDIR) Extract -R $(COQLIBDIR)/CompCert compcert -R $(COQLIBDIR)/paco/src Paco -R $(COQLIBDIR)/InteractionTrees/theories ITree

COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

COQFILES := Error LLVMAst Util Misc AstLib Dom CFG CFGProp MemoryAddress DynamicValues LLVMIO TypeUtil StepSemantics StepSemanticsProp Memory IntrinsicsDefinitions Intrinsics Renaming DeadInstr Transform LLVMAddr MemoryModel MemoryCerberus TopLevel Numeric/Archi Numeric/Coqlib Numeric/Fappli_IEEE_extra Numeric/Floats Numeric/Integers

OLLVMFILES := 

VFILES := $(COQFILES:%=coq/%.v)
VOFILES := $(COQFILES:%=coq/%.vo)

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) coq
	$(MAKE) extracted
	$(MAKE) vellvm

coq: $(VOFILES)

.PHONY: extracted
extracted: $(EXTRACTDIR)/STAMP $(VOFILES)

$(EXTRACTDIR)/STAMP: $(VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
	patch -p0 < CRelationClasses.mli.patch
	touch $(EXTRACTDIR)/STAMP


%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

depend: $(VFILES) 
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend


.PHONY: clean test qc restore

# Directories containing plain Caml code
OCAMLDIRS= $(EXTRACTDIR) $(MLDIR) $(CERBERUS) $(CERBERUSGENERATED) $(LEMLIB) $(LEMOCAMLLIB)

COMMA=,
OCAMLINCLUDES=$(patsubst %,-I %, $(OCAMLDIRS))
print-ocaml-includes:
	@echo $(OCAMLINCLUDES)

# Deal with Z3 package installed by opam
ifeq ($(shell ocamlfind query -qe -qo Z3; echo $$?), 0)
Z3="Z3"
else
Z3="z3"
endif


OCAMLLIBS := str
OCAMLPKGS := unix,lem,cmdliner,pprint,yojson,${Z3}

.PHONY: clean main.native test qc restore


# TODO dune
# EXE=_build/default/ml/main.exe

$(EXE): extracted ml/dune ml/extracted/dune
	@echo "Compiling Vellvm"
	ocamlbuild cerberus-private/src/cerberus_cstubs.o
	ocamlbuild -tag debug -tag link_cstubs -j 4 -r -use-menhir -yaccflag --explain $(OCAMLINCLUDES) -use-ocamlfind -pkgs $(OCAMLPKGS) -libs $(OCAMLLIBS) main.native
# TODO dune
#	dune build ml/main.exe

vellvm: $(EXE)
	cp $(EXE) vellvm

test: vellvm
	./vellvm --test

print-includes:
	@echo $(COQINCLUDES)

clean:
	rm -f .depend
	rm -f $(VOFILES)
	rm -rf doc/html doc/*.glob
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	dune clean
	rm -rf output
	rm -f vellvm
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o

doc/coq2html: 
	make -C ../lib/coq2html
	cp ../lib/coq2html doc/coq2html
	chmod +x doc/coq2html

.PHONY: documentation
documentation: doc/coq2html $(VFILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	doc/coq2html -d doc/html doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)
	cp ../lib/coq2html/coq2html.css ../lib/coq2html/coq2html.js doc/html/

-include .depend
