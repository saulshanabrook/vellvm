# Coq sources
COQDIR = coq
COQLIBDIR = ../lib

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted

ITREEDIR=../lib/InteractionTrees

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Vir) -R $(EXTRACTDIR) Extract -R $(ITREEDIR)/theories/ ITree 
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

COQFILESINTERP := Numeric/Archi Numeric/Coqlib Numeric/Integers Numeric/Zbits Numeric/IEEE754_extra Numeric/Floats ParserHelper\
									Tactics Util PropT Error LLVMAst AstLib Dom CFG CFGProp MemoryAddress DynamicTypes DynamicValues\
									LLVMEvents TypToDtyp IntrinsicsDefinitions\
									Handlers/Intrinsics Handlers/Local Handlers/Global Handlers/Stack Handlers/Pick Handlers/Memory Handlers/UndefinedBehaviour Handlers/Handlers\
									Denotation InterpreterMCFG InterpreterCFG TopLevel Refinement TopLevelRefinements

COQFILESOPT    := Transformations/Transform Transformations/Traversal

OLLVMFILES :=

VFILES  := $(COQFILESINTERP:%=coq/%.v) $(COQFILESOPT:%=coq/%.v)
VOFILES := $(COQFILESINTERP:%=coq/%.vo) $(COQFILESOPT:%=coq/%.vo)


VFILES  := $(COQFILESINTERP:%=coq/%.v) $(COQFILESOPT:%=coq/%.v)
VOFILES := $(COQFILESINTERP:%=coq/%.vo) $(COQFILESOPT:%=coq/%.vo)

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) coq
	$(MAKE) extracted
	$(MAKE) vir

interp:
	@test -f .depend || $(MAKE) depend
	$(MAKE) coqinterp
	$(MAKE) extracted
	$(MAKE) vir

coq: $(VOFILES)

coqinterp: $(COQFILESINTERP:%=coq/%.vo)

update-trees:
	git submodule update -- $(ITREEDIR)

itrees:
	make -C $(ITREEDIR)

.PHONY: extracted itrees 
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

depend: itrees $(VFILES) 
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend


.PHONY: clean test qc restore

EXE=_build/default/ml/main.exe

$(EXE): extracted ml/dune ml/extracted/dune ml/testing/dune
	@echo "Compiling Vir"
	dune build ml/main.exe 

vir: $(EXE)
	cp $(EXE) vir

test: vir
	./vir --test

print-includes:
	@echo $(COQINCLUDES)

clean: clean-vir clean-itrees
clean-vir:
	rm -f .depend
	find $(COQDIR) -name "*.vo" -delete
	find $(COQDIR) -name "*.vio" -delete
	rm -f $(VOFILES)
	rm -rf doc/html doc/*.glob
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	dune clean
	rm -rf output
	rm -f vir
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o
clean-itrees:
	make -C $(ITREEDIR) clean
.PHONY: clean-vir clean-itrees

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
