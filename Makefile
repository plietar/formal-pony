COQC=coqc
COQDEP=coqdep
COQINCLUDES=\
    -R src pony

SRC=\
    src/Ast.v \
    src/Eval.v \
    src/Semantics.v \
    src/Store.v \
    src/Extract.v \
    src/Entities.v

VO=$(SRC:.v=.vo)
DEP=$(SRC:.v=.v.d)

all: $(VO)

%.v.d: %.v
	$(COQDEP) $(COQINCLUDES) $< > $@

%.vo: %.v
	$(COQC) $(COQFLAGS) $(COQINCLUDES) $<

-include $(DEP)

clean:
	rm -f $(VO) $(DEP)
