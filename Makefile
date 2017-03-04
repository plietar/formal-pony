COQC=coqc
COQDEP=coqdep
COQINCLUDES=\
    -R src pony \
    -R $(TLC) TLC

TLC=tlc/src
TLC_SRC=$(wildcard $(TLC)/*.v)
TLC_VO=$(TLC_SRC:.v=.vo)

SRC=\
    src/Ast.v \
    src/Eval.v \
    src/Semantics.v \
    src/Store.v \
#    src/main.v

VO=$(SRC:.v=.vo)

all: $(VO)

%.v.d: %.v
	$(COQDEP) $(COQINCLUDES) $< > $@

%.vo: %.v
	$(COQC) $(COQFLAGS) $(COQINCLUDES) $<

-include $(SRC:.v=.v.d)
-include $(TLC_SRC:.v=.v.d)

clean:
	rm -f $(VO) $(TLC_VO)
	rm -f $(SRC:.v=.v.d) $(TLC_SRC:.v=.v.d)
