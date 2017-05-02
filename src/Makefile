COQC=coqc
COQDEP=coqdep

SRCS=stringfacts.v string_as_ot.v base.v ast.v logic.v vfs.v semantics.v all.v

.SUFFIXES: .v .vo

all: $(SRCS:.v=.vo)

.v.vo:
	$(COQC) $<

depend:
	$(COQDEP) $(SRCS) > .depend.new
	mv -f .depend.new .depend
-include .depend

clean:
	rm -f *.vo *.glob

distclean: clean
	rm -f .depend

.PHONY: all depend clean distclean

