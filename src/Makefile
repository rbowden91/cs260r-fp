COQC=coqc
COQDEP=coqdep

SRCS=stringfacts.v base.v ast.v logic.v vfs.v all.v

.SUFFIXES: .v .vo

all: all.vo

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

