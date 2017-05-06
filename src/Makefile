COQC=coqc
COQDEP=coqdep

SRCS=\
	stringfacts.v string_as_ot.v base.v \
	ast.v varmap.v astprops.v semantics.v soundness.v \
	logic.v \
	all.v

# These do not work any more - they depend on being able to have
# values of arbitrary coq type, including with typeclasses. I want
# to figure out how to fix this in a non-horrible way, but that is
# not happening this weekend.
#     vfs.v caponfs.v

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

