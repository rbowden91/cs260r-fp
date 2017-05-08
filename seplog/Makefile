COQC=coqc
COQDEP=coqdep
COQFLAGS=-R VST/msl msl -R VST/veric veric -R VST/compcert compcert

SRCS=\
	ast.v varmap.v \
	semantics.v typing.v oldtyping.v \
	fo_seplogic.v \
	typingproofs.v oldtypingproofs.v
# table.v (deprecated)

.SUFFIXES: .v .vo

all: $(SRCS:.v=.vo)

.v.vo:
	$(COQC) $(COQFLAGS) $<

depend:
	$(COQDEP) $(COQFLAGS) $(SRCS) > .depend.new
	mv -f .depend.new .depend
-include .depend

clean:
	rm -f *.vo *.glob

distclean: clean
	rm -f .depend

.PHONY: all depend clean distclean

