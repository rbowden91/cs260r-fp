COQC=coqc
COQDEP=coqdep
COQFLAGS=-R VST/msl msl -R VST/veric veric -R VST/compcert compcert

SRCS=ast.v varmap.v typing.v semantics.v fo_seplogic.v typingproofs.v
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

