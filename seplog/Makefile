COQC=coqc
COQDEP=coqdep
COQFLAGS=-R VST/msl msl -R VST/veric veric -R VST/compcert compcert

SRCS=ast.v varmap.v astprops.v semantics.v fo_seplogic.v type_soundness.v

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

