COQC=coqc
COQDEP=coqdep
COQFLAGS=-R . veric -R ../msl msl -R ../sepcomp sepcomp -R ../compcert compcert

# these are the ones we use directly; make depend before building
# to get the ones used indirectly (quite a few)
SRCS=lift.v

.SUFFIXES: .v .vo

all: $(SRCS:.v=.vo)

.v.vo:
	$(COQC) $(COQFLAGS) $<

depend:
	#$(COQDEP) $(COQFLAGS) $(SRCS) > .depend.new
	$(COQDEP) $(COQFLAGS) *.v > .depend.new
	mv -f .depend.new .depend
-include .depend

clean:
	rm -f *.vo *.glob

distclean: clean
	rm -f .depend

.PHONY: all depend clean distclean

