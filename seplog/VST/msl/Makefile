COQC=coqc
COQDEP=coqdep
COQFLAGS=-R . msl -R ../compcert/lib compcert.lib

# these are the ones we use directly; make depend before building
# to get the ones used indirectly (quite a few)
SRCS=eq_dec.v msl_direct.v Coqlib2.v seplog.v log_normalize.v

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

