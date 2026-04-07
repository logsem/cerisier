FUNDAMENTAL		:=	 theories/logrel/fundamental.v
COQMAKEFILE 	?=   Makefile.coq
COQ_PROJ 		?= _CoqProject

SRCS := $(shell egrep '^.*\.v$$' _CoqProject | grep -v '^\#')

all: $(COQMAKEFILE)
		+@$(MAKE) -f $^ $@

# Forward `make` commands to `$(COQMAKEFILE)`
%: $(COQMAKEFILE)
		+@$(MAKE) -f $^ $@

fundamental: export TGTS=${FUNDAMENTAL:.v=.vo}
fundamental: $(COQMAKEFILE) only

assumptions: $(COQMAKEFILE)
		rm -f theories/assumptions.vo
		make all

$(COQMAKEFILE): $(COQ_PROJ)
		coq_makefile -f $^ -o $@

count-lines:
		coqwc $(SRCS)

.PHONY: all fundamental ci
