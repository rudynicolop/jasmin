# -*- Makefile -*-

.PHONY: all clean

COQMAKE = $(MAKE) -f Makefile.coq

all: Makefile.coq
	+$(COQMAKE)

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	+$(COQMAKE) $@

clean:
	@if [ -f Makefile.coq ]; then $(COQMAKE) clean; fi
	@find . -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '*.aux' -o -name '*.d' \) -delete
	@rm -f Makefile.coq
