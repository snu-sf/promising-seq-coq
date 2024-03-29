COQMODULE    := PromisingSEQ
COQTHEORIES  := \
	src/lang/*.v \
	src/itree/*.v \
	src/prop/*.v \
	src/transformation/*.v \
	src/sequential/*.v \
	src/promotion/*.v \
	src/ldrfpf/*.v \
	src/ldrfra/*.v \
	src/ldrfsc/*.v \
	src/optimizer/*.v \

.PHONY: all theories clean

all: quick

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R src/lang $(COQMODULE)"; \
   echo "-R src/itree $(COQMODULE)"; \
   echo "-R src/prop $(COQMODULE)"; \
   echo "-R src/transformation $(COQMODULE)"; \
   echo "-R src/sequential $(COQMODULE)"; \
   echo "-R src/promotion $(COQMODULE)"; \
   echo "-R src/ldrfpf $(COQMODULE)"; \
   echo "-R src/ldrfra $(COQMODULE)"; \
   echo "-R src/ldrfsc $(COQMODULE)"; \
   echo "-R src/optimizer $(COQMODULE)"; \
   \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq Makefile.coq.conf
