
.PHONY: agda isabelle

all: agda

include ../Makefile.top

agda: $(AGDA24)
	$(AGDA24) --version
	cd ./agda/ && $(AGDA24) VerifyAnd.agda

isabelle: build-isabelle
	isabelle 
