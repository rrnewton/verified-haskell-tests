
.PHONY: agda

all: agda

include ../Makefile.top

agda: $(AGDA)
	$(AGDA) --version
	cd ./agda/ && $(AGDA) VerifyAnd.agda
