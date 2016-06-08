
.PHONY: agda

all: agda

include ../Makefile.top

agda:
	$(AGDA) --version
	cd ./agda/ && $(AGDA) VerifyAnd.agda
