

default: UseIdAgda 
all: UseIdAgda Hello2

include ../Makefile.top

UseIdAgda: $(AGDA25) UseIdAgda.hs IdAgda.agda
	$(AGDA25) --ghc-dont-call-ghc --compile IdAgda.agda

# This one has a main function:
Hello2: $(AGDA25) Hello2.agda
	$(AGDA25) --compile Hello2.agda

clean:
	rm -rf ./MAlonzo Hello2 *.agdai *.o *.hi
