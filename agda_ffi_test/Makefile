

default: UseIdAgda.exe
all: UseIdAgda Hello2

include ../Makefile.top

UseIdAgda.exe: $(AGDA25) UseIdAgda.hs IdAgda.agda
	$(AGDA25) --ghc-dont-call-ghc --compile IdAgda.agda
	$(GHC) -O2 UseIdAgda.hs -o $@

# This one has a main function:
Hello2: $(AGDA25) Hello2.agda
	$(AGDA25) --compile Hello2.agda

clean:
	rm -rf ./MAlonzo Hello2 *.agdai *.o *.hi
