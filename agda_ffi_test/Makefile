

default: UseIdAgda 
all: UseIdAgda Hello2

UseIdAgda: UseIdAgda.hs IdAgda.agda
	agda --ghc-dont-call-ghc --compile IdAgda.agda

# This one has a main function:
Hello2: Hello2.agda
	agda --compile Hello2.agda

clean:
	rm -rf ./MAlonzo Hello2 *.agdai *.o *.hi

