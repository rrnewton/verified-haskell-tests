

# Proofs are not very future proof because there aren't good packaging
# systems for them.

# Still, we can use containers and other tricks to make a given proof
# build reliably.

.PHONY: tools agda

tools: ./bin/agda

# Install agda 2.4.2.3
./bin/agda:
	stack install --local-bin-path=./bin --resolver=lts-3.0 Agda

AGDA=$(PWD)/bin/agda
# Here's an alternate command to run Agda 2.4.2.3:
# AGDA= docker run -i --rm -v $(HOME):$(HOME) banacorn/agda:2.4.2.3 agda

agda:
	$(AGDA) --version
	cd ./verify_and_warm_up/agda/ && \
	$(AGDA) VerifyAnd.agda
