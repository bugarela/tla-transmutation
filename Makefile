.PHONY: compile

compile:
	ghc BlackboxTestGenerator.hs && ghc WhiteboxTestGenerator.hs && ghc CodeGenerator.hs
