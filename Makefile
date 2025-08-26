FLAGS =
LIBRARIES =

.PHONY: app alllib clean clean-lib clean-agdai

# this should stay in sync with the modules defined in cabal
# also the order is silly, we redo a lot of the work because we don't know the dependencies
alllib: lib \
	lib/CoverageCheck/Prelude.hs \
	lib/CoverageCheck/Name.hs \
	lib/CoverageCheck/GlobalScope.hs \
	lib/CoverageCheck/Syntax.hs \
	lib/CoverageCheck/Instance.hs \
	lib/CoverageCheck/Subsumption.hs \
	lib/CoverageCheck/Usefulness.hs \
	lib/CoverageCheck/Usefulness/Algorithm.hs \
	lib/CoverageCheck/Usefulness/Useful.hs \
	lib/CoverageCheck/Usefulness/UsefulP.hs \
	lib/CoverageCheck/Exhaustiveness.hs \
	lib/CoverageCheck.hs

lib:
	mkdir lib

lib/%.hs: src/%.agda
	agda2hs $(FLAGS) $(LIBRARIES) $< -o lib

clean: clean-lib clean-agdai

clean-lib:
	rm -rf lib

clean-agdai:
	find src -iname *.agdai -delete
	rm -rf _build

app: alllib
	cabal build

clean-hs:
	rm -rf dist-newstyle
