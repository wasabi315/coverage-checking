FLAGS = --config=rewrite-rules.yaml
LIBRARIES =

.PHONY: app clean clean-lib clean-agdai

lib: src/CoverageCheck.agda
	mkdir lib
	agda2hs $(FLAGS) $(LIBRARIES) $< -o lib

clean: clean-lib clean-agdai

clean-lib:
	rm -rf lib

clean-agdai:
	find src -iname *.agdai -delete
	rm -rf _build

app: lib
	cabal build

clean-hs:
	rm -rf dist-newstyle
