
.PHONY : src/everything.agda
src/everything.agda :
	@rm -rf $@
	@cd src && find . -type f \( -name "*.agda" -o -name "*.lagda"  -o -name  "*.lagda.md" \) > agdaFiles
	@cd src && sort -o agdaFiles agdaFiles
	@cd src && echo "-- everything" > everything.agda
	@cd src && echo "-- The list of Agda modules below is automatically generated." >> everything.agda
	@cd src && echo "{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}" >> everything.agda
	@cd src && echo "module everything where" >> everything.agda
	@cd src && echo "" >> everything.agda
	@cd src && cat agdaFiles \
		| cut -c 3-               \
		| cut -f1 -d'.'           \
		| sed 's/\//\./g'         \
		| sed 's/^/open import /' \
		>> everything.agda

.PHONY : check
check : src/everything.agda
	agda src/everything.agda

html: src/everything.agda
	mkdir -p docs
	rm -rf docs/*.html
	agda --html --html-dir=docs src/everything.agda --dependency-graph=docs/dependency.dot -v0
	dot -Tpng -o docs/graph.png docs/dependency.dot
	cp docs/everything.html docs/index.html

