
.PHONY : src/everything.agda
src/everything.agda :
	@rm -rf $@
	@cd src && find . -type f \( -name "*.agda" -o -name "*.lagda"  -o -name  "*.lagda.md" \) > agdaFiles
	@cd src && sort -o agdaFiles agdaFiles
	@cd src && echo "-- everything" > everything.agda
	@cd src && echo "-- The list of Agda modules below is automatically generated." >> everything.lagda.md
	@cd src && echo "{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}" >> everything.lagda.md
	@cd src && echo "module everything where" >> everything.lagda.md
	@cd src && echo "" >> everything.lagda.md
	@cd src && cat agdaFiles \
		| cut -c 3-               \
		| cut -f1 -d'.'           \
		| sed 's/\//\./g'         \
		| sed 's/^/open import /' \
		>> everything.lagda.md

.PHONY : check
check : src/everything.lagda.md
	agda src/everything.lagda.md

html: src/everything.lagda.md
	mkdir -p docs
	rm -rf docs/*.html
	agda --html --html-highlight=code --html-dir=docs src/everything.lagda.md --css=docs/Agda.css
	agda --html --html-highlight=code --html-dir=docs src/README.lagda.md --css=docs/Agda.css --dependency-graph=docs/dependency.dot -v0
	dot -Tpng -o docs/graph.png docs/dependency.dot
	cd docs/ && sh conv.sh
	cp docs/README.html  docs/index.html
