
checkOpts=--without-K --exact-split
everythingOpts+=--allow-unsolved-metas
htmlOpts=--html --html-highlight=code --html-dir=docs --css=docs/Agda.css
AGDA ?=agda

src/everything.lagda.md :
	@rm -rf $@
	@cd src; \
	find . -type f \( -name "*.agda" -o -name "*.lagda"  -o -name  "*.lagda.md" \) > agdaFiles; \
	sort -o agdaFiles agdaFiles; \
	echo "\`\`\`agda" > everything.lagda.md; \
	echo "{-# OPTIONS $(everythingOpts) #-}" >> everything.lagda.md; \
	echo "module everything where" >> everything.lagda.md; \
	echo "" >> everything.lagda.md; \
	cat agdaFiles \
		| cut -c 3-               \
		| cut -f1 -d'.'           \
		| sed 's/\//\./g'         \
		| sed 's/^/open import /' \
		>> everything.lagda.md; \
	echo "\`\`\`" >> everything.lagda.md; \
	echo "Agda files: $(sed -n '$=' agdaFiles)"

.PHONY : check
check : src/everything.lagda.md 
	${AGDA} $?

html: src/everything.lagda.md
	mkdir -p docs
	rm -rf docs/*.html
	${AGDA} ${htmlOpts} src/everything.lagda.md 
	${AGDA} ${htmlOpts} --dependency-graph=docs/dependency.dot -v0 src/README.lagda.md
	cd docs/; \
	dot -Tpng -o graph.png dependency.dot; \
	sh conv.sh; \
	cp README.html index.html

.PHONY : clean
clean:
	rm -Rf _build/
