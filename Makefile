
checkOpts :=--without-K --exact-split
everythingOpts :=$(checkOpts) --allow-unsolved-metas
agdaVerbose?=0
# export agdaVerbose=20 if you want to see all

htmlOpts=--html --html-highlight=code --html-dir=docs --css=docs/Agda.css
AGDA ?=agda -v$(agdaVerbose)
TIME ?=time

gen-file-list : agdaFiles
	@rm -rf src/everything.lagda.md ;\
	find src -type f \( -name "*.agda" -o -name "*.lagda"  -o -name  "*.lagda.md" \) > $?; \
	sort -o $? $?; \
	wc -l $?

.PHONY : src/everything.lagda.md
src/everything.lagda.md : gen-file-list
	@echo "\`\`\`agda" > $@ ;\
	echo "{-# OPTIONS $(everythingOpts) #-}" >> $@ ;\
	echo "module everything where" >> $@ ;\
	echo "" >> $@ ;\
	cat agdaFiles \
		| cut -c 5-               \
		| cut -f1 -d'.'           \
		| sed 's/\//\./g'         \
		| sed 's/^/open import /' \
		>> $@ ;\
	echo "\`\`\`" >> $@ ;

.PHONY : check
check : src/everything.lagda.md
	@${TIME} ${AGDA} $?

html: src/everything.lagda.md
	mkdir -p docs
	rm -rf docs/*.html
	${AGDA} ${htmlOpts} src/everything.lagda.md 
	${AGDA} ${htmlOpts} --dependency-graph=docs/dependency.dot src/README.lagda.md
	cd docs/; \
	dot -Tpng -o graph.png dependency.dot; \
	sh conv.sh; \
	cp README.html index.html

.PHONY : clean
clean:
	rm -Rf _build/
