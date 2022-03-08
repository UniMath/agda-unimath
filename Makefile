
checkOpts :=--without-K --exact-split
everythingOpts :=$(checkOpts) --allow-unsolved-metas
agdaVerbose?=1
# use "$ export agdaVerbose=20" if you want to see all
AGDA_FILES := $(wildcard ./src/**/*.lagda.md)
bar := $(foreach f,$(AGDA_FILES),$(shell wc -l $(f))"\n")

htmlOpts=--html --html-highlight=code --html-dir=docs --css=docs/Agda.css
AGDA ?=agda -v$(agdaVerbose)
TIME ?=time

.PHONY : agdaFiles
agdaFiles : 
	@rm -rf $@
	@rm -rf src/everything.lagda.md
	@find src -type f \( -name "*.agda" -o -name "*.lagda"  -o -name  "*.lagda.md" \) > $@
	@sort -o $@ $@
	@wc -l $@
	@echo "$(shell (find src -name '*.lagda.md' -print0 | xargs -0 cat ) | wc -l) LOC"


# for p in $(shell cat $@); do echo $(shell wc -l $p); done


.PHONY : src/everything.lagda.md
src/everything.lagda.md : agdaFiles
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
	${TIME} ${AGDA} $?

html: src/everything.lagda.md
	mkdir -p docs
	rm -rf docs/*.html
	${AGDA} ${htmlOpts} src/everything.lagda.md 
	cd docs/; \
	sh conv.sh; \
	cp README.html index.html

.PHONY : graph
graph:
	${AGDA} ${htmlOpts} --dependency-graph=docs/dependency.dot src/README.lagda.md

.PHONY : clean
clean:
	rm -Rf _build/
