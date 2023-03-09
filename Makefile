
CHECKOPTS :=--without-K --exact-split --guardedness
everythingOpts :=$(CHECKOPTS)
AGDAVERBOSE?=-v1
# use "$ export AGDAVERBOSE=20" if you want to see all
AGDAFILES := $(wildcard src/**/*.lagda.md)
AGDAMDFILES:= $(subst src/,docs/,$(AGDAFILES:.lagda.md=.md))

bar := $(foreach f,$(AGDAFILES),$(shell wc -l $(f))"\n")

AGDAHTMLFLAGS?=--html --html-highlight=code --html-dir=docs --css=Agda.css --only-scope-checking
AGDA ?=agda $(AGDAVERBOSE)
TIME ?=time

METAFILES:=CITATION.cff \
			CODINGSTYLE.md \
			CONTRIBUTORS.md \
			CONVENTIONS.md \
			DESIGN-PRINCIPLES.md \
			HOME.md \
			HOWTO-INSTALL.md \
			LICENSE.md \
			MAINTAINERS.md \
			README.md \
			STATEMENT-OF-INCLUSION.md \
			SUMMARY.md \
			USERS.md \

.PHONY : agdaFiles
agdaFiles :
	@rm -rf $@
	@rm -rf src/everything.lagda.md
	@find src -type f \( -name "*.agda" -o -name "*.lagda"  -o -name  "*.lagda.md" \) > $@
	@sort -o $@ $@
	@wc -l $@
	@echo "$(shell (find src -name '*.lagda.md' -print0 | xargs -0 cat ) | wc -l) LOC"

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

AGDAMDFILES: $(AGDAMDFILES)

docs/%.md: src/%.lagda.md
	@echo "... $@"
	@${AGDA} ${AGDAHTMLFLAfoGS} $<

agda-html: src/everything.lagda.md
	@rm -rf docs/
	@mkdir -p docs/
	@${AGDA} ${AGDAHTMLFLAGS} src/everything.lagda.md

.PHONY: website
website: agda-html
	@cp $(METAFILES) docs/
	@mdbook build

update-contributors:
	@python update-contributors.py

.phony: serve-website
serve-website:
	@mdbook serve -p 8080 --open -d ./book/html

.PHONY : graph
graph:
	${AGDA} ${AGDAHTMLFLAGS} --dependency-graph=docs/dependency.dot src/README.lagda.md

.PHONY : clean
clean:
	rm -Rf _build/
	find docs -name '*.html' -and -name '*.md' -delete -print0

.PHONY : pre-commit
pre-commit:
	@make check
	@pre-commit run --all-files
