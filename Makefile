
checkOpts :=--without-K --exact-split --guardedness
everythingOpts :=$(checkOpts)
agdaVerbose?=-v1
# use "$ export agdaVerbose=20" if you want to see all
AGDAFILES := $(wildcard src/**/*.lagda.md)
HTMLFILES := $(AGDAFILES:.lagda.md=.html)

bar := $(foreach f,$(AGDAFILES),$(shell wc -l $(f))"\n")

AGDAHTMLFLAGS?=--html --html-highlight=code --html-dir=docs --css=docs/Agda.css
AGDA ?=agda $(agdaVerbose)
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

# FIXME: update this to only use agda and output in book folder directly
# when writing the book
.PHONY: html
html: $(HTMLFILES)

%.html: %.lagda.md
	@echo "... $@"
	@pandoc --standalone \
				--metadata-file=docs/_config.yml \
				--template=docs/template.html5 \
				--metadata \
        title="Expected HTML" \
				$? \
				--from markdown+tex_math_dollars+tex_math_double_backslash+latex_macros+lists_without_preceding_blankline \
				--to=html5  \
				--mathjax \
				-o $@ \
				--variable=reload:"true"

agda-html: src/everything.lagda.md
	mkdir -p docs
	rm -rf docs/*.html
	${AGDA} ${AGDAHTMLFLAGS} src/everything.lagda.md

.PHONY: website
website: agda-html
	@mdbook build

.phony: serve-website
serve-wesite:
	@mdbook serve -p 8080

.PHONY : graph
graph:
	${AGDA} ${AGDAHTMLFLAGS} --dependency-graph=docs/dependency.dot src/README.lagda.md

.PHONY : clean
clean:
	rm -Rf _build/
	find docs -name '*.html' -and -name '*.md' -delete -print0