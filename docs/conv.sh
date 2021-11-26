# Adapted from https://jonaprieto.github.io/synthetic-graph-theory/conv.sh
#
# 1. Install pandoc from http://johnmacfarlane.net/pandoc/
# 2. Copy this script into the directory containing the .md files
# 3. Ensure that the script has all the permissions to be executed
# $ chmod +x conv.sh
# 4. Run the script
# $ ./conv.sh

AGDAVERSION=$(agda --version)
PANDOCVERSION=$(pandoc --version | head -n 1)

FILES=*.md

for f in $FILES
do
  filename="${f%.*}"
  echo "Converting $f to $filename.html"
  pandoc --standalone \
         --metadata-file="_config.yml" \
         --template=template.html5 \
         $f \
         --from markdown+tex_math_dollars+tex_math_double_backslash+latex_macros+lists_without_preceding_blankline \
         --to=html5  \
         --mathjax \
         -o $filename.html \
         --variable=updated:"$(date +'%A, %B %e, %Y, %I:%M %p')" \
         --variable=lastCommit:"$(git log --pretty='format:(%as)(%h) %Creset%s by %cl' --no-merges -15)" \
         --variable=agdaVersion:"$AGDAVERSION" \
         --variable=pandocVersion:"${PANDOCVERSION:u}" \
         --variable=file:$f
  rm $f
done