#!/usr/bin/env bash

set -eux

# Hashtable of checksums
#
# When adding support for a new Agda version, add its checksum here.
# You can find it at the Agda release page, in gray text next to the
# Linux executable.
declare -rA VERSION_CHECKSUMS=(
  ['2.8.0']='824081b8dcbe431289a50ac6bd83e451f390c51c3884ac7a8c4a5c0df2632faf'
)

if [ $# -lt 1 ]; then
  echo 'The script needs to be called with the Agda version as its first argument.'
  exit 1
fi

AGDA_VERSION=$1
AGDA_OUTFILE=agda.tar.xz

AGDA_URL=https://github.com/agda/agda/releases/download/v${AGDA_VERSION}/Agda-v${AGDA_VERSION}-linux.tar.xz

# Fetch the file
wget -O "${AGDA_OUTFILE}" "${AGDA_URL}"

# Check the hash
if ! (echo "${VERSION_CHECKSUMS["${AGDA_VERSION}"]} ${AGDA_OUTFILE}" | sha256sum --check); then
  echo 'Hash mismatch, expected ${VERSION_CHECKSUMS["${AGDA_VERSION}"]}'
  echo 'Got'
  sha256sum "${AGDA_OUTFILE}"
  exit 2
fi

# Extract the binary
mkdir bin
tar xJf "${AGDA_OUTFILE}" -C bin

# Make the binary available
echo "$(pwd)/bin/" >> $GITHUB_PATH
