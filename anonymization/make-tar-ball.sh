#!/bin/sh

# Make sure you call this from the anonymization directory!
# Note: this script deletes things... Be careful :).

# Make sure that we have all of the git submodules pre-packaged
git submodule update --init

# Remove git information
rm ../.gitmodules
rm ../.gitignore
rm -rf ../.git

# Remove this directory
cd ..
rm -rf anonymization

# Go to directory containing vir to make vir.tar.gz
VIRPATH=$(pwd)
cd ..
VIRPATH=$(realpath --relative-to=. $VIRPATH)
tar --owner=0 --group=0 -cvzf vir.tar.gz $VIRPATH
