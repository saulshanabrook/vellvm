#!/bin/sh

grep --exclude-dir=.git --exclude-dir=_qc_src.tmp/ --exclude-dir=lib --exclude="*aux" -RIif greplist ../
# find . -iname "
