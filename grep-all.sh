#!/bin/sh
grep -I --exclude-dir={lib} --exclude=greplist --exclude="*#*" --exclude="*~" --exclude="*aux*" -Rif greplist .
grep -I --exclude-dir={lib} --exclude=grepcaselist  --exclude="*#*" --exclude="*~" --exclude="*aux*" -Rf grepcaselist .
