#!/bin/sh
grep -I --exclude-dir={lib} --exclude=greplist --exclude="*~" -Rif greplist .
