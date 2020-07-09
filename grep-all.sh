#!/bin/sh
grep -I --exclude-dir={lib,.git} --exclude=grepcaselist --exclude=greplist --exclude "*#*" "*~" "*aux*" -Rif greplist .
grep -I --exclude-dir={lib,.git} --exclude=grepcaselist --exclude=greplist --exclude={"*#*", "*~", "*aux*"} -Rf grepcaselist .
