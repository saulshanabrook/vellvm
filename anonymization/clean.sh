#!/bin/sh

find .. -name "*vellvm*" -exec rename vellvm vir {} \;
find .. -name "*Vellvm*" -exec rename Vellvm Vir {} \;
