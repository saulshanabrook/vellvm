#!/bin/sh

find .. -name "*vellvm*" -exec rename vellvm vir {} \;
find .. -name "*Vellvm*" -exec rename Vellvm Vir {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/vellvm/vir/g" {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/Vellvm/Vir/g" {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/VELLVM/VIR/g" {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>/Anonymized/g" {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/ - the Verified LLVM project/                            /g" {} \;
