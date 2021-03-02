#!/bin/sh

# Rename directories with vellvm in the name
find .. -name "*vellvm*" -exec rename vellvm vir {} \;
find .. -name "*Vellvm*" -exec rename Vellvm Vir {} \;

# Change vellvm to vir in files
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/vellvm/vir/g" {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/Vellvm/Vir/g" {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/VELLVM/VIR/g" {} \;

# Clean up the copyright headers
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>/Anonymized/g" {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/ - the Verified LLVM project/                            /g" {} \;

# Remove todo comments
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec perl -pi -e  "s|\(\* TODO.*?\*\)||g"  {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec perl -pi -e  "s|\(\* CB TODO.*?\*\)||g"  {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec perl -pi -e  "s|\(\* CB: TODO.*?\*\)||g"  {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec perl -pi -e  "s|\(\* YZ TODO.*?\*\)||g"  {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec perl -pi -e  "s|\(\* YZ: TODO.*?\*\)||g"  {} \;

# Remove comments from people
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec perl -pi -e  "s|\(\* Calvin.*?\*\)||g"  {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec perl -pi -e  "s|\(\* SAZ.*?\*\)||g"  {} \;
