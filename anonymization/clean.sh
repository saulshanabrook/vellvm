#!/bin/sh

find .. -name "*vellvm*" -exec rename vellvm vir {} \;
find .. -name "*Vellvm*" -exec rename Vellvm Vir {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/vellvm/vir/g" {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/Vellvm/Vir/g" {} \;
find .. -not -path "*anonymization*" -not -path "*.git*" -type f -exec sed -i -e "s/VELLVM/VIR/g" {} \;
