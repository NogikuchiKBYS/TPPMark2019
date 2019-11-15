#!/bin/sh
rm -f RunExample.vo
coq_makefile -f _CoqProject -o CoqMakefile && make -f CoqMakefile RunExample.vo
