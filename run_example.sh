#!/bin/sh
coq_makefile -f _CoqProject -o CoqMakefile && make -f CoqMakefile -B Example.vo
