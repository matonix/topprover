#!/usr/bin/env bash

if [ $# -eq 0 ]
  then
    echo "No arguments supplied"
    exit 1
fi

echo "generate $1"
mkdir $1
touch $1/Problem.v
touch $1/Example.v
cp _CoqProject $1
cd $1 && coq_makefile Example.v Problem.v > Makefile && make
echo "done."
tree $1
