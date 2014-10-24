#! /usr/bin/env sh

FILE=$1
if [ $# == 0 ]
then 
  FILE=src/Main 
else 
  shift 
fi

exec env GHCI_LOAD=$FILE ghci $@
