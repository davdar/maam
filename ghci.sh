#! /usr/bin/env sh

MODULE=$1
if [ $# == 0 ]
then 
  MODULE=src/Lang/LamIf/Main.hs
else 
  shift 
fi

exec env GHCI_LOAD=$MODULE ghci $@
