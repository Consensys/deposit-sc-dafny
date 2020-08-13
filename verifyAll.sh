#! /bin/bash
for entry in "$1"/*.dfy
do
  echo "$entry"
  dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes "$entry"
done