#! /bin/bash
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

error=0
processedfiles=0

for entry in "$1"/*.dfy
do
  processedfiles=$((processedfiles + 1))
  echo -e "${BLUE}-------------------------------------------------------${NC}"
  echo -e "${BLUE}Processing $entry${NC}"
  dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes "$entry"
  # echo "$result"
  if [ $? -eq 0 ] 
  then
      echo -e "${GREEN}No errors in $entry${NC}"
  else
      echo -e "${RED}Some errors occured in $entry${NC}"
      error=$((error + 1))
  fi
done

if [ $error -ne 0 ]
then
  echo -e "${RED}Some files [$error/$processedfiles] has(ve) errors :-("
else 
  echo -e "${GREEN}No errors occured! Great job.${NC}"
fi