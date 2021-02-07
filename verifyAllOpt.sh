#! /bin/bash
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

error=0
processedfiles=0
basedir="src/dafny/smart"
# verify each folder with a suitable verifier configuration
# src/dafny/smart/algorithms
# dafny3 /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /trace  CommuteProof.dfy
# dafny3 /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /trace  IndexBasedAlgorithm.dfy
# dafny3 /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /trace  MainAlgorithm.dfy
# dafny3 /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /trace  OptimalAlgorithm.dfy

for value in algorithms helpers paths seqofbits synthattribute trees .
# for value in "./"
# for value in trees
do
    echo -e "${BLUE}-------------------------------------------------------${NC}"
    echo -e "${BLUE}==> Processing *.dfy files in subdir $basedir/$value"
    echo -e "${BLUE}-------------------------------------------------------${NC}"
    for entry in "$basedir/$value"/*.dfy
    do
      processedfiles=$((processedfiles + 1))
      # echo -e "${BLUE}-------------------------------------------------------${NC}"
      echo -e "${BLUE}Processing $entry${NC}"
      # dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /trace /noCheating:1 $entry
      dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /trace /noCheating:1 /proverWarnings:1 /vcsMaxKeepGoingSplits:10 /vcsCores:12 /vcsMaxCost:1000 /vcsKeepGoingTimeout:10 /restartProver /verifySeparately $entry
      # echo "$result"
      if [ $? -eq 0 ] 
      then
          echo -e "${GREEN}No errors in $entry${NC}"
      else
          echo -e "${RED}Some errors occured in $entry${NC}"
          error=$((error + 1))
      fi
    done

    echo -e "${BLUE}-------------------------------------------------------${NC}"
    if [ $error -ne 0 ]
    then
      echo -e "${RED}Some files [$error/$processedfiles] has(ve) errors :-("
      # exit 1
    else 
      echo -e "${GREEN}No errors occured in $processedfiles files! Great job.${NC}"
      # exit 0
    fi
    echo -e "${BLUE}<== [DONE] subdir $basedir/$value"
    echo -e "${BLUE}-------------------------------------------------------${NC}"


done

# for entry in "$1"/*.dfy
# do
#   processedfiles=$((processedfiles + 1))
#   echo -e "${BLUE}-------------------------------------------------------${NC}"
#   echo -e "${BLUE}Processing $entry${NC}"
#   dafny3 /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /trace /noCheating:1 /proverWarnings:1 /vcsMaxKeepGoingSplits:10 /vcsCores:12 /vcsMaxCost:1000 /vcsKeepGoingTimeout:8 /restartProver /verifySeparately "$entry"
#   # echo "$result"
#   if [ $? -eq 0 ] 
#   then
#       echo -e "${GREEN}No errors in $entry${NC}"
#   else
#       echo -e "${RED}Some errors occured in $entry${NC}"
#       error=$((error + 1))
#   fi
# done

# if [ $error -ne 0 ]
# then
#   echo -e "${RED}Some files [$error/$processedfiles] has(ve) errors :-("
#   exit 1
# else 
#   echo -e "${GREEN}No errors occured! Great job.${NC}"
#   exit 0
# fi