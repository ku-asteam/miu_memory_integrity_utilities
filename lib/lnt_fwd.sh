#!/bin/bash
hascinput=0

echo "clang -flto Interposed..."
#clang -flto ${1+"$@"}

for var in "$@"
do
  echo "$var"
  if [[ $var == *.c ]];
  then	
    hascinput=1
    break;
  fi
done
echo "C src inserted.."
if [[ $hascinput == 1 ]];
then
  echo "Generating objects.. (bitcode)"
  clang -flto ${1+"$@"}
else
  echo "Linking.." 
  clang ${1+"$@"}
fi
