#!/bin/bash

# Test syntax
echo "Testing SYNTAX/"

for a in ../tests/syntax/good/*.cpp; do
	if ./main.byte --parse-only $a;
		then echo "OK    $a";
		else echo "FAIL  $a";
	fi;
done;

for a in ../tests/syntax/bad/*.cpp; do
	if ./main.byte --parse-only $a 2> /dev/null;
		then echo "FAIL  $a";
		else echo "OK    $a";
	fi;
done;

echo "---"
echo "Testing TYPING/ only against parsing"
for a in ../tests/typing/*/*.cpp; do
	if ./main.byte --parse-only $a;
		then echo "OK    $a";
		else echo "FAIL  $a";
	fi;
done;

echo "---"
echo "Testing EXEC/ only against parsing"
for a in ../tests/exec/*.cpp; do
	if ./main.byte --parse-only $a;
		then echo "OK    $a";
		else echo "FAIL  $a";
	fi;
done;

echo "---"
echo "Testing TYPING/"
for a in ../tests/typing/good/*.cpp; do
	if ./main.byte $a;
		then echo "OK    $a";
		else echo "FAIL  $a";
	fi;
done;

for a in ../tests/typing/bad/*.cpp; do
	if ./main.byte $a 2> /dev/null;
		then echo "FAIL  $a";
		else echo "OK    $a";
	fi;
done;

echo "---"
echo "Testing EXEC/ only against typing"
for a in ../tests/exec/*.cpp; do
	if ./main.byte --type-only $a;
		then echo "OK    $a";
		else echo "FAIL  $a";
	fi;
done;
