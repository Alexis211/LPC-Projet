#!/bin/sh

menhir -v parser.mly
rm parser.mli parser.ml
