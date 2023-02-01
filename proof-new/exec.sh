#!/bin/bash

build/bin/cvc5 \
	--produce-proofs \
	--proof-granularity=dsl-rewrite \
	--dump-proofs \
	--proof-format-mode=alethe \
	--dag-thres=0 \
	$1

