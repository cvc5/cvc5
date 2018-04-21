#!/bin/bash

for f in *_options; do echo $f; time ./mkoptions-toml module-sed $f > ${f}.toml; done
