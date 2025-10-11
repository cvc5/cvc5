#!/bin/sh

# Removes the word 'demos' from the 'SUBDIRS =' line in Makefile.in
# This prevents building the demos programs, which require Bison.
#
#   /^SUBDIRS =/ -> only applies the substitution to lines starting with SUBDIRS =
#   s/patten//g  -> replaces all occurrences of 'pattern' with nothing
#   where:
#     \bdemos\b -> matches the word demos exactly (word boundaries)
#      *        -> removes any spaces following demos
#
sed -i.orig '/^SUBDIRS =/s/\bdemos\b *//g' "$1/Makefile.in"
