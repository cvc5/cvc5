#!/bin/bash
#
# Enumerates public interface headers, so that public-only documentation
# can be produced.
#

cd "$(dirname "$0")"

echo -n "\"$srcdir/src/include/cvc4.h\" "
echo -n "\"$srcdir/src/include/cvc4_public.h\" "
( (find "$builddir" -name '*.h' | xargs grep -l '^# *include  *"cvc4.*_public\.h"'); \
  (find "$srcdir" -name '*.h' | xargs grep -l '^# *include  *"cvc4.*_public\.h"'); \
) | \
while read f; do
  if expr "$f" : ".*_\(template\|private\|test_utils\)\.h$" &>/dev/null; then
    continue
  fi
  echo -n "\"$f\" "
done

