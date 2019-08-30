#!/bin/sh
#
# Convenience wrapper for cmake in src/base/CMakeLists.txt
#
# Update Debug_tags/Trace_tags in case that debug/trace tags have been
# modified. Use diff to compare the contents of the *.tmp files with the
# corresponding *_tags file.
#
# Usage: gentags.sh Debug|Trace

tags_type="$1" # Debug/Trace
tags_file="${tags_type}_tags"

if [ "${tags_type}" != "Debug" ] && [ "${tags_type}" != "Trace" ]; then
  echo "$0: Invalid tags type '${tags_type}' (must be 'Debug' or 'Trace')"
  exit 1
fi

[ ! -e "${tags_file}.tmp" ] && \
    echo "$0: ${tags_file}.tmp does not exist" && exit 1

if [ -e "${tags_file}" ]; then
  # Do not update file if tags didn't change.
  diff -q "${tags_file}.tmp" "${tags_file}" > /dev/null 2>&1 && exit 0
fi
mv "${tags_file}.tmp" "${tags_file}"
