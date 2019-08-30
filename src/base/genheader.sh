#!/bin/sh
#
# Convenience wrapper for cmake in src/base/CMakeLists.txt
#
# Create Debug_tags.h/Trace_tags.h header files.
#
# Usage: genheader.sh <directory-mktags> Debug|Trace

path="$1"
shift
tags_type="$1" # Debug/Trace
tags_file="${tags_type}_tags"

if [ "${tags_type}" != "Debug" ] && [ "${tags_type}" != "Trace" ]; then
  echo "$0: Invalid tags type '${tags_type}' (must be 'Debug' or 'Trace')"
  exit 1
fi

[ ! -e "${tags_file}" ] && echo "$0: ${tags_file} does not exist" && exit 1

"${path}/mktagheaders" "${tags_file}" "${tags_file}" > "${tags_file}.h"
