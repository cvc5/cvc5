#!/bin/sh
#
# Convenience wrapper for cmake in src/base/CMakeLists.txt
#
# Create Debug_tags.tmp/Trace_tags.tmp files from given source files.
#
# Usage: gentmptags.sh <directory-mktags> Debug|Trace <source files ...>

path="$1"
shift
tags_type="$1"
tags_file="${tags_type}_tags"
shift
source_files_list="$*"

if [ "${tags_type}" != "Debug" ] && [ "${tags_type}" != "Trace" ]; then
  echo "$0: Invalid tags type '${tags_type}' (must be 'Debug' or 'Trace')"
  exit 1
fi

"${path}/mktags" "${tags_type}" "${source_files_list}" > "${tags_file}.tmp"
