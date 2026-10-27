#!/usr/bin/env bash
set -euo pipefail

# ---- Check clang-format presence ----
if ! command -v clang-format >/dev/null 2>&1; then
  echo "Error: clang-format not found in PATH"
  exit 1
fi

# ---- Check clang-format version ----
version_str="$(clang-format --version)"
# Extract first number after "version" (major version)
version="$(echo "$version_str" | sed -E 's/.*version ([0-9]+).*/\1/')"

if [[ -z "$version" ]]; then
  echo "Error: Failed to parse clang-format version"
  echo "Output was: $version_str"
  exit 1
fi

if (( version < 22 )); then
  echo "Error: clang-format version >= 22 required, found $version"
  exit 1
fi

# ---- Mode selection ----
mode="${1:-check}"  # default = check

case "$mode" in
  check)
    clang_flags=(--dry-run --Werror)
    ;;
  fix)
    clang_flags=(-i)
    ;;
  *)
    echo "Usage: $0 [check|fix]"
    exit 1
    ;;
esac

# ---- Run clang-format ----
find src include test examples \
  -type f \
  \( -name '*.cpp' -o -name '*.h' -o -name '*.java' \) -print0 | \
xargs -0 clang-format \
  "${clang_flags[@]}" \
  -style=file
