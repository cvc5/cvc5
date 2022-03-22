#!/usr/bin/env python3

import json
import re
import subprocess
import sys


def demangle(name):
    """Demangle a C++ symbol using c++filt."""
    pipe = subprocess.Popen(['c++filt', name],
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE)
    stdout, _ = pipe.communicate()
    return stdout.decode().strip()


def get_uncovered(data, file_patterns):
    """Collect all uncovered functions from files matching the given patterns.
       Returns a list of dicts with filename, function and startline."""
    notcovered = []

    for file, fdata in data['sources'].items():
        if all([re.search(f, file) == None for f in file_patterns]):
            continue
        for function, funcdata in fdata['']['functions'].items():
            if funcdata['execution_count'] == 0:
                notcovered.append({
                    'filename': file,
                    'startline': funcdata['start_line'],
                    'function': demangle(function),
                })

    notcovered.sort(key=lambda s: (s['filename'], s['startline']))
    return notcovered


if __name__ == "__main__":
    patterns = ['src/api/cpp/cvc5.*']
    data = json.load(open('coverage.json', 'r'))
    notcovered = get_uncovered(data, patterns)
    for nc in notcovered:
        print('starting in {filename}:{startline}'.format(**nc))
        print('function {function}'.format(**nc))
        print('')
    if notcovered:
        sys.exit(1)
    sys.exit(0)
