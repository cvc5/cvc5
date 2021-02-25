#!/usr/bin/env python3

import argparse
import glob
import os
import re
import shutil
import subprocess


def parse_args():
    ap = argparse.ArgumentParser(description='collect debug and trace tags')
    ap.add_argument('destdir', help='where to put the results')
    ap.add_argument('type', choices=['Debug', 'Trace'], help='which tags to collect')
    ap.add_argument('basedir', help='where to look for source file')
    return ap.parse_args()

def collect_tags(basedir):
    tags = set()
    for ext in ['.cc', '.cpp', '.g', '.h']:
        for filename in glob.iglob(f'{basedir}/**/*{ext}', recursive=True):
            content = open(filename).read()
            for tag in RE_PAT.finditer(content):
                tags.add(tag.group(1))
    return sorted(tags)


def write_tmp_file(filename, type, tags):
    with open(filename, 'w') as out:
        out.write(f'static char const* const {type}_tags[] = {{\n')
        for t in tags:
            out.write(f'\"{t}\",\n')
        out.write('nullptr\n')
        out.write('};\n')


if __name__ == '__main__':
    opts = parse_args()
    RE_PAT = re.compile(f'{opts.type}(?:\\.isOn)?\\("([^"]+)"\\)')
    FILENAME_TMP = f'{opts.destdir}/{opts.type}_tags.tmp'
    FILENAME_DEST = f'{opts.destdir}/{opts.type}_tags.h'


    tags = collect_tags(opts.basedir)
    write_tmp_file(FILENAME_TMP, opts.type, tags)
    if not os.path.isfile(FILENAME_DEST):
        shutil.copy(FILENAME_TMP, FILENAME_DEST)
    elif subprocess.run(['diff', FILENAME_TMP, FILENAME_DEST], stdout=subprocess.PIPE).returncode == 1:
        shutil.copy(FILENAME_TMP, FILENAME_DEST)
