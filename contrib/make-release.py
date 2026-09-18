#!/usr/bin/env python3
###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
##

import argparse
import collections
import logging
import os
import re
import subprocess
import sys

args = None


def exec(cmd):
    """Execute given command"""
    return subprocess.check_output(cmd).decode().strip()


def parse_options():
    """Handle command line options"""
    ap = argparse.ArgumentParser(description='Make a new release')
    ap.add_argument('bump',
                    choices=['major', 'minor', 'patch'],
                    help='which version part to bump')
    ap.add_argument('-v',
                    '--verbose',
                    action='store_true',
                    help='be more verbose')
    global args
    args = ap.parse_args()

    logging.basicConfig(format='[%(levelname)s] %(message)s')
    if args.verbose:
        logging.getLogger().setLevel(level=logging.DEBUG)
    else:
        logging.getLogger().setLevel(level=logging.INFO)


def identify_next_version():
    """Figure out the new version number"""
    try:
        curversion = exec(['git', 'describe', '--tags', '--match', 'cvc5-*'])
    except:
        logging.error('git describe was unable to produce a proper version')
        sys.exit(1)
    logging.debug('git version info: {}'.format(curversion))

    re_release = re.compile(r'^cvc5-(\d+)\.(\d+)\.(\d+)')
    m = re_release.match(curversion)
    if m:
        major, minor, patch = map(int, m.groups())
        if args.bump == 'major':
            major += 1
            minor = 0
            patch = 0
        elif args.bump == 'minor':
            minor += 1
            patch = 0
        elif args.bump == 'patch':
            patch += 1
        version = "{}.{}.{}".format(major, minor, patch)
        logging.debug('target version: {}'.format(version))
        return version

    logging.error(
        "Did not understand current git version: '{}'".format(curversion))
    sys.exit(1)


def generate_cmake_version_file(version, is_release):
    """Update the cmake version file"""
    filename = os.path.join(os.path.dirname(os.path.dirname(__file__)),
                            'cmake/version-base.cmake')
    tpl = open(filename + '.template').read()
    tpl = tpl.replace('{{VERSION}}', version)
    tpl = tpl.replace('{{IS_RELEASE}}', 'true' if is_release else 'false')
    open(filename, 'w').write(tpl)


def finalize_news_file(version):
    """Check the news file and drop the prerelease marker of its top section.

    The release notes on the release page are extracted from the section
    titled 'cvc5 <version>', so the top section of the news file has to be
    titled like that. A leftover 'prerelease' marker is removed, any other
    title (in particular, a different version) is an error.
    Returns whether the news file was modified.
    """
    filename = os.path.join(os.path.dirname(os.path.dirname(__file__)),
                            'NEWS.md')
    content = open(filename).read()
    re_section = re.compile(r'^(cvc5 .*?)[ \t]*\n=+[ \t]*$', re.MULTILINE)
    m = re_section.search(content)
    if not m:
        logging.error('Did not find any release section in NEWS.md')
        sys.exit(1)

    curtitle = m.group(1)
    title = 'cvc5 {}'.format(version)
    if curtitle == title:
        return False
    if curtitle != '{} prerelease'.format(title):
        logging.error("Top section of NEWS.md is titled '{}', expected '{}' "
                      "or '{} prerelease'".format(curtitle, title, title))
        sys.exit(1)

    newcontent = '{}{}\n{}{}'.format(content[:m.start()], title,
                                     '=' * len(title), content[m.end():])
    open(filename, 'w').write(newcontent)
    return True


def make_release_commit(version, news_updated):
    """Make the release commit"""
    tagname = 'cvc5-{}'.format(version)
    if news_updated:
        exec(['git', 'add', 'NEWS.md'])
    exec(['git', 'add', 'cmake/version-base.cmake'])
    exec(['git', 'commit', '-m', 'Bump version to {}'.format(version)])
    exec(['git', 'tag', tagname])
    return tagname


def make_post_release_commit(version):
    """Make the post-release commit"""
    exec(['git', 'add', 'cmake/version-base.cmake'])
    exec(['git', 'commit', '-m', 'Start post-release for {}'.format(version)])
    return exec(['git', 'rev-parse', 'HEAD'])


if __name__ == '__main__':
    parse_options()

    # Compute next version
    version = identify_next_version()

    # Check the news file before touching anything else
    news_updated = finalize_news_file(version)

    # release commit
    logging.info('Performing release commit')
    generate_cmake_version_file(version, True)
    tagname = make_release_commit(version, news_updated)

    # post-release commit
    logging.info('Performing post-release commit')
    generate_cmake_version_file(version, False)
    postcommit = make_post_release_commit(version)

    # Show commits and ask user to push
    print('Please check the following commits carefully:')
    subprocess.call(['git', 'show', tagname])
    subprocess.call(['git', 'show', postcommit])

    print(
        'If you are sure you want to push this release, use the following command:'
    )
    print(f'\tgit push origin main       # push commits')
    print(f'\tgit push origin {tagname}  # push tag {tagname}')
