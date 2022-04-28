#!/usr/bin/env python3

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

    re_release = re.compile('^cvc5-(\d+)\.(\d+)\.(\d+)')
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


def make_release_commit(version):
    """Make the release commit"""
    tagname = 'cvc5-{}'.format(version)
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

    # release commit
    logging.info('Performing release commit')
    generate_cmake_version_file(version, True)
    tagname = make_release_commit(version)

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
