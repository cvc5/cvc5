###############################################################################
# Top contributors (to current version):
#   Makai Mann
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# ############################################################################
#
# Script for building wheels distribution for pycvc5
#
# Example usage (from top-level directory):
#   python3 ./src/api/python/wheels/build_wheel.py bdist_wheel
# Configures and builds in directory ./build
# Creates wheel in ./dist
#
##

import os
import re
import sys
import platform
import subprocess
import multiprocessing
import shutil

from setuptools import setup, Extension
from setuptools.command.build_ext import build_ext
from skbuild.cmaker import CMaker
from distutils.version import LooseVersion

WORKING_DIR="build"

def get_project_src_path():
    # expecting this script to be in src/api/python/wheels
    # The project source directory is 4 directories up
    # (5 dirnames because start with file)
    project_src_path = __file__
    for i in range(5):
        project_src_path = os.path.dirname(project_src_path)
    return os.path.abspath(project_src_path)


def get_cvc5_version():
    project_src_path = get_project_src_path()

    # read CMakeLists.txt to get version number
    version = dict()
    str_pattern = 'set\(CVC5_(?P<component>MAJOR|MINOR|RELEASE)\s*(?P<version>\d+)\)'
    pattern = re.compile(str_pattern)
    with open(os.path.join(project_src_path, 'CMakeLists.txt'), 'r') as f:
        for line in f:
            line = line.strip()
            m = pattern.search(line)
            if m:
                gd = m.groupdict()
                version[gd['component']] = gd['version']
                if len(version) == 3:
                    break

    assert len(version) == 3, 'Expecting MAJOR, MINOR and RELEASE'
    return version['MAJOR'], version['MINOR'], version['RELEASE']


class CMakeExtension(Extension):
    def __init__(self, name, sourcedir=''):
        Extension.__init__(self, name, sources=[])
        self.sourcedir = os.path.abspath(sourcedir)


class CMakeBuild(build_ext):
    def run(self):
        try:
            out = subprocess.check_output(['cmake', '--version'])
        except OSError:
            raise RuntimeError(
                "CMake must be installed to build the following extensions: " +
                ", ".join(e.name for e in self.extensions))

        if self.is_windows():
            cmake_version = LooseVersion(
                re.search(r'version\s*([\d.]+)', out.decode()).group(1))
            if cmake_version < '3.1.0':
                raise RuntimeError("CMake >= 3.1.0 is required on Windows")

        for ext in self.extensions:
            self.build_extension(ext)

    @staticmethod
    def is_windows():
        tag = platform.system().lower()
        return tag == "windows"

    def build_extension(self, ext):
        extdir = os.path.abspath(
            os.path.dirname(self.get_ext_fullpath(ext.name)))

        cfg = 'Production'
        build_args = ['--config', cfg]

        cpu_count = max(2, multiprocessing.cpu_count() // 2)
        build_args += ['--', '-j{0}'.format(cpu_count)]

        project_src_path = get_project_src_path()
        build_dir = os.path.join(project_src_path, WORKING_DIR)

        # configure with the working directory python-build-wheel
        args = ['--python-bindings',
                '--auto-download',
                '--lib-only',
                '--name='+WORKING_DIR]
        # find correct Python include directory and library
        # works even for nonstandard Python installations
        # (e.g., on pypa/manylinux)
        args.append('-DPYTHON_VERSION_STRING:STRING=' + \
                    sys.version.split(' ')[0])
        python_version = CMaker.get_python_version()
        args.append('-DPYTHON_INCLUDE_DIR:PATH=' + \
                    CMaker.get_python_include_dir(python_version))
        args.append('-DPYTHON_LIBRARY:FILEPATH=' + \
                    CMaker.get_python_library(python_version))

        config_filename = os.path.join(project_src_path, "configure.sh")
        subprocess.check_call([config_filename] + args)

        # build the main library
        subprocess.check_call(
            ['cmake', '--build', '.', "--target", "cvc5"] + build_args, cwd=build_dir)

        # build the python binding
        python_build_dir = os.path.join(build_dir, "src", "api", "python")
        subprocess.check_call(["make"], cwd=python_build_dir)
        # the build folder gets cleaned during the config, need to create it again
        # this is necessary since "build" is a python dist folder
        if not os.path.isdir(extdir):
            os.mkdir(extdir)

        # copy the library over. we need to consider other users that are not on linux
        # module is a directory called pycvc5
        pycvc5_module = os.path.join(python_build_dir, "pycvc5")
        dst_name = os.path.join(extdir, "pycvc5")
        if os.path.isdir(dst_name):
            # remove, then replace
            shutil.rmtree(dst_name)

        shutil.copytree(pycvc5_module, dst_name)


setup(
    name='pycvc5',
    version='.'.join(get_cvc5_version()),
    long_description='Python bindings for cvc5',
    url='https://github.com/cvc5/cvc5',
    license='BSD-3-Clause',
    zip_safe=False,
    ext_modules=[CMakeExtension('pycvc5')],
    cmdclass=dict(build_ext=CMakeBuild),
    tests_require=['pytest']
)

