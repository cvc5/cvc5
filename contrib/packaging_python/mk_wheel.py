###############################################################################
# Top contributors (to current version):
#   Makai Mann, Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# ############################################################################
#
# Build script for python wheels for cvc5.
# It provides two main functions:
# - get_cvc5_version() uses the version.cmake script to obtain the proper cvc5
#   version string. It is extracted from the versioninfo.cpp file and passed on
#   to the setuptools config.
# - build_extension() builds the cvc5 python api(s) using the cvc5_python_api
#   target and copying it to wherever setuptools expects it to be.
#
# Example usage (from build directory):
#   python3 ../contrib/packaging_python/mk_wheel.py bdist_wheel -d dist
##

import os
import re
import platform
import subprocess
import shutil

from setuptools import setup, Extension
from setuptools.command.build_ext import build_ext
from distutils.version import LooseVersion


def get_project_src_path():
    # expecting this script to be in contrib/packaging_python/
    # The project source directory is two directories up
    name = __file__
    for i in range(3):
        name = os.path.dirname(name)
    name = os.path.abspath(name)
    if not os.path.isfile(os.path.join(name, 'configure.sh')):
        raise RuntimeError('Finding the project source path failed. We guessed ' + name)
    return name


def get_cvc5_version():
    # run the version detection in cmake
    subprocess.check_call([
        'cmake', '-DPROJECT_SOURCE_DIR=' + get_project_src_path(),
        '-DCMAKE_BINARY_DIR=.', '-P',
        get_project_src_path() + '/cmake/version.cmake'
    ])

    # read versioninfo.cpp to get version number
    with open(os.path.join('src', 'base', 'versioninfo.cpp'), 'r') as f:
        m = re.search('CVC5_FULL_VERSION = "([0-9a-z.-]+)"', f.read())
        if m:
            version = m.group(1)
            version = re.sub('-dev\.([0-9]+)\.[0-9a-f]+', '.dev\\1', version)
            return version
        else:
            raise Exception('Could not find version')


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
        # build the python api
        subprocess.check_call(['cmake', '--build', '.', '--target', 'cvc5_python_api'])

        # copy the library over. we need to consider other users that are not on linux
        # module is a directory called cvc5_python_base_module
        extdir = os.path.abspath(
            os.path.dirname(self.get_ext_fullpath(ext.name)))
        cvc5_python_base_module = os.path.join("src", "api", "python", "cvc5")
        dst_name = os.path.join(extdir, "cvc5")

        shutil.rmtree(dst_name, ignore_errors=True)
        shutil.copytree(cvc5_python_base_module, dst_name)


setup(
    name='cvc5',
    version=get_cvc5_version(),
    long_description='Python bindings for cvc5',
    url='https://github.com/cvc5/cvc5',
    license='BSD-3-Clause',
    zip_safe=False,
    ext_modules=[CMakeExtension('cvc5')],
    cmdclass=dict(build_ext=CMakeBuild),
    tests_require=['pytest']
)
