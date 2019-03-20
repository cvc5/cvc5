from distutils.core import setup

from Cython.Build import cythonize

setup(ext_modules=cythonize("pycvc4.pyx"))
