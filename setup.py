from skbuild import setup

setup(
    name="pycvc4",
    version="1.9.0",
    license="BSD",
    packages=['pycvc4'],
    package_dir={
        'pycvc4': 'src/api/pycvc4'},
    cmake_args=['-DBUILD_BINDINGS_PYTHON=ON', '-DENABLE_SHARED=OFF', '-DBUILD_LIB_ONLY=ON']
)
