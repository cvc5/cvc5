FROM quay.io/pypa/manylinux2014_x86_64
WORKDIR /home/pycvc5
RUN yum -q -y install ccache jre libffi-devel gmp-devel
RUN ccache --set-config=cache_dir=/home/pycvc5/ccache-dir

ENV PATH="/usr/lib64/ccache:${PATH}" \
    CMAKE_CXX_COMPILER_LAUNCHER=/usr/bin/ccache \
    CMAKE_C_COMPILER_LAUNCHER=/usr/bin/ccache
