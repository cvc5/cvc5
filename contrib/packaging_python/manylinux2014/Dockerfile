FROM quay.io/pypa/manylinux2014_x86_64
WORKDIR /home/pycvc5
RUN yum -y install ccache jre libffi-devel
RUN ccache --set-config=cache_dir=/home/pycvc5/ccache-dir

ENV PATH="/usr/lib64/ccache:${PATH}"
ENV CMAKE_CXX_COMPILER_LAUNCHER=/usr/bin/ccache
ENV CMAKE_C_COMPILER_LAUNCHER=/usr/bin/ccache
