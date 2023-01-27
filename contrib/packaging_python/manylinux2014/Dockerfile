FROM quay.io/pypa/manylinux2014_x86_64
WORKDIR /home/pycvc5
RUN yum -q -y install ccache jre libffi-devel flex
RUN ccache --set-config=cache_dir=/home/pycvc5/ccache-dir

ENV PATH="/usr/lib64/ccache:${PATH}"

RUN ln -s /usr/bin/ccache /usr/lib64/ccache/g++ && \
    ln -s /usr/bin/ccache /usr/lib64/ccache/gcc && \
    ln -s /usr/bin/ccache /usr/lib64/ccache/c++ && \
    ln -s /usr/bin/ccache /usr/lib64/ccache/cc
