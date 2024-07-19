FROM arm64v8/ubuntu:20.04

ARG OTHER_OPTS
ARG DEBIAN_FRONTEND=noninteractive
ARG JAVA_TOOL_OPTIONS=-Dfile.encoding=UTF8

RUN apt-get update && apt-get install -y \
  automake \
  cmake \
  g++ \
  libtool \
  openjdk-11-jdk \
  python3 \
  python3-pip \
  python3-venv \
  && rm -rf /var/lib/apt/lists/*

COPY . /cvc5
WORKDIR /cvc5

RUN ./configure.sh --auto-download --prefix=./install \
    -DJAVA_HOME=/usr/lib/jvm/java-11-openjdk-arm64 \
    --gpl --cln --cocoa --glpk ${OTHER_OPTS}
WORKDIR /cvc5/build

RUN make -j`nproc`
RUN make install

WORKDIR /cvc5

RUN cp COPYING ./install/ && \
    cp -r licenses ./install/
