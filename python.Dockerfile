FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
  cmake \
  python3-pip \
  python-is-python3 \
  m4 \
  && rm -rf /var/lib/apt/lists/*

RUN mkdir -p ~/.config/pip/ && \
  echo "[global]" >> ~/.config/pip/pip.conf && \
  echo "break-system-packages = true" >> ~/.config/pip/pip.conf

COPY . /cvc5
WORKDIR /cvc5

RUN ./configure.sh --auto-download --no-pyvenv --python-bindings --poly --cocoa
WORKDIR /cvc5/build
RUN make -j`nproc` cvc5_python_api
ENV PYTHONPATH="/cvc5/build/src/api/python/"

WORKDIR /
ENTRYPOINT ["/usr/bin/python"]
