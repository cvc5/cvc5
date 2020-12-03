#!/bin/bash
# Install dependencies GitHub actions in the ubuntu flavor

sudo apt-get update
sudo apt-get install -y \
     build-essential \
     ccache \
     cxxtest \
     libcln-dev \
     libgmp-dev \
     libgtest-dev \
     libedit-dev \
     flex \
     libfl-dev \
     flexc++
