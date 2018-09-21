FROM ubuntu:14.04
MAINTAINER Mate Soos
# RUN apt-get update && apt-get install -y libboost-program-options1.54.0 libstdc++6 && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*
RUN apt-get install libboost-program-options1.54.0
ADD cryptominisat4 /home/cryptominisat4
ADD libcryptominisat4* /home/
ADD libm4ri-* /home/
WORKDIR /home
CMD ["./cryptominisat4"]
