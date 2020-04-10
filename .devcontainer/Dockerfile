FROM trzeci/emscripten:sdk-incoming-64bit
LABEL description="A dev container for developing the Lean 3 compiler with."
# Avoid warnings by switching to noninteractive
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update
RUN apt-get -y install --no-install-recommends apt-utils dialog 2>&1
RUN apt-get install -y git iproute2 procps lsb-release build-essential cmake cppcheck valgrind ninja-build libgmp-dev gdb
RUN apt-get install -y m4

ENV NODE_OPTIONS="--max-old-space-size=4096"

# install Emscripten build tools

# # RUN apt-get install python2.7 cmake default-jre
# WORKDIR /
# RUN git clone --depth=1 https://github.com/emscripten-core/emsdk.git
# WORKDIR /emsdk
# RUN ./emsdk install latest
# RUN ./emsdk activate latest

# #[HACK] this seems to be what `source /emsdk/emsdk_env.sh` does.
# ENV PATH $PATH:/emsdk:/emsdk/upstream/emscripten:/emsdk/node/12.9.1_64bit/bin/node
# ENV EMSDK /emsdk
# ENV EM_CONFIG /root/.emscripten
# ENV EMSDK_NODE /emsdk/node/12.9.1_64bit/bin/node
