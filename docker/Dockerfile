FROM ubuntu:18.04
WORKDIR /home/tacas2020

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get install -y python3-pip libpcre* wget unzip build-essential python3 automake libgmp-dev curl nano python3-dev libboost-dev default-jdk libclang-dev llvm llvm-dev lbzip2 libncurses5-dev git libtool iverilog libmpfr-dev libmpc-dev cmake clang libreadline-dev tcl-dev libffi-dev bison flex pkg-config
# zlib1g-dev

RUN python3 -m pip install cython jupyterlab numpy pandas

RUN git clone https://github.com/pysmt/pysmt
RUN cd pysmt && git checkout -f 09dc303185812149550110123ad266326beb1179 && python3 -m pip install -e .

RUN git clone -b smtcomp19 https://github.com/Boolector/boolector
# branch was force pushed and lost that commit hash -- using a different one from paper
RUN cd boolector && git checkout -f 98aeefd27d0ce1188707dda013c1c63a00be7b4c && ./contrib/setup-btor2tools.sh && ./contrib/setup-cadical.sh && ./configure.sh --python --py3 && cd build && make -j2 && make install
ENV PYTHONPATH="/home/tacas2020/boolector/build/lib/:${PYTHONPATH}"

RUN git clone https://github.com/cristian-mattarei/CoSA
RUN cd CoSA && git checkout -f ff3c8cee1f0834c03167b2a8ecdd1223031312b3 && python3 -m pip install -e .
# The first time a new install of CoSA is run, PySMT compiles a Cython parser -- run it now to get this over with
RUN CoSA --help

RUN git clone https://github.com/YosysHQ/yosys
RUN cd yosys && git checkout -f a4b59de5d48a89ba5e1b46eb44877a91ceb6fa44 && make -j8 && make install

RUN git clone https://github.com/makaimann/tacas2020-exps
# Need to apply a simple one-line patch to pysmt for it to run this branch of boolector
RUN cd pysmt && git apply ../tacas2020-exps/pysmt.patch