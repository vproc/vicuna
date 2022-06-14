#!/bin/sh

sudo apt-get update
sudo apt-get install srecord llvm-14 clang-14
sudo ln -sf /usr/bin/llvm-objdump-14 /usr/bin/llvm-objdump
sudo ln -sf /usr/bin/llvm-objcopy-14 /usr/bin/llvm-objcopy
sudo apt-get install git perl python3 g++ flex bison ccache libfl2 libfl-dev zlib1g zlib1g-dev
git clone https://github.com/verilator/verilator
unset VERILATOR_ROOT
cd verilator
git checkout tags/v4.210
autoconf
./configure --prefix /opt/verilator
make
sudo make install
echo 'export PATH=/opt/verilator/bin:$PATH' | sudo tee -a /etc/profile
