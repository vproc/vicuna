# Simulation directory

The files in this directory allow to simulate the vector processor.  Simulation
is done with the help of `make`.   The environment variable `PROG_PATHS_LIST`
can be used to specify a series of programs that should be executed on the
simulated vector processor.  Such a list of programs can be a simple text file
with each line containing the file path of a `*.vmem` file specifying the
memory initialization file of the respective programs.

The default simulator is [Verilator](https://www.veripool.org/verilator/).
Note that version 4.210 or newer is required.  In case your distribution only
offers older versions, you need to compile Verilator from source by executing
the following instructions (the last two lines are optional, you may as well
run Verilator from its build directory):
```
git clone https://github.com/verilator/verilator
unset VERILATOR_ROOT
cd verilator
git checkout tags/v4.210
autoconf
./configure --prefix /opt/verilator
make
sudo make install
echo 'export PATH=/opt/verilator/bin:$PATH' | sudo tee -a /etc/profile
```

The environment variables `VREG_W` and `VMEM_W` can be used to specify the bit
width of the vector registers and the memory interface of the vector core,
respectively.
