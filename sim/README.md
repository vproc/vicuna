# Simulation directory

The files in this directory allow to simulate the vector processor.  Simulation
is done with the help of `make`.   The environment variable `PROG_PATHS_LIST`
can be used to specify a series of programs that should be executed on the
simulated vector processor.  Such a list of programs can be a simple text file
with each line containing the file path of a `*.vmem` file specifying the
memory initialization file of the respective programs.

The environment variables `VREG_W` and `VMEM_W` can be used to specify the bit
width of the vector registers and the memory interface of the vector core,
respectively.
