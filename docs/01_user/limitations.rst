Limitations and Pitfalls
========================

As for most parallel architectures,
the performance of vector processors is usually not limited by the computational performance
but rather by the available memory bandwidth for most applications.
Before attempting to optimize code for Vicuna,
programmers should consider the performance ceilings
resulting from the available throughput of the vector execution pipelines
and the bandwidth of the memory interface.

The `roofline model <https://en.wikipedia.org/wiki/Roofline_model>`__
is a useful tool to assess the performance limit of an application based on its
`arithmetic intensity <https://en.wikipedia.org/wiki/Roofline_model#Arithmetic_intensity>`__.
The roofline model can also be used to understand which of Vicuna's configuration options
can potentially improve the performance of an application.
For instance, if the arithmetic intensity of a program puts it in the memory-bound region
of a certain configuration of Vicuna,
then increasing the computational throughput alone will not improve its performance,
since the memory interface is already the bottleneck
and performance can only be improved by increasing the memory bandwidth.


Scheduling model
----------------

Vector instructions are typically long-latency instructions,
since operations on vector registers are not processed instantaneously,
but are instead carried out across multiple clock cycles.
Combined with the fact that Vicuna is an in-order vector core,
this means that a clever arrangement of vector instructions
can substantially reduce the amount of time the core is stalled
due to data-dependencies between instructions.

Modern compilation toolchains re-arrange instructions in order to avoid such stalls,
which is referred to as instruction scheduling.
In order for instruction scheduling to be effective,
the compiler needs a model of the processing hardware
that can be used to decide which arrangement of instructions will have the best performance.
Such a model is called a scheduling model.

The latency of vector instructions executed on Vicuna
varies greatly depending on the chosen configuration.
Therefore, a scheduling model for Vicuna must be adapted for each configuration.
Future versions of the :file:`config.mk` Makefile
will produce a scheduling model for use with LLVM compiler
in addition to the configuration package that sets the values for the configuration parameters.


Inefficient vector instructions
-------------------------------

Vicuna complies with the embedded profile ``Zve32x``
of `the RISC-V Vector extension specification <https://github.com/riscv/riscv-v-spec>`__,
which supports elements widths of 8, 16, and 32 bits,
and comprises all vector load and store,
vector integer (currently the division and remainder instructions are still missing),
vector fixed-point, vector integer reduction, vector mask,
and vector permutation instructions.
However, while all these instructions are available,
certain instructions operate more efficiently than others.
In order to write efficient vector code for Vicuna,
programmers should try to avoid inefficient instructions,
preferably substituting them
with alternative instruction sequences with better performance
whenever possible.

A number of vector instructions are only processing one vector element per cycle
because a more performant implementation would require extensive resources
or would be overly complicated.
This section lists these instructions
and suggests some possible alternatives.


Inefficient vector loads and stores
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Most vector load and store instructions
only load or store one vector element per memory transaction.
In particular, the strided and indexed vector loads and stores,
as well as all vector load/store segment instructions
(i.e., vector loads and stores with more than one field),
always generate a separate transaction for each element.

Vector unit-stride loads and stores can take advantage of the full width of the memory interface
to load or store as many elements as possible per transaction
if the base address is aligned to the width of the memory interface.
If the base address is not suitably aligned,
then unit-strided loads and stores are handled
like a general strided load or store (with a stride of 1)
and thus also require one transaction per element.

Similarly, the vector load/store whole register instructions
perform efficiently when the base address is aligned to the width of the memory interface
and much less efficiently otherwise.

Therefore, arrays that shall be accessed by vector load and store instructions
should always be aligned to the width of the memory interface.
For instance, if the memory interface is 64 bits (i.e., 8 bytes) wide,
then a suitably aligned C array can be declared as follows:

.. code-block:: c

   int8_t array[1024] __attribute__ ((aligned (8)));

Unit-strided loads and stores should always be preferred.
If data that shall be loaded into a vector register is not stored contiguously
but rather with a small stride (e.g., 8-bit data with a stride of 4 bytes),
then a unit-strided load followed by narrowing shift instructions
can be used as a substitute for the less efficient strided load instruction.

.. literalinclude:: ../code/opt_vlse.c
   :language: c
   :start-at: (


Inefficient vector reduction instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Currently, all vector reduction instructions
perform the reduction one element at a time.

For large vectors,
a more efficient approach is to split the vector into its upper and lower halves
and combine these two halves by applying the reduction operation.
This step is then repeated for the resulting vector
(which has half the size of the original vector),
until the vector is short enough to use the actual reduction instruction.
The C code below shows an efficient implementation
of an 8-bit sum reduction using this technique to shorten the vector to less than 8 elements
before using the actual reduction instruction:

.. literalinclude:: ../code/opt_reduction.c
   :language: c
   :start-at: (


Inefficient vector permutation instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The following vector permutation instructions
only process one element per cycle:

* The general vector permutation ``vrgather`` (as well as ``vrgatherei16``)
* The vector compress instruction ``vcompress``

Whenever possible,
code should use the much more efficient vector slide instructions instead.
Most static permutation patterns can be replaced by a short series of masked slide instructions.
For instance,
the 16-element permutation performed during the `ShiftRows step of AES encryption
<https://en.wikipedia.org/wiki/Advanced_Encryption_Standard#The_ShiftRows_step>`_
can be implemented using the following series of vector slide instructions:

.. literalinclude:: ../code/opt_shiftrows.c
   :language: c
   :start-at: (

When searching for efficient implementations for permutation patterns,
inspiration can be found in code generators for bit permutations,
such as the one on `programming.sirrida.de <https://programming.sirrida.de/calcperm.php>`__.
Finding efficient patterns for vector element permutations using vector slide operations
is analog to finding patterns for bit permutations using shift operations
and for the latter many online resources are available.
