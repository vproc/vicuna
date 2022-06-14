Vicuna - a flexible and scalable RISC-V vector coprocessor
==========================================================

Vicuna is an open-source 32-bit integer vector coprocessor written in SystemVerilog
that implements version 1.0 of the
`RISC-V "V" Vector extension specification <https://github.com/riscv/riscv-v-spec>`__.
More precisely, Vicuna complies with the ``Zve32x`` extension,
a variant of the V extension aimed at embedded processors
that do not require 64-bit elements or floating-point support
(see Sect. 18.2 of the specification for details).
As such, Vicuna supports vector element widths of 8, 16, and 32 bits
and implements all vector load and store, vector integer [#f1]_,
vector fixed-point, vector integer reduction, vector mask, and vector permutation instructions.

Vicuna is a coprocessor and thus requires a main processor to function.
It uses the `OpenHW Group's CORE-V eXtension Interface (CORE-V-XIF)
<https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/>`__
as interface to the main core.
Currently, the `CV32E40X core <https://github.com/openhwgroup/cv32e40x>`__
or a modified version of the `Ibex core <https://github.com/lowRISC/ibex>`__
serves as the main core.

Vicuna is extensively configurable.
For instance, the width of the vector registers,
the number and layout of its execution pipelines
and the width of its memory interface are configurable.
The following figure gives a high-level overview of Vicuna.

.. image:: fig/vproc_overview.svg

Each of Vicuna's vector pipelines can host one or multiple vector execution units.
Vicuna currently offers the following units:

* **VLSU:** The vector load and store unit,
  responsible for loading and storing memory data to and from vector registers.
* **VALU:** The vector arithmetic and logic unit executes most vector arithmetic
  and vector mask instructions.
* **VMUL:** The vector multiplier implements the vector multiplication instructions.
* **VSLD:** The vector slide unit takes care of the vector slide instructions.
* **VELEM:** The vector element unit uses element-wise processing
  to implement several vector permutation, many vector mask,
  and the vector reduction instructions.
  It is also the only unit capable of writing back data
  to the general-purpose registers in the main core.


Vector Processing
-----------------

If you are not yet familiar with vector processing
and would like to first understand the advantages it offers and how it can be used,
you might want to read some of these posts:

* `Erik Engheim's comparison of vector processing on CPUs and GPUs
  <https://itnext.io/vector-processing-on-cpus-and-gpus-compared-b1fab24343e6>`__
  to understand what vector processing is,
  which approaches there are,
  and how it compares to other parallel processing concepts.

* to understand how RISC-V vector instructions can currently be used
  to speed-up you data-parallel workloads.


Getting Started
---------------

Clone `Vicuna's repository <https://github.com/vproc/vicuna>`__,
as well as the repository's submodules, with the following commands:

.. code-block:: sh

   git clone https://github.com/vproc/vicuna.git
   cd vicuna
   git submodule update --init --recursive

Then, follow the instructions in :doc:`the user guide <01_user/index>`
to get started with using Vicuna.

.. toctree::
   :maxdepth: 2
   :hidden:

   01_user/index.rst


.. rubric:: Footnotes

.. [#f1] Currently, the vector integer divide instructions
   (i.e., ``vdiv``, ``vdivu``, ``vrem``, and ``vremu``) are still missing.
