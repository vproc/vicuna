Configuration
=============

Vicuna is heavily parametrizable,
which allows users to customize it for their specific needs.
This section explains the various configuration options
and attempts to guide users in choosing the right parameter values for their intended application.


TL;DR
-----

Take a moment to think about your answer to the following two questions:

* What is your target technology?

* What is your performance vs area/resource utilization trade-off?

Now, have a look at the table below
and identify the cell that best fits your desired performance goals and target technology.

+----------------------+------------------------+------------------------+------------------------+
|                      |                            Target Technology                             |
+ Performance tradeoff +------------------------+------------------------+------------------------+
|                      |          FPGA          |          ASIC          | I don't care, I just   |
|                      |                        |                        | want to simulate it.   |
+======================+========================+========================+========================+
| I need it to be as   |``VPROC_CONFIG=compact``|``VPROC_CONFIG=compact``|``VPROC_CONFIG=compact``|
| small and compact    |``VREG_W=64``           |``VREG_W=64``           |``VREG_W=64``           |
| as possible.         |``VPORT_POLICY=some``   |``VPORT_POLICY=many``   |                        |
|                      |``TARGET_TECH=fgpa``    |``TARGET_TECH=asic``    |                        |
+----------------------+------------------------+------------------------+------------------------+
| I need reasonable    |``VPROC_CONFIG=dual``   |``VPROC_CONFIG=dual``   |``VPROC_CONFIG=dual``   |
| performance without  |``VREG_W=512``          |``VREG_W=256``          |``VREG_W=512``          |
| wasting to much      |``VPORT_POLICY=few``    |``VPORT_POLICY=many``   |                        |
| area / resources.    |``TARGET_TECH=fpga``    |``TARGET_TECH=asic``    |                        |
+----------------------+------------------------+------------------------+------------------------+
| I have plenty of     |``VPROC_CONFIG=triple`` |``VPROC_CONFIG=triple`` |``VPROC_CONFIG=triple`` |
| area / resources to  |``VREG_W=4096``         |``VREG_W=1024``         |``VREG_W=2048``         |
| spare and need       |``VMEM_W=512``          |``VMEM_W=512``          |                        |
| maximum performance. |``VPORT_POLICY=some``   |``VPORT_POLICY=many``   |                        |
|                      |``TARGET_TECH=fgpa``    |``TARGET_TECH=asic``    |                        |
+----------------------+------------------------+------------------------+------------------------+


.. note::
   Vicuna is currently optimized for use on FPGAs.
   Even when selecting ``TARGET_TECH=asic``
   the generated RTL is still far from optimal for an ASIC.
   However, there is work in progress to improve that.

Remember the values in the cell that you selected
and move on to :doc:`simulation` if you first want to simulate some vector programs on Vicuna,
to :doc:`synthesis` if you prefer using Vicuna on an FPGA right away,
or to :doc:`integration` if you want to integrate Vicuna into a custom SoC.


What is actually configurable?
------------------------------

Vicuna has a lot of parameters that allow for extensive configuration.
Besides basic properties, such as the width of the vector registers,
several parameters configure the number and layout of the vector pipelines.
Vicuna can use an arbitrary number of vector pipelines
with each pipeline containing one or multiple vector execution units.
The vector pipelines operate in parallel,
allowing multiple vector instruction to be executed concurrently.

A configuration Makefile (:file:`config.mk`)
is used to generate the concrete values for the configuration parameters
based on a high-level description of the desired vector pipeline configuration.
This Makefile is included by the various other Makefiles used during simulation or synthesis
and does not need to be invoked directly.
Several environment variables are available to control the configuration of Vicuna.

The easiest way to select a certain pipeline layout
is to set the environment variable ``VPROC_CONFIG`` to one of the following values:

* ``compact``: Selects a layout with a single vector pipeline containing all execution units.
* ``dual``: Selects a layout with two pipelines,
  one containing the VLSU, VALU, and VMEM, and the other the VMUL and VSLD units.
* ``triple``: Selects a layout with three pipelines,
  with the VLSU in a dedicated pipeline, the VALU and VELEM in a second,
  and the VMUL and VSLD units in a third pipeline.
* ``legacy``: Selects the old configuration of Vicuna where each unit has its own vector pipeline.

In addition, the environment variables ``VREG_W`` and ``VMEM_W``
select the bit widths of the vector registers and Vicuna's memory interface, respectively.
Selecting a dual pipeline layout with 128-bit vector registers and a 32-bit memory interface
is accomplished with the following settings:

.. code-block:: sh

   VPROC_CONFIG=dual VREG_W=128 VMEM_W=32

Three different policies allow to control
how many vector register read ports each vector pipeline should get.
For that purpose,
the environment variable ``VPORT_POLICY`` may be set to one of the following values:

* ``few``: Use as few read ports per pipeline as possible (defaults to one read port per pipeline).
* ``some``: Use some read ports depending on the requirements of the pipeline's units
  (defaults to using one read port per pipeline, or two if it contains the VMUL unit).
* ``many``: Use many read ports (defaults to one read port for each operand).

The vector pipelines typically use multiplexing on the vector register read ports
to read multiple operands from a single port.
Therefore, each pipeline may use fewer read ports than operands.
However, if using fewer read ports the operands that have already been fetched must be buffered
while waiting for the remaining ones, consuming flip-flops for that purpose.
In addition, the available number of vector register read ports
limits the maximum throughput of the pipeline.

If more fine-tuning is desired,
the environment variable ``VPROC_PIPELINES`` can be used
to precisely define the layout of each vector pipeline.
It accepts a sequence of whitespace-separated descriptions of each pipeline,
with each pipeline described by a string of the form ``WIDTH:UNIT[,UNIT]*``,
where ``WIDTH`` is the bit width of the pipeline's operands
and ``UNIT[,UNIT]*`` a list of one or multiple comma-separated execution unit names.
For instance, a dual pipeline layout
with 32-bit wide vector operands hosting the VLSU, the VALU, and the VELEM units
and 64-bit wide vector operands hosting the VMUL and VSLD units is selected as follows:

.. code-block:: sh

   VPROC_PIPELINES="32:VLSU,VALU,VELEM 64:VMUL,VSLD"

In addition to defining the vector execution units that shall be contained in each pipeline,
this approach allows to specify the width of the vector operands for each pipeline.
The vector operands are consecutive portions of the vector registers
that are fed to the vector execution units.
Their width determines the amount of vector elements
that can be processed each clock cycle by the respective pipeline.
A pipeline with wider operands has a higher throughput than a pipeline with narrow operands.
This allows to increase the performance
of individual vector execution units that are used frequently
by moving these to a wider pipeline,
while saving resources on other execution units which are placed in a narrow pipeline.

Note that the operand width of a pipeline must be a power of two, at least 32,
and less than or equal to the width of the vector registers.
Also, the operand width of the pipeline containing the VLSU
must equal the width of the memory interface (``VMEM_W``).

The :file:`config.mk` computes the parameter values
for the SystemVerilog parameters of Vicuna's core module ``vproc_core``
that correspond to the selected configuration.
These parameter values are written
to a dynamically generated SystemVerilog package named ``vproc_config``
and are then used as default values for the ``vproc_core`` module's parameters.

While the intent of the ``vproc_config`` package is to provide consistent default parameter values
derived from a high-level description of the desired configuration,
they can be overridden when instantiating the ``vproc_core`` module.
The :doc:`integration` section has a complete list of all configuration parameters
that can be overridden when instantiating Vicuna's core module in a custom design.
