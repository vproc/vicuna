Core Integration
================

There are two ways to integrate Vicuna into a custom RTL design:

* Integrate the vector coprocessor only by instantiating the ``vproc_core`` module.

* Integrate the vector coprocessor together with a main core
  and optional instruction and data caches
  by instantiating the ``vproc_top`` module.


Integrate Vicuna alone
----------------------

Instantiate the ``vproc_core`` module using the following instantiation template:

.. code-block:: systemverilog

   vproc_core #(
       .XIF_ID_W           (                    ),
       .XIF_MEM_W          (                    ),
       .DONT_CARE_ZERO     (                    ),
       .ASYNC_RESET        (                    )
   ) v_core (
       .clk_i              (                    ),
       .rst_ni             (                    ),

       .xif_issue_if       (                    ),
       .xif_commit_if      (                    ),
       .xif_mem_if         (                    ),
       .xif_memres_if      (                    ),
       .xif_result_if      (                    ),

       .pending_load_o     (                    ),
       .pending_store_o    (                    ),

       .csr_vtype_o        (                    ),
       .csr_vl_o           (                    ),
       .csr_vlenb_o        (                    ),
       .csr_vstart_o       (                    ),
       .csr_vstart_i       (                    ),
       .csr_vstart_set_i   (                    ),
       .csr_vxrm_o         (                    ),
       .csr_vxrm_i         (                    ),
       .csr_vxrm_set_i     (                    ),
       .csr_vxsat_o        (                    ),
       .csr_vxsat_i        (                    ),
       .csr_vxsat_set_i    (                    ),

       .pend_vreg_wr_map_o (                    )
   );


.. _core_parameters:

Parameters that should be set when instantiating the ``vproc_core`` module
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Mandatory parameters related to XIF interface
(must be specified, default values cause compilation errors):

+-------------------+--------------------------------+--------------------------------------------+
| Name              | Type                           | Description                                |
+===================+================================+============================================+
|``XIF_ID_W``       |``int unsigned``                | Width of XIF instruction IDs (bits)        |
+-------------------+--------------------------------+--------------------------------------------+
|``XIF_MEM_W``      |``int unsigned``                | Width of XIF memory interface (bits)       |
+-------------------+--------------------------------+--------------------------------------------+

Don't care policy and reset properties
(default values as indicated):

+-------------------+-------+--------+------------------------------------------------------------+
| Name              | Type  | Default| Description                                                |
+===================+=======+========+============================================================+
|``DONT_CARE_ZERO`` |``bit``|``1'b0``| If set, use ``'0`` for don't care values rather than ``'x``|
+-------------------+-------+--------+------------------------------------------------------------+
|``ASYNC_RESET``    |``bit``|``1'b0``| Set if ``rst_ni`` is asynchronous instead of synchronous   |
+-------------------+-------+--------+------------------------------------------------------------+


.. _core_parameters_config:

Parameters that should be **not be overridden** when instantiating the ``vproc_core`` module
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Vector register file configuration
(default values taken from configuration package ``vproc_config``):

+-------------------+--------------------------------+--------------------------------------------+
| Name              | Type                           | Description                                |
+===================+================================+============================================+
|``VREG_TYPE``      |``vproc_pkg::vreg_type``        | Vector register file type                  |
+-------------------+--------------------------------+--------------------------------------------+
|``VREG_W``         |``int unsigned``                | Width of the vector registers (bits)       |
+-------------------+--------------------------------+--------------------------------------------+
|``VPORT_RD_CNT``   |``int unsigned``                | Number of vector register read ports       |
+-------------------+--------------------------------+--------------------------------------------+
|``VPORT_RD_W``     |``int unsigned [VPORT_RD_CNT]`` | Width of each of the vector register read  |
|                   |                                | ports (bits, currently all read ports must |
|                   |                                | be ``VREG_W`` bits wide)                   |
+-------------------+--------------------------------+--------------------------------------------+
|``VPORT_WR_CNT``   |``int unsigned``                | Number of vector register write ports      |
+-------------------+--------------------------------+--------------------------------------------+
|``VPORT_WR_W``     |``int unsigned [VPORT_WR_CNT]`` | Width of each of the vector register write |
|                   |                                | ports (bits, currently all write ports     |
|                   |                                | must be ``VREG_W`` bits wide)              |
+-------------------+--------------------------------+--------------------------------------------+

.. note::
   These parameters should normally not be overridden when instantiating the ``vproc_core`` module.
   Instead, a ``vproc_config`` package that provides defaults for these parameters
   should be generated as explained in :doc:`configuration`.

Vector pipeline configuration
(default values taken from configuration package ``vproc_config``):

+-------------------+---------------------------------+-------------------------------------------+
| Name              | Type                            | Description                               |
+===================+=================================+===========================================+
|``PIPE_CNT``       |``int unsigned``                 | Number of vector execution pipelines      |
+-------------------+---------------------------------+-------------------------------------------+
|``PIPE_UNITS``     |``bit [UNIT_CNT-1:0] [PIPE_CNT]``| Vector execution units contained in each  |
|                   |                                 | vector pipeline (for each pipeline the    |
|                   |                                 | bit mask indicates the units it contains) |
+-------------------+---------------------------------+-------------------------------------------+
|``PIPE_W``         |``int unsigned       [PIPE_CNT]``| Operand width of each pipeline (bits)     |
+-------------------+---------------------------------+-------------------------------------------+
|``PIPE_VPORT_CNT`` |``int unsigned       [PIPE_CNT]``| Number of vector register read ports of   |
|                   |                                 | each pipeline                             |
+-------------------+---------------------------------+-------------------------------------------+
|``PIPE_VPORT_IDX`` |``int unsigned       [PIPE_CNT]``| Index of the first vector register read   |
|                   |                                 | port associated with each pipeline        |
+-------------------+---------------------------------+-------------------------------------------+
|``PIPE_VPORT_WR``  |``int unsigned       [PIPE_CNT]``| Index of the vector register write port   |
|                   |                                 | used by each pipeline                     |
+-------------------+---------------------------------+-------------------------------------------+

.. note::
   These parameters should normally not be overridden when instantiating the ``vproc_core`` module.
   Instead, a ``vproc_config`` package that provides defaults for these parameters
   should be generated as explained in :doc:`configuration`.

Unit-specific configuration
(default values taken from configuration package ``vproc_config``):

+-------------------+-------------------------------------+---------------------------------------+
| Name              | Type                                | Description                           |
+===================+=====================================+=======================================+
|``VLSU_QUEUE_SZ``  |``int unsigned``                     | Size of the VLSU's transaction queue  |
|                   |                                     | (limits the number of outstanding     |
|                   |                                     | memory transactions)                  |
+-------------------+-------------------------------------+---------------------------------------+
|``VLSU_FLAGS``     |``bit [vproc_pkg::VLSU_FLAGS_W-1:0]``| Flags for the VLSU's properties       |
+-------------------+-------------------------------------+---------------------------------------+
|``MUL_TYPE``       |``vproc_pkg::mul_type``              | Vector multiplier type                |
+-------------------+-------------------------------------+---------------------------------------+

.. note::
   These parameters should normally not be overridden when instantiating the ``vproc_core`` module.
   Instead, a ``vproc_config`` package that provides defaults for these parameters
   should be generated as explained in :doc:`configuration`.

Miscellaneous configuration
(default values taken from configuration package ``vproc_config``):

+-------------------+------------------------------------+----------------------------------------+
| Name              | Type                               | Description                            |
+===================+====================================+========================================+
|``INSTR_QUEUE_SZ`` |``int unsigned``                    | Size of Vicuna's instruction queue     |
|                   |                                    | (when full, offloading of instructions |
|                   |                                    | is stalled until the first instruction |
|                   |                                    | in the queue can be dispatched)        |
+-------------------+------------------------------------+----------------------------------------+
|``BUF_FLAGS``      |``bit [vproc_pkg::BUF_FLAGS_W-1:0]``| Flags for various optional buffering   |
|                   |                                    | stages (including within the vector    |
|                   |                                    | pipelines)                             |
+-------------------+------------------------------------+----------------------------------------+

.. note::
   These parameters should normally not be overridden when instantiating the ``vproc_core`` module.
   Instead, a ``vproc_config`` package that provides defaults for these parameters
   should be generated as explained in :doc:`configuration`.


.. _core_ports:

Ports
^^^^^

+----------------------+-------+---------+--------------------------------------------------------+
| Name                 | Width |Direction| Description                                            |
+======================+=======+=========+========================================================+
|``clk_i``             | 1     | input   | Clock signal                                           |
+----------------------+-------+---------+--------------------------------------------------------+
|``rst_ni``            | 1     | input   | Active low reset (see parameter ``ASYNC_RESET``)       |
+----------------------+-------+---------+--------------------------------------------------------+
|``xif_issue_if``      | `XIF issue interface`_                                                   |
+----------------------+-------+---------+--------------------------------------------------------+
|``xif_commit_if``     | `XIF commit interface`_                                                  |
+----------------------+-------+---------+--------------------------------------------------------+
|``xif_mem_if``        | `XIF memory request/response interface`_                                 |
+----------------------+-------+---------+--------------------------------------------------------+
|``xif_memres_if``     | `XIF memory result interface`_                                           |
+----------------------+-------+---------+--------------------------------------------------------+
|``xif_result_if``     | `XIF result interface`_                                                  |
+----------------------+-------+---------+--------------------------------------------------------+
|``pending_load_o``    | 1     | output  | Indicates that there is a pending vector load          |
+----------------------+-------+---------+--------------------------------------------------------+
|``pending_store_o``   | 1     | output  | Indicates that there is a pending vector store         |
+----------------------+-------+---------+--------------------------------------------------------+
|``csr_vtype_o``       | 32    | output  | *Deprecated* Content of the ``vtype`` CSR              |
+----------------------+-------+---------+--------------------------------------------------------+
|``csr_vl_o``          | 32    | output  | *Deprecated* Content of the ``vl`` CSR                 |
+----------------------+-------+---------+--------------------------------------------------------+
|``csr_vlenb_o``       | 32    | output  | *Deprecated* Content of the ``vlenb`` CSR              |
+----------------------+-------+---------+--------------------------------------------------------+
|``csr_vstart_o``      | 32    | output  | *Deprecated* Content of the ``vstart`` CSR             |
+----------------------+-------+---------+--------------------------------------------------------+
|``csr_vstart_i``      | 32    | input   | *Deprecated* Data for setting the ``vstart`` CSR       |
+----------------------+-------+---------+--------------------------------------------------------+
|``csr_vstart_set_i``  | 1     | input   | *Deprecated* Write enable setting the ``vstart`` CSR   |
+----------------------+-------+---------+--------------------------------------------------------+
|``csr_vxrm_o``        | 2     | output  | *Deprecated* Content of the ``vxrm`` CSR               |
+----------------------+-------+---------+--------------------------------------------------------+
|``csr_vxrm_i``        | 2     | input   | *Deprecated* Data for setting the ``vxrm`` CSR         |
+----------------------+-------+---------+--------------------------------------------------------+
|``csr_vxrm_set_i``    | 1     | input   | *Deprecated* Write enable setting the ``vxrm`` CSR     |
+----------------------+-------+---------+--------------------------------------------------------+
|``csr_vxsat_o``       | 1     | output  | *Deprecated* Content of the ``vxsat`` CSR              |
+----------------------+-------+---------+--------------------------------------------------------+
|``csr_vxsat_i``       | 1     | input   | *Deprecated* Data for setting the ``vxsat`` CSR        |
+----------------------+-------+---------+--------------------------------------------------------+
|``csr_vxsat_set_i``   | 1     | input   | *Deprecated* Write enable setting the ``vxrm`` CSR     |
+----------------------+-------+---------+--------------------------------------------------------+
|``pend_vreg_wr_map_o``| 32    | output  | *Debug* Map of pending vector register writes          |
+----------------------+-------+---------+--------------------------------------------------------+

.. _XIF issue interface: https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/en/latest/x_ext.html#issue-interface
.. _XIF commit interface: https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/en/latest/x_ext.html#commit-interface
.. _XIF memory request/response interface: https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/en/latest/x_ext.html#memory-request-response-interface
.. _XIF memory result interface: https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/en/latest/x_ext.html#memory-result-interface
.. _XIF result interface: https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/en/latest/x_ext.html#result-interface

The ``clk_i`` and ``rst_ni`` ports are the clock and active-low reset inputs, respectively.
The reset may be either synchronous (the default) or asynchronous.
When using an asynchronous reset the parameter ``ASYNC_RESET`` must be set to ``1'b1``.

Vicuna uses the `OpenHW Group's eXtension interface (CORE-V-XIF)
<https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/en/latest/x_ext.html>`__
as interface to a main core, as well as to the memory system.
The ``xif_*`` ports correspond to `the individual interfaces of the CORE-V-XIF
<https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/en/latest/x_ext.html#interfaces>`__.
These are implemented as ports of a SystemVerilog interface
(see Sect. 25 of `IEEE Std 1800-2017 <https://standards.ieee.org/ieee/1800/6700/>`__)
defined in ``vproc_xif.sv``.

The CORE-V-XIF allows to route a coprocessor's memory requests through the main core,
which performs the actual requests on behalf of the coprocessor.
That way memory protection rules, such as PMA checks,
that are typically handled within the LSU of the main core,
can be enforced for memory requests originating from a coprocessor.
However, connecting Vicuna's memory interface to the main core is optional.
Instead, a memory arbiter could directly read Vicuna's memory requests
from the ports of Vicuna's CORE-V-XIF memory interface
and provide memory results via the corresponding ports, thus bypassing the main core.

If Vicuna's  ports are directly hooked up to a memory arbiter,
than that arbiter must hold back memory requests by the main core
while there are pending vector loads and stores,
in order to ensure data consistency.
The output ports ``pending_load_o`` and ``pending_store_o`` indicate
whether a vector load or store is currently in progress, respectively.
Data requests of the main core must be paused according to the following table:

+------------------+-------------------+----------------------------------------------------------+
|``pending_load_o``|``pending_store_o``| Rule                                                     |
+==================+===================+==========================================================+
| 0                | 0                 | Main core may read and write data                        |
+------------------+-------------------+----------------------------------------------------------+
| 1                | 0                 | Main core may read data, but data writes are held back   |
+------------------+-------------------+----------------------------------------------------------+
| X                | 1                 | Both data reads and writes from the main core must be    |
|                  |                   | held back                                                |
+------------------+-------------------+----------------------------------------------------------+

If Vicuna's memory interface is connected to the main core,
then the CORE-V-XIF protocol ensures data consistency
and ``pending_load_o`` and ``pending_store_o`` should be left unconnected.

The ``csr_*`` ports are a deprecated way of accessing the seven vector CSRs,
as defined in the `RISC-V V extension specification <https://github.com/riscv/riscv-v-spec>`__.
Note that the ``vcsr`` CSR is just a concatenation of ``vxsat`` and ``vxrm``,
which is why no dedicated ports for that CSR are provided.
The ``csr_*_o`` ports can be used to read the content of any of the vector CSRs.
The ``csr_*_set_i`` and ``csr_*_i`` port pairs can be used to overwrite the content
of the four read/write CSRs.
The ``csr_*_set_i`` ports are used as active-high write enable signals,
which move the data supplied on the associated ``csr_*_i`` port into the corresponding CSR.

The ``csr_*`` ports deprecated and will be removed in the future.
The vector CSRs should be accessed via the CORE-V-XIF using RISC-V's regular CSR instructions
(the main core should attempt to offload CSR instruction for CSRs that it does not recognize).
Designs should leave the ``csr_*_o`` ports unconnected and drive the ``csr_*_i`` ports with ``'0``.

The ``pend_vreg_wr_map_o`` output port is used for debug purposes
to keep track of pending vector register writes within Vicuna.
Design should leave that port unconnected.


Integrate Vicuna combined with a main core
------------------------------------------

Instantiate the ``vproc_top`` module using the following instantiation template:

.. code-block:: systemverilog

   vproc_top #(
       .MEM_W              (                       ),
       .VMEM_W             (                       ),
       .ICACHE_SZ          (                       ),
       .ICACHE_LINE_W      (                       ),
       .DCACHE_SZ          (                       ),
       .DCACHE_LINE_W      (                       )
   ) vproc (
       .clk_i              (                       ),
       .rst_ni             (                       ),
       .mem_req_o          (                       ),
       .mem_addr_o         (                       ),
       .mem_we_o           (                       ),
       .mem_be_o           (                       ),
       .mem_wdata_o        (                       ),
       .mem_rvalid_i       (                       ),
       .mem_err_i          (                       ),
       .mem_rdata_i        (                       ),
       .pend_vreg_wr_map_o (                       )
   );


.. _top_parameters:

Parameters
^^^^^^^^^^

+-----------------+----------------+----------------+---------------------------------------------+
| Name            | Type           | Default        | Description                                 |
+=================+================+================+=============================================+
|``MEM_W``        |``int unsigned``|``32``          | Memory bus width (bits)                     |
+-----------------+----------------+----------------+---------------------------------------------+
|``VMEM_W``       |``int unsigned``|``32``          | Vector (XIF) memory interface width (bits)  |
+-----------------+----------------+----------------+---------------------------------------------+
|``VREG_TYPE``    |``vreg_type``   |``VREG_GENERIC``| Vector register file type (defined in       |
|                 |                |                | ``vproc_pkg``, see :ref:`the parameters of  |
|                 |                |                | the core module <core_parameters_config>`)  |
+-----------------+----------------+----------------+---------------------------------------------+
|``MUL_TYPE``     |``mul_type``    |``MUL_GENERIC`` | Vector multiplier type (defined in          |
|                 |                |                | ``vproc_pkg``, see :ref:`the parameters of  |
|                 |                |                | the core module <core_parameters_config>`)  |
+-----------------+----------------+----------------+---------------------------------------------+
|``ICACHE_SZ``    |``int unsigned``|``0``           | Instruction cache size (bytes,              |
|                 |                |                | 0 = no instruction cache                    |
+-----------------+----------------+----------------+---------------------------------------------+
|``ICACHE_LINE_W``|``int unsigned``|``128``         | Line width of the instruction cache (bits)  |
+-----------------+----------------+----------------+---------------------------------------------+
|``DCACHE_SZ``    |``int unsigned``|``0``           | Data cache size (bytes, 0 = no data cache)  |
+-----------------+----------------+----------------+---------------------------------------------+
|``DCACHE_LINE_W``|``int unsigned``|``512``         | Line width of the data cache (bits)         |
+-----------------+----------------+----------------+---------------------------------------------+


.. _top_ports:

Ports
^^^^^

+----------------------+-------+---------+--------------------------------------------------------+
| Name                 | Width |Direction| Description                                            |
+======================+=======+=========+========================================================+
|``clk_i``             | 1     | input   | Clock signal                                           |
+----------------------+-------+---------+--------------------------------------------------------+
|``rst_ni``            | 1     | input   | Active low reset                                       |
+----------------------+-------+---------+--------------------------------------------------------+
|``mem_req_o``         | 1     | output  | Memory request valid signal (high for one cycle)       |
+----------------------+-------+---------+--------------------------------------------------------+
|``mem_addr_o``        | 32    | output  | Memory address (word aligned, valid when ``mem_req_o`` |
|                      |       |         | is high)                                               |
+----------------------+-------+---------+--------------------------------------------------------+
|``mem_we_o``          | 1     | output  | Memory write enable (high for writes, low for reads,   |
|                      |       |         | (valid when ``mem_req_o`` is high)                     |
+----------------------+-------+---------+--------------------------------------------------------+
|``mem_be_o``          |MEM_W/8| output  | Memory byte enable for writes  (valid when             |
|                      |       |         | ``mem_req_o`` is high)                                 |
+----------------------+-------+---------+--------------------------------------------------------+
|``mem_wdata_o``       | MEM_W | output  | Memory write data (valid when ``mem_req_o`` is high)   |
+----------------------+-------+---------+--------------------------------------------------------+
|``mem_rvalid_i``      | 1     | input   | Memory read data valid signal (high for one cycle)     |
+----------------------+-------+---------+--------------------------------------------------------+
|``mem_err_i``         | 1     | input   | Memory error (high on error, valid when                |
|                      |       |         | ``mem_rvalid_i`` is high)                              |
+----------------------+-------+---------+--------------------------------------------------------+
|``mem_rdata_i``       | MEM_W | input   | Memory read data (valid when ``mem_rvalid_i`` is high) |
+----------------------+-------+---------+--------------------------------------------------------+
|``pend_vreg_wr_map_o``| 32    | output  | *Debug* Pending vector register writes map             |
+----------------------+-------+---------+--------------------------------------------------------+
