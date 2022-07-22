// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

// This interface definition is based on the CORE-V-XIF specification for a CPU
// extension interface. The current draft of the specification can be found at:
// https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/x_ext.html
// Disclaimer: The copyright for the CORE-V-XIF specification and interface
// definition is owned by the OpenHW Group.


interface vproc_xif #(
        parameter int unsigned X_NUM_RS    =  2,  // Number of register file read ports that can be used by the eXtension interface
        parameter int unsigned X_ID_WIDTH  =  3,  // Identification width for the eXtension interface
        parameter int unsigned X_MEM_WIDTH =  32, // Memory access width for loads/stores via the eXtension interface
        parameter int unsigned X_RFR_WIDTH =  32, // Register file read access width for the eXtension interface
        parameter int unsigned X_RFW_WIDTH =  32, // Register file write access width for the eXtension interface
        parameter logic [31:0] X_MISA      =  '0  // MISA extensions implemented on the eXtension interface
    );

    typedef struct packed {
        logic [           31:0]                  instr;     // Offloaded instruction
        logic [            1:0]                  mode;      // Privilege level
        logic [X_ID_WIDTH -1:0]                  id;        // Identification of the offloaded instruction
        logic [X_NUM_RS   -1:0][X_RFR_WIDTH-1:0] rs;        // Register file source operands for the offloaded instruction
        logic [X_NUM_RS   -1:0]                  rs_valid;  // Validity of the register file source operand(s)
    } x_issue_req_t;

    typedef struct packed {
        logic       accept;     // Is the offloaded instruction (id) accepted by the coprocessor?
        logic       writeback;  // Will the coprocessor perform a writeback in the core to rd?
        logic       dualwrite;  // Will the coprocessor perform a dual writeback in the core to rd and rd+1?
        logic [2:0] dualread;   // Will the coprocessor require dual reads from rs1\rs2\rs3 and rs1+1\rs2+1\rs3+1?
        logic       loadstore;  // Is the offloaded instruction a load/store instruction?
        logic       exc;        // Can the offloaded instruction possibly cause a synchronous exception in the coprocessor itself?
    } x_issue_resp_t;

    typedef struct packed {
        logic [X_ID_WIDTH-1:0] id;          // Identification of the offloaded instruction
        logic                  commit_kill; // Shall an offloaded instruction be killed?
    } x_commit_t;

    typedef struct packed {
        logic [X_ID_WIDTH   -1:0] id;       // Identification of the offloaded instruction
        logic [             31:0] addr;     // Virtual address of the memory transaction
        logic [              1:0] mode;     // Privilege level
        logic                     we;       // Write enable of the memory transaction
        logic [              2:0] size;     // Size of the memory transaction
        logic [X_MEM_WIDTH/8-1:0] be;       // Byte enable mask of the memory transaction
        logic [              1:0] attr;     // Memory transaction attributes
        logic [X_MEM_WIDTH  -1:0] wdata;    // Write data of a store memory transaction
        logic                     last;     // Is this the last memory transaction for the offloaded instruction?
        logic                     spec;     // Is the memory transaction speculative?
    } x_mem_req_t;

    typedef struct packed {
        logic       exc;      // Did the memory request cause a synchronous exception?
        logic [5:0] exccode;  // Exception code
        logic       dbg;      // Did the memory request cause a debug trigger match with mcontrol.timing = 0?
    } x_mem_resp_t;

    typedef struct packed {
        logic [X_ID_WIDTH -1:0] id;     // Identification of the offloaded instruction
        logic [X_MEM_WIDTH-1:0] rdata;  // Read data of a read memory transaction
        logic                   err;    // Did the instruction cause a bus error?
        logic                   dbg;    // Did the read data cause a debug trigger match with mcontrol.timing = 0?
    } x_mem_result_t;

    typedef struct packed {
        logic [X_ID_WIDTH -   1:0] id;      // Identification of the offloaded instruction
        logic [X_RFW_WIDTH-   1:0] data;    // Register file write data value(s)
        logic [               4:0] rd;      // Register file destination address(es)
        logic [X_RFW_WIDTH/32-1:0] we;      // Register file write enable(s)
        logic                      exc;     // Did the instruction cause a synchronous exception?
        logic [               5:0] exccode; // Exception code
        logic                      err;     // Instruction caused a memory bus error
        logic                      dbg;     // Instruction caused a debug trigger with mcontrol.timing = 0
    } x_result_t;


    // Issue interface
    logic               issue_valid;
    logic               issue_ready;
    x_issue_req_t       issue_req;
    x_issue_resp_t      issue_resp;

    // Commit interface
    logic               commit_valid;
    x_commit_t          commit;

    // Memory (request/response) interface
    logic               mem_valid;
    logic               mem_ready;
    x_mem_req_t         mem_req;
    x_mem_resp_t        mem_resp;

    // Memory result interface
    logic               mem_result_valid;
    x_mem_result_t      mem_result;

    // Result interface
    logic               result_valid;
    logic               result_ready;
    x_result_t          result;

    // Port directions for host CPU
    modport cpu_issue (
        output issue_valid,
        input  issue_ready,
        output issue_req,
        input  issue_resp
    );
    modport cpu_commit (
        output commit_valid,
        output commit
    );
    modport cpu_mem (
        input  mem_valid,
        output mem_ready,
        input  mem_req,
        output mem_resp
    );
    modport cpu_mem_result (
        output mem_result_valid,
        output mem_result
    );
    modport cpu_result (
        input  result_valid,
        output result_ready,
        input  result
    );

    // Port directions for extension
    modport coproc_issue (
        input  issue_valid,
        output issue_ready,
        input  issue_req,
        output issue_resp
    );
    modport coproc_commit (
        input  commit_valid,
        input  commit
    );
    modport coproc_mem (
        output mem_valid,
        input  mem_ready,
        output mem_req,
        input  mem_resp
    );
    modport coproc_mem_result (
        input  mem_result_valid,
        input  mem_result
    );
    modport coproc_result (
        output result_valid,
        input  result_ready,
        output result
    );

endinterface
