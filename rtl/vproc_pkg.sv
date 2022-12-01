// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


package vproc_pkg;

`define VPROC_OP_MODE_UNION
//`define VPROC_OP_REGS_UNION

typedef enum {
    VREG_GENERIC     = 0,
    VREG_XLNX_RAM32M = 1,
    VREG_ASIC        = 2
} vreg_type;

parameter int unsigned VLSU_FLAGS_W = 1;
typedef enum {
    VLSU_ALIGNED_UNITSTRIDE = 0  // base address of unit-strided loads/stores must be aligned to XIF_MEM_W
} vlsu_flag;

parameter int unsigned BUF_FLAGS_W = 12;
typedef enum {
    BUF_DEQUEUE              = 0,  // buffer instruction queue outputs
    BUF_VREG_RD              = 1,  // buffer vector register read ports
    BUF_OPERANDS             = 2,  // within units, buffer operands after unpacking
    BUF_RESULTS              = 3,  // within units, buffer results before packing
    BUF_VLSU_REQUEST         = 4,  // within the VLSU, buffer memory requests
    BUF_VLSU_RDATA           = 5,  // within the VLSU, buffer memory read data
    BUF_VALU_INTERMEDIATE    = 6,  // within the VALU, buffer intermediate results
    BUF_VMUL_MUL_IN          = 7,  // within the VMUL unit, buffer HW multiplier input
    BUF_VMUL_MUL_OUT         = 8,  // within the VMUL unit, buffer HW multiplier output
    BUF_VREG_WR_MUX_TIMEPRED = 9,  // buffer vector register writes in a timing-predictable fashion
    BUF_VREG_WR              = 10, // buffer vector register write ports
    BUF_VREG_PEND            = 11  // buffer pending vreg reads
} buf_flag;

typedef enum {
    MUL_GENERIC      = 0,
    MUL_XLNX_DSP48E1 = 1
} mul_type;

/***** ECE 498 HK MODIFICATIONS *****/
typedef enum {
    DIV_GENERIC      = 0
} div_type;
/***** END ECE 498 HK MODIFICATIONS *****/

typedef enum logic [1:0] {
    INSTR_INVALID,
    INSTR_SPECULATIVE,
    INSTR_COMMITTED,
    INSTR_KILLED
} instr_state;

typedef enum logic [1:0] {
    VSEW_8       = 2'b00,
    VSEW_16      = 2'b01,
    VSEW_32      = 2'b10,
    VSEW_INVALID = 2'b11
} cfg_vsew;

typedef enum logic [2:0] {
    LMUL_INVALID = 3'b100,
    LMUL_F8      = 3'b101,
    LMUL_F4      = 3'b110,
    LMUL_F2      = 3'b111,
    LMUL_1       = 3'b000,
    LMUL_2       = 3'b001,
    LMUL_4       = 3'b010,
    LMUL_8       = 3'b011
} cfg_lmul;

typedef enum logic [1:0] {
    EMUL_1 = 2'b00,
    EMUL_2 = 2'b01,
    EMUL_4 = 2'b10,
    EMUL_8 = 2'b11
} cfg_emul;

// Policy for determining the effective vector length of an instruction
typedef enum logic [1:0] {
    EVL_DEFAULT, // default EVL (VL for most instr; depends on EEW/SEW ratio for loads and stores)
    EVL_1,       // set EVL to 1
    EVL_MASK,    // set EVL to ceil(VL/8) (used for loading/storing vector masks)
    EVL_MAX      // set EVL to the maximum value for the current config
} evl_policy;

typedef enum logic [1:0] {
    OP_SINGLEWIDTH,  // neither widening nor narrowing
    OP_WIDENING,     // widening operation with 2*SEW =   SEW op SEW
    OP_WIDENING_VS2, // widening operation with 2*SEW = 2*SEW op SEW
    OP_NARROWING     // narrowing operating with  SEW = 2*SEW op SEW
} op_widenarrow;

// fixed-point rounding mode
typedef enum logic [1:0] {
    VXRM_RNU = 2'b00,   // round-to-nearest-up
    VXRM_RNE = 2'b01,   // round-to-nearest-even
    VXRM_RDN = 2'b10,   // round-down
    VXRM_ROD = 2'b11    // round-to-odd
} cfg_vxrm;

typedef enum logic [2:0] {
    UNIT_LSU,
    UNIT_ALU,
    UNIT_DIV,   // ECE 498 HK MODIFICATION
    UNIT_MUL,
    UNIT_SLD,
    UNIT_ELEM,
    // pseudo-units (used for instructions that require no unit):
    UNIT_CFG
} op_unit;

// The number of different types of execution units (excludes pseudo-units)
parameter int unsigned UNIT_CNT = 6;
// LSU ALU DIV MUL STD ELEM

typedef enum logic [1:0] {
    COUNT_INC_1,
    COUNT_INC_2,
    COUNT_INC_4,
    COUNT_INC_MAX
} count_inc_e;

typedef enum logic [1:0] {
    LSU_UNITSTRIDE,
    LSU_STRIDED,
    LSU_INDEXED
} lsu_stride;

typedef struct packed {
    logic       masked;
    logic       store;
    lsu_stride  stride;
    cfg_vsew    eew;
    logic [2:0] nfields;
`ifdef VPROC_OP_MODE_UNION
    logic [3:0] unused;
`endif
} op_mode_lsu;

typedef enum logic [1:0] {
    ALU_SEL_CARRY,
    ALU_SEL_OVFLW,
    ALU_SEL_LT,
    ALU_SEL_MASK
} opcode_alu_sel;

typedef enum logic [1:0] {
    ALU_SHIFT_VSLL,
    ALU_SHIFT_VSRL,
    ALU_SHIFT_VSRA
} opcode_alu_shift;

typedef enum logic [2:0] {
    ALU_VADD,
    ALU_VSADD,
    ALU_VAND,
    ALU_VOR,
    ALU_VXOR,
    ALU_VSHIFT,
    ALU_VSEL,
    ALU_VSELN
} opcode_alu_res;

typedef enum logic [2:0] {
    ALU_CMP_CMP,
    ALU_CMP_CMPN,
    ALU_CMP_EQ,
    ALU_CMP_NE
} opcode_alu_cmp;

typedef enum logic [1:0] {
    ALU_MASK_NONE,  // mask vreg is not used
    ALU_MASK_WRITE, // mask used as write enable (regular masked operation)
    ALU_MASK_CARRY, // mask used as carry
    ALU_MASK_SEL    // mask used as selector
} opcode_alu_mask;

typedef struct packed {
    logic           cmp;        // compare instruction (result is a mask)
    union packed {
        opcode_alu_sel   sel;
        opcode_alu_shift shift;
    } opx1;
    union packed {
        opcode_alu_res res;
        opcode_alu_cmp cmp;
    } opx2;
    opcode_alu_mask op_mask;
    logic           shift_op;   // shift operands right by 1 bit (also sets carry in for rounding)
    logic           inv_op1;    // invert operand 1
    logic           inv_op2;    // invert operand 2
    logic           sat_res;    // saturate result for narrowing operations
    logic           sigext;
} op_mode_alu;

typedef enum logic [1:0] {
    MUL_VMUL,   // regular multiplication
    MUL_VMULH,  // multiplication retaining high part
    MUL_VSMUL,  // multiplication with rounding and saturation
    MUL_VMACC   // multiply-accumulate
} opcode_mul;

typedef struct packed {
    logic       masked;
    opcode_mul  op;
    logic       accsub;     // subtract from accumulator instead of adding
    logic       op1_signed;
    logic       op2_signed;
    logic       op2_is_vd;
`ifdef VPROC_OP_MODE_UNION
    logic [5:0] unused;
`endif
} op_mode_mul;

/***** ECE 498 HK MODIFICATIONS *****/
typedef enum logic [0:0] {
    DIV_VDIV,   //  divide
    DIV_VREM    // remainder
} opcode_div;

typedef struct packed {
    // TODO
    logic       masked;
    opcode_div  op;
    logic       op1_signed;
    logic       op2_signed;
`ifdef VPROC_OP_MODE_UNION
    logic [8:0] unused;
`endif                                            
} op_mode_div;
/***** END ECE 498 HK MODIFICATIONS *****/

typedef enum logic [0:0] {
    SLD_UP,
    SLD_DOWN
} opcode_sld_dir;

typedef struct packed {
    logic          masked;
    opcode_sld_dir dir;    // slide direction
    logic          slide1; // slide 1 element
`ifdef VPROC_OP_MODE_UNION
    logic [9:0] unused;
`endif
} op_mode_sld;

typedef enum logic [3:0] {
    ELEM_XMV,
    ELEM_VPOPC,
    ELEM_VFIRST,
    ELEM_VID,
    ELEM_VIOTA,
    ELEM_VRGATHER,
    ELEM_VCOMPRESS,
    ELEM_FLUSH,
    ELEM_VREDSUM,
    ELEM_VREDAND,
    ELEM_VREDOR,
    ELEM_VREDXOR,
    ELEM_VREDMINU,
    ELEM_VREDMIN,
    ELEM_VREDMAXU,
    ELEM_VREDMAX
} opcode_elem;

typedef struct packed {
    logic       masked;
    opcode_elem op;
    logic       sigext;
    logic       xreg;
`ifdef VPROC_OP_MODE_UNION
    logic [5:0] unused;
`endif
} op_mode_elem;

typedef enum logic [3:0] {
    // vsetvl (modifies vtype and vl)
    CFG_VSETVL,
    // read-only CSR
    CFG_VTYPE_READ,
    CFG_VL_READ,
    CFG_VLENB_READ,
    // read-write CSR
    CFG_VSTART_WRITE,
    CFG_VSTART_SET,
    CFG_VSTART_CLEAR,
    CFG_VXSAT_WRITE,
    CFG_VXSAT_SET,
    CFG_VXSAT_CLEAR,
    CFG_VXRM_WRITE,
    CFG_VXRM_SET,
    CFG_VXRM_CLEAR,
    CFG_VCSR_WRITE,
    CFG_VCSR_SET,
    CFG_VCSR_CLEAR
} cfg_csr_op;

typedef struct packed {
    cfg_csr_op  csr_op;
    cfg_vsew    vsew;
    cfg_lmul    lmul;
    logic [1:0] agnostic;
    logic       vlmax;
    logic       keep_vl;
} op_mode_cfg;

`ifdef VPROC_OP_MODE_UNION
typedef union packed {
    logic [12:0]  unused;
`else
typedef struct packed {
`endif
    op_mode_lsu  lsu;
    op_mode_alu  alu;
    op_mode_div  div;   // ECE 498 HK MODIFICATION
    op_mode_mul  mul;
    op_mode_sld  sld;
    op_mode_elem elem;
    op_mode_cfg  cfg;
} op_mode;

// source register type:
typedef struct packed {
    logic vreg;
    logic xreg;
`ifdef VPROC_OP_REGS_UNION
    union {
`else
    struct packed {
`endif
       logic [4:0]  vaddr;
       logic [31:0] xval;
    } r;
} op_regs;

// destination register type:
typedef struct packed {
    logic       vreg;
    logic [4:0] addr;
} op_regd;

// operand fetch info structure
typedef struct packed {
    logic shift;
    logic hold;
    logic vreg;
    logic elemwise;
    logic narrow;
    logic sigext;
} unpack_flags;

// result store info structure
typedef struct packed {
    logic       shift;
    logic       elemwise;
    logic       narrow;
    logic       saturate;
    logic       sig;
    logic [2:0] mul_idx;
} pack_flags;

endpackage
