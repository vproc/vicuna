#include <stdint.h>
#include <riscv_vector.h>

vint8m1_t vload_stride_4(int8_t *addr, size_t vl) {
    vint32m4_t vec32 = vle32_v_i32m4((int32_t *)addr, vl);
    vint16m2_t vec16 = vnsra_wx_i16m2(vec32, 0, vl);
    return vnsra_wx_i8m1(vec16, 0, vl);
}
