#include <stdint.h>
#include <riscv_vector.h>

int8_t sum_reduce(vint8m1_t vec, size_t vl) {
    while (vl > 8) {
        vint8m1_t tmp;
        tmp = vslidedown_vx_i8m1(tmp, vec, vl / 2, vl);
        vl /= 2;
        vec = vadd_vv_i8m1(vec, tmp, vl);
    }
    vint8m1_t sum = vmv_v_x_i8m1(0, vl);
    sum = vredsum_vs_i8m1_i8m1(sum, vec, sum, vl);
    return vmv_x_s_i8m1_i8(sum);
}
