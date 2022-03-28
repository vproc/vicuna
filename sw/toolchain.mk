# Copyright CSEM
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

CMAKE                      := cmake
CC                         := gcc

LLVM_INSTALL_DIR           := $(LLVM_DIR)/install
LLVM_REPO                  := https://github.com/llvm/llvm-project
LLVM_COMMIT                := 5177676261147ef6c930e060a13a895e45bb6af4
LLVM_DEFAULT_TARGET_TRIPLE := riscv32-unknown-elf
LLVM_TARGETS_TO_BUILD      := RISCV
LLVM_ENABLE_PROJECTS       := "clang;lld"
MAKE_BUILD_TYPE            := Release


NEWLIB_REPO                := https://sourceware.org/git/newlib-cygwin.git
NEWLIB_COMMIT              := 761ef3b434b5eb7f321e58c3fae1f578f5c34999

.PHONY: llvm
llvm: check_env_vars
	cd $(LLVM_DIR) && mkdir install &&                                     \
	git clone --recurse-submodules $(LLVM_REPO) && cd llvm-project &&      \
	git checkout $(LLVM_COMMIT) && rm build/ -r -f &&                      \
	mkdir build && cd build &&                                             \
	$(CMAKE) -G "Unix Makefiles"                                           \
	         -DCMAKE_C_COMPILER=$(CC)                                      \
	         -DCMAKE_INSTALL_PREFIX=$(LLVM_INSTALL_DIR)                    \
	         -DLLVM_ENABLE_PROJECTS=$(LLVM_ENABLE_PROJECTS)                \
	         -DCMAKE_BUILD_TYPE=$(MAKE_BUILD_TYPE)                         \
	         -DLLVM_DEFAULT_TARGET_TRIPLE=$(LLVM_DEFAULT_TARGET_TRIPLE)    \
	         -DLLVM_TARGETS_TO_BUILD=$(LLVM_TARGETS_TO_BUILD)              \
	         ../llvm && cd .. &&                                           \
	$(CMAKE) --build build --target install && cd $(LLVM_DIR) &&           \
	git clone $(NEWLIB_REPO) newlib && cd newlib &&                        \
	git checkout $(NEWLIB_COMMIT) &&                                       \
	rm -rf build && mkdir -p build && cd build &&                          \
	../configure --prefix=${LLVM_INSTALL_DIR}                              \
	--target=riscv32-unknown-elf                                           \
	CC_FOR_TARGET="${LLVM_INSTALL_DIR}/bin/clang -march=rv32gc -mabi=ilp32 \
	-mno-relax -mcmodel=medany"                                            \
	AS_FOR_TARGET=${LLVM_INSTALL_DIR}/bin/llvm-as                          \
	AR_FOR_TARGET=${LLVM_INSTALL_DIR}/bin/llvm-ar                          \
	LD_FOR_TARGET=${LLVM_INSTALL_DIR}/bin/llvm-ld                          \
	RANLIB_FOR_TARGET=${LLVM_INSTALL_DIR}/bin/llvm-ranlib &&               \
	make &&                                                                \
	make install

check_env_vars:
ifndef LLVM_DIR
	$(error LLVM_DIR variable not set. (set it to the path where the llvm  \
	repository will be cloned to and the llvm toolchain will be installed))
endif
