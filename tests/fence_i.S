# See LICENSE for license details.

#*****************************************************************************
# fence_i.S
#-----------------------------------------------------------------------------
#
# Test self-modifying code and the fence.i instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

li a3, 111
la a0, 3f
la a1, 1f
la a2, 2f
lw a0, 0(a0)

# test I$ hit
.align 6
sw a0, 0(a1)
fence.i

1: addi a3, a3, 222
TEST_CASE( 2, a3, 444, nop )

# test prefetcher hit
li a4, 100
1: addi a4, a4, -1
bnez a4, 1b

sw a0, 0(a2)
fence.i

.align 6
2: addi a3, a3, 555
TEST_CASE( 3, a3, 777, nop )

3: addi a3, a3, 333

TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
