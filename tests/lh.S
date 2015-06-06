# See LICENSE for license details.

#*****************************************************************************
# lh.S
#-----------------------------------------------------------------------------
#
# Test lh instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Basic tests
  #-------------------------------------------------------------

  TEST_LD_OP( 2, lh, 0x000000ff, 0,  tdat );
  TEST_LD_OP( 3, lh, 0xffffff00, 2,  tdat );
  TEST_LD_OP( 4, lh, 0x00000ff0, 4,  tdat );
  TEST_LD_OP( 5, lh, 0xfffff00f, 6, tdat );

  # Test with negative offset

  TEST_LD_OP( 6, lh, 0x000000ff, -6,  tdat4 );
  TEST_LD_OP( 7, lh, 0xffffff00, -4,  tdat4 );
  TEST_LD_OP( 8, lh, 0x00000ff0, -2,  tdat4 );
  TEST_LD_OP( 9, lh, 0xfffff00f,  0, tdat4 );

  # Test with a negative base

  TEST_CASE( 10, x3, 0x000000ff, \
    la  x1, tdat; \
    addi x1, x1, -32; \
    lh x3, 32(x1); \
  )

  # Test with unaligned base

  TEST_CASE( 11, x3, 0xffffff00, \
    la  x1, tdat; \
    addi x1, x1, -5; \
    lh x3, 7(x1); \
  )

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_LD_DEST_BYPASS( 12, 0, lh, 0x00000ff0, 2, tdat2 );
  TEST_LD_DEST_BYPASS( 13, 1, lh, 0xfffff00f, 2, tdat3 );
  TEST_LD_DEST_BYPASS( 14, 2, lh, 0xffffff00, 2, tdat1 );

  TEST_LD_SRC1_BYPASS( 15, 0, lh, 0x00000ff0, 2, tdat2 );
  TEST_LD_SRC1_BYPASS( 16, 1, lh, 0xfffff00f, 2, tdat3 );
  TEST_LD_SRC1_BYPASS( 17, 2, lh, 0xffffff00, 2, tdat1 );

  #-------------------------------------------------------------
  # Test write-after-write hazard
  #-------------------------------------------------------------

  TEST_CASE( 18, x2, 2, \
    la  x3, tdat; \
    lh  x2, 0(x3); \
    li  x2, 2; \
  )

  TEST_CASE( 19, x2, 2, \
    la  x3, tdat; \
    lh  x2, 0(x3); \
    nop; \
    li  x2, 2; \
  )

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

tdat:
tdat1:  .half 0x00ff
tdat2:  .half 0xff00
tdat3:  .half 0x0ff0
tdat4:  .half 0xf00f

RVTEST_DATA_END
