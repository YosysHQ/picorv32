# See LICENSE for license details.

#*****************************************************************************
# sb.S
#-----------------------------------------------------------------------------
#
# Test sb instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Basic tests
  #-------------------------------------------------------------

  TEST_ST_OP( 2, lb, sb, 0xffffffaa, 0, tdat );
  TEST_ST_OP( 3, lb, sb, 0x00000000, 1, tdat );
  TEST_ST_OP( 4, lh, sb, 0xffffefa0, 2, tdat );
  TEST_ST_OP( 5, lb, sb, 0x0000000a, 3, tdat );

  # Test with negative offset

  TEST_ST_OP( 6, lb, sb, 0xffffffaa, -3, tdat8 );
  TEST_ST_OP( 7, lb, sb, 0x00000000, -2, tdat8 );
  TEST_ST_OP( 8, lb, sb, 0xffffffa0, -1, tdat8 );
  TEST_ST_OP( 9, lb, sb, 0x0000000a, 0,  tdat8 );

  # Test with a negative base

  TEST_CASE( 10, x3, 0x78, \
    la  x1, tdat9; \
    li  x2, 0x12345678; \
    addi x4, x1, -32; \
    sb x2, 32(x4); \
    lb x3, 0(x1); \
  )

  # Test with unaligned base

  TEST_CASE( 11, x3, 0xffffff98, \
    la  x1, tdat9; \
    li  x2, 0x00003098; \
    addi x1, x1, -6; \
    sb x2, 7(x1); \
    la  x4, tdat10; \
    lb x3, 0(x4); \
  )

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_ST_SRC12_BYPASS( 12, 0, 0, lb, sb, 0xffffffdd, 0, tdat );
  TEST_ST_SRC12_BYPASS( 13, 0, 1, lb, sb, 0xffffffcd, 1, tdat );
  TEST_ST_SRC12_BYPASS( 14, 0, 2, lb, sb, 0xffffffcc, 2, tdat );
  TEST_ST_SRC12_BYPASS( 15, 1, 0, lb, sb, 0xffffffbc, 3, tdat );
  TEST_ST_SRC12_BYPASS( 16, 1, 1, lb, sb, 0xffffffbb, 4, tdat );
  TEST_ST_SRC12_BYPASS( 17, 2, 0, lb, sb, 0xffffffab, 5, tdat );

  TEST_ST_SRC21_BYPASS( 18, 0, 0, lb, sb, 0x33, 0, tdat );
  TEST_ST_SRC21_BYPASS( 19, 0, 1, lb, sb, 0x23, 1, tdat );
  TEST_ST_SRC21_BYPASS( 20, 0, 2, lb, sb, 0x22, 2, tdat );
  TEST_ST_SRC21_BYPASS( 21, 1, 0, lb, sb, 0x12, 3, tdat );
  TEST_ST_SRC21_BYPASS( 22, 1, 1, lb, sb, 0x11, 4, tdat );
  TEST_ST_SRC21_BYPASS( 23, 2, 0, lb, sb, 0x01, 5, tdat );

  li a0, 0xef
  la a1, tdat
  sb a0, 3(a1)

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

tdat:
tdat1:  .byte 0xef
tdat2:  .byte 0xef
tdat3:  .byte 0xef
tdat4:  .byte 0xef
tdat5:  .byte 0xef
tdat6:  .byte 0xef
tdat7:  .byte 0xef
tdat8:  .byte 0xef
tdat9:  .byte 0xef
tdat10: .byte 0xef

RVTEST_DATA_END
