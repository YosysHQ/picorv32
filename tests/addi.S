# See LICENSE for license details.

#*****************************************************************************
# addi.S
#-----------------------------------------------------------------------------
#
# Test addi instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_IMM_OP( 2,  addi, 0x00000000, 0x00000000, 0x000 );
  TEST_IMM_OP( 3,  addi, 0x00000002, 0x00000001, 0x001 );
  TEST_IMM_OP( 4,  addi, 0x0000000a, 0x00000003, 0x007 );

  TEST_IMM_OP( 5,  addi, 0xfffff800, 0x00000000, 0x800 );
  TEST_IMM_OP( 6,  addi, 0x80000000, 0x80000000, 0x000 );
  TEST_IMM_OP( 7,  addi, 0x7ffff800, 0x80000000, 0x800 );

  TEST_IMM_OP( 8,  addi, 0x000007ff, 0x00000000, 0x7ff );
  TEST_IMM_OP( 9,  addi, 0x7fffffff, 0x7fffffff, 0x000 );
  TEST_IMM_OP( 10, addi, 0x800007fe, 0x7fffffff, 0x7ff );

  TEST_IMM_OP( 11, addi, 0x800007ff, 0x80000000, 0x7ff );
  TEST_IMM_OP( 12, addi, 0x7ffff7ff, 0x7fffffff, 0x800 );

  TEST_IMM_OP( 13, addi, 0xffffffff, 0x00000000, 0xfff );
  TEST_IMM_OP( 14, addi, 0x00000000, 0xffffffff, 0x001 );
  TEST_IMM_OP( 15, addi, 0xfffffffe, 0xffffffff, 0xfff );

  TEST_IMM_OP( 16, addi, 0x80000000, 0x7fffffff, 0x001 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_IMM_SRC1_EQ_DEST( 17, addi, 24, 13, 11 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_IMM_DEST_BYPASS( 18, 0, addi, 24, 13, 11 );
  TEST_IMM_DEST_BYPASS( 19, 1, addi, 23, 13, 10 );
  TEST_IMM_DEST_BYPASS( 20, 2, addi, 22, 13,  9 );

  TEST_IMM_SRC1_BYPASS( 21, 0, addi, 24, 13, 11 );
  TEST_IMM_SRC1_BYPASS( 22, 1, addi, 23, 13, 10 );
  TEST_IMM_SRC1_BYPASS( 23, 2, addi, 22, 13,  9 );

  TEST_IMM_ZEROSRC1( 24, addi, 32, 32 );
  TEST_IMM_ZERODEST( 25, addi, 33, 50 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
