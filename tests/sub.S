# See LICENSE for license details.

#*****************************************************************************
# sub.S
#-----------------------------------------------------------------------------
#
# Test sub instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2,  sub, 0x00000000, 0x00000000, 0x00000000 );
  TEST_RR_OP( 3,  sub, 0x00000000, 0x00000001, 0x00000001 );
  TEST_RR_OP( 4,  sub, 0xfffffffc, 0x00000003, 0x00000007 );

  TEST_RR_OP( 5,  sub, 0x00008000, 0x00000000, 0xffff8000 );
  TEST_RR_OP( 6,  sub, 0x80000000, 0x80000000, 0x00000000 );
  TEST_RR_OP( 7,  sub, 0x80008000, 0x80000000, 0xffff8000 );

  TEST_RR_OP( 8,  sub, 0xffff8001, 0x00000000, 0x00007fff );
  TEST_RR_OP( 9,  sub, 0x7fffffff, 0x7fffffff, 0x00000000 );
  TEST_RR_OP( 10, sub, 0x7fff8000, 0x7fffffff, 0x00007fff );

  TEST_RR_OP( 11, sub, 0x7fff8001, 0x80000000, 0x00007fff );
  TEST_RR_OP( 12, sub, 0x80007fff, 0x7fffffff, 0xffff8000 );

  TEST_RR_OP( 13, sub, 0x00000001, 0x00000000, 0xffffffff );
  TEST_RR_OP( 14, sub, 0xfffffffe, 0xffffffff, 0x00000001 );
  TEST_RR_OP( 15, sub, 0x00000000, 0xffffffff, 0xffffffff );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_RR_SRC1_EQ_DEST( 16, sub, 2, 13, 11 );
  TEST_RR_SRC2_EQ_DEST( 17, sub, 3, 14, 11 );
  TEST_RR_SRC12_EQ_DEST( 18, sub, 0, 13 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_RR_DEST_BYPASS( 19, 0, sub, 2, 13, 11 );
  TEST_RR_DEST_BYPASS( 20, 1, sub, 3, 14, 11 );
  TEST_RR_DEST_BYPASS( 21, 2, sub, 4, 15, 11 );

  TEST_RR_SRC12_BYPASS( 22, 0, 0, sub, 2, 13, 11 );
  TEST_RR_SRC12_BYPASS( 23, 0, 1, sub, 3, 14, 11 );
  TEST_RR_SRC12_BYPASS( 24, 0, 2, sub, 4, 15, 11 );
  TEST_RR_SRC12_BYPASS( 25, 1, 0, sub, 2, 13, 11 );
  TEST_RR_SRC12_BYPASS( 26, 1, 1, sub, 3, 14, 11 );
  TEST_RR_SRC12_BYPASS( 27, 2, 0, sub, 4, 15, 11 );

  TEST_RR_SRC21_BYPASS( 28, 0, 0, sub, 2, 13, 11 );
  TEST_RR_SRC21_BYPASS( 29, 0, 1, sub, 3, 14, 11 );
  TEST_RR_SRC21_BYPASS( 30, 0, 2, sub, 4, 15, 11 );
  TEST_RR_SRC21_BYPASS( 31, 1, 0, sub, 2, 13, 11 );
  TEST_RR_SRC21_BYPASS( 32, 1, 1, sub, 3, 14, 11 );
  TEST_RR_SRC21_BYPASS( 33, 2, 0, sub, 4, 15, 11 );

  TEST_RR_ZEROSRC1( 34, sub, 15, -15 );
  TEST_RR_ZEROSRC2( 35, sub, 32, 32 );
  TEST_RR_ZEROSRC12( 36, sub, 0 );
  TEST_RR_ZERODEST( 37, sub, 16, 30 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
