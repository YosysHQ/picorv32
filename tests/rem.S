# See LICENSE for license details.

#*****************************************************************************
# rem.S
#-----------------------------------------------------------------------------
#
# Test rem instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, rem,  2,  20,   6 );
  TEST_RR_OP( 3, rem, -2, -20,   6 );
  TEST_RR_OP( 4, rem,  2,  20,  -6 );
  TEST_RR_OP( 5, rem, -2, -20,  -6 );

  TEST_RR_OP( 6, rem,  0, -1<<31,  1 );
  TEST_RR_OP( 7, rem,  0, -1<<31, -1 );

  TEST_RR_OP( 8, rem, -1<<31, -1<<31, 0 );
  TEST_RR_OP( 9, rem,      1,      1, 0 );
  TEST_RR_OP(10, rem,      0,      0, 0 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
