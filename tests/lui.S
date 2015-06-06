# See LICENSE for license details.

#*****************************************************************************
# lui.S
#-----------------------------------------------------------------------------
#
# Test lui instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Basic tests
  #-------------------------------------------------------------

  TEST_CASE( 2, x1, 0x00000000, lui x1, 0x00000 );
  TEST_CASE( 3, x1, 0xfffff800, lui x1, 0xfffff;sra x1,x1,1);
  TEST_CASE( 4, x1, 0x000007ff, lui x1, 0x7ffff;sra x1,x1,20);
  TEST_CASE( 5, x1, 0xfffff800, lui x1, 0x80000;sra x1,x1,20);

  TEST_CASE( 6, x0, 0, lui x0, 0x80000 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
