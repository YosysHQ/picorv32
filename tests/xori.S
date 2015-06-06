# See LICENSE for license details.

#*****************************************************************************
# xori.S
#-----------------------------------------------------------------------------
#
# Test xori instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Logical tests
  #-------------------------------------------------------------

  TEST_IMM_OP( 2, xori, 0xff00f00f, 0x00ff0f00, 0xf0f );
  TEST_IMM_OP( 3, xori, 0x0ff00f00, 0x0ff00ff0, 0x0f0 );
  TEST_IMM_OP( 4, xori, 0x00ff0ff0, 0x00ff08ff, 0x70f );
  TEST_IMM_OP( 5, xori, 0xf00ff0ff, 0xf00ff00f, 0x0f0 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_IMM_SRC1_EQ_DEST( 6, xori, 0xff00f00f, 0xff00f700, 0x70f );

   #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_IMM_DEST_BYPASS( 7,  0, xori, 0x0ff00f00, 0x0ff00ff0, 0x0f0 );
  TEST_IMM_DEST_BYPASS( 8,  1, xori, 0x00ff0ff0, 0x00ff08ff, 0x70f );
  TEST_IMM_DEST_BYPASS( 9,  2, xori, 0xf00ff0ff, 0xf00ff00f, 0x0f0 );

  TEST_IMM_SRC1_BYPASS( 10, 0, xori, 0x0ff00f00, 0x0ff00ff0, 0x0f0 );
  TEST_IMM_SRC1_BYPASS( 11, 1, xori, 0x00ff0ff0, 0x00ff0fff, 0x00f );
  TEST_IMM_SRC1_BYPASS( 12, 2, xori, 0xf00ff0ff, 0xf00ff00f, 0x0f0 );

  TEST_IMM_ZEROSRC1( 13, xori, 0x0f0, 0x0f0 );
  TEST_IMM_ZERODEST( 14, xori, 0x00ff00ff, 0x70f );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
