# See LICENSE for license details.

#*****************************************************************************
# ori.S
#-----------------------------------------------------------------------------
#
# Test ori instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Logical tests
  #-------------------------------------------------------------

  TEST_IMM_OP( 2, ori, 0xffffff0f, 0xff00ff00, 0xf0f );
  TEST_IMM_OP( 3, ori, 0x0ff00ff0, 0x0ff00ff0, 0x0f0 );
  TEST_IMM_OP( 4, ori, 0x00ff07ff, 0x00ff00ff, 0x70f );
  TEST_IMM_OP( 5, ori, 0xf00ff0ff, 0xf00ff00f, 0x0f0 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_IMM_SRC1_EQ_DEST( 6, ori, 0xff00fff0, 0xff00ff00, 0x0f0 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_IMM_DEST_BYPASS( 7,  0, ori, 0x0ff00ff0, 0x0ff00ff0, 0x0f0 );
  TEST_IMM_DEST_BYPASS( 8,  1, ori, 0x00ff07ff, 0x00ff00ff, 0x70f );
  TEST_IMM_DEST_BYPASS( 9,  2, ori, 0xf00ff0ff, 0xf00ff00f, 0x0f0 );

  TEST_IMM_SRC1_BYPASS( 10, 0, ori, 0x0ff00ff0, 0x0ff00ff0, 0x0f0 );
  TEST_IMM_SRC1_BYPASS( 11, 1, ori, 0xffffffff, 0x00ff00ff, 0xf0f );
  TEST_IMM_SRC1_BYPASS( 12, 2, ori, 0xf00ff0ff, 0xf00ff00f, 0x0f0 );

  TEST_IMM_ZEROSRC1( 13, ori, 0x0f0, 0x0f0 );
  TEST_IMM_ZERODEST( 14, ori, 0x00ff00ff, 0x70f );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
