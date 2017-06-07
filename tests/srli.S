# See LICENSE for license details.

#*****************************************************************************
# srli.S
#-----------------------------------------------------------------------------
#
# Test srli instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_IMM_OP( 2,  srli, 0xffff8000, 0xffff8000, 0  );
  TEST_IMM_OP( 3,  srli, 0x7fffc000, 0xffff8000, 1  );
  TEST_IMM_OP( 4,  srli, 0x01ffff00, 0xffff8000, 7  );
  TEST_IMM_OP( 5,  srli, 0x0003fffe, 0xffff8000, 14 );
  TEST_IMM_OP( 6,  srli, 0x0001ffff, 0xffff8001, 15 );

  TEST_IMM_OP( 7,  srli, 0xffffffff, 0xffffffff, 0  );
  TEST_IMM_OP( 8,  srli, 0x7fffffff, 0xffffffff, 1  );
  TEST_IMM_OP( 9,  srli, 0x01ffffff, 0xffffffff, 7  );
  TEST_IMM_OP( 10, srli, 0x0003ffff, 0xffffffff, 14 );
  TEST_IMM_OP( 11, srli, 0x00000001, 0xffffffff, 31 );

  TEST_IMM_OP( 12, srli, 0x21212121, 0x21212121, 0  );
  TEST_IMM_OP( 13, srli, 0x10909090, 0x21212121, 1  );
  TEST_IMM_OP( 14, srli, 0x00424242, 0x21212121, 7  );
  TEST_IMM_OP( 15, srli, 0x00008484, 0x21212121, 14 );
  TEST_IMM_OP( 16, srli, 0x00000000, 0x21212121, 31 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_IMM_SRC1_EQ_DEST( 21, srli, 0x7fffc000, 0xffff8000, 1  );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_IMM_DEST_BYPASS( 22, 0, srl, 0x7fffc000, 0xffff8000, 1  );
  TEST_IMM_DEST_BYPASS( 23, 1, srl, 0x0003fffe, 0xffff8000, 14 );
  TEST_IMM_DEST_BYPASS( 24, 2, srl, 0x0001ffff, 0xffff8000, 15 );

  TEST_IMM_SRC1_BYPASS( 25, 0, srl, 0x7fffc000, 0xffff8000, 1  );
  TEST_IMM_SRC1_BYPASS( 26, 1, srl, 0x0003fffe, 0xffff8000, 14 );
  TEST_IMM_SRC1_BYPASS( 27, 2, srl, 0x0001ffff, 0xffff8000, 15 );


  TEST_IMM_ZEROSRC1( 28, srli, 0, 31 );
  TEST_IMM_ZERODEST( 29, srli, 33, 20 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
