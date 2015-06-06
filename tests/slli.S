# See LICENSE for license details.

#*****************************************************************************
# slli.S
#-----------------------------------------------------------------------------
#
# Test slli instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_IMM_OP( 2,  slli, 0x00000001, 0x00000001, 0  );
  TEST_IMM_OP( 3,  slli, 0x00000002, 0x00000001, 1  );
  TEST_IMM_OP( 4,  slli, 0x00000080, 0x00000001, 7  );
  TEST_IMM_OP( 5,  slli, 0x00004000, 0x00000001, 14 );
  TEST_IMM_OP( 6,  slli, 0x80000000, 0x00000001, 31 );

  TEST_IMM_OP( 7,  slli, 0xffffffff, 0xffffffff, 0  );
  TEST_IMM_OP( 8,  slli, 0xfffffffe, 0xffffffff, 1  );
  TEST_IMM_OP( 9,  slli, 0xffffff80, 0xffffffff, 7  );
  TEST_IMM_OP( 10, slli, 0xffffc000, 0xffffffff, 14 );
  TEST_IMM_OP( 11, slli, 0x80000000, 0xffffffff, 31 );

  TEST_IMM_OP( 12, slli, 0x21212121, 0x21212121, 0  );
  TEST_IMM_OP( 13, slli, 0x42424242, 0x21212121, 1  );
  TEST_IMM_OP( 14, slli, 0x90909080, 0x21212121, 7  );
  TEST_IMM_OP( 15, slli, 0x48484000, 0x21212121, 14 );
  TEST_IMM_OP( 16, slli, 0x80000000, 0x21212121, 31 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_IMM_SRC1_EQ_DEST( 17, slli, 0x00000080, 0x00000001, 7 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_IMM_DEST_BYPASS( 18, 0, slli, 0x00000080, 0x00000001, 7  );
  TEST_IMM_DEST_BYPASS( 19, 1, slli, 0x00004000, 0x00000001, 14 );
  TEST_IMM_DEST_BYPASS( 20, 2, slli, 0x80000000, 0x00000001, 31 );

  TEST_IMM_SRC1_BYPASS( 21, 0, slli, 0x00000080, 0x00000001, 7  );
  TEST_IMM_SRC1_BYPASS( 22, 1, slli, 0x00004000, 0x00000001, 14 );
  TEST_IMM_SRC1_BYPASS( 23, 2, slli, 0x80000000, 0x00000001, 31 );

  TEST_IMM_ZEROSRC1( 24, slli, 0, 31 );
  TEST_IMM_ZERODEST( 25, slli, 33, 20 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
