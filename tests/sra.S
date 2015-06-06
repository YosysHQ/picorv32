# See LICENSE for license details.

#*****************************************************************************
# sra.S
#-----------------------------------------------------------------------------
#
# Test sra instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2,  sra, 0x80000000, 0x80000000, 0  );
  TEST_RR_OP( 3,  sra, 0xc0000000, 0x80000000, 1  );
  TEST_RR_OP( 4,  sra, 0xff000000, 0x80000000, 7  );
  TEST_RR_OP( 5,  sra, 0xfffe0000, 0x80000000, 14 );
  TEST_RR_OP( 6,  sra, 0xffffffff, 0x80000001, 31 );

  TEST_RR_OP( 7,  sra, 0x7fffffff, 0x7fffffff, 0  );
  TEST_RR_OP( 8,  sra, 0x3fffffff, 0x7fffffff, 1  );
  TEST_RR_OP( 9,  sra, 0x00ffffff, 0x7fffffff, 7  );
  TEST_RR_OP( 10, sra, 0x0001ffff, 0x7fffffff, 14 );
  TEST_RR_OP( 11, sra, 0x00000000, 0x7fffffff, 31 );

  TEST_RR_OP( 12, sra, 0x81818181, 0x81818181, 0  );
  TEST_RR_OP( 13, sra, 0xc0c0c0c0, 0x81818181, 1  );
  TEST_RR_OP( 14, sra, 0xff030303, 0x81818181, 7  );
  TEST_RR_OP( 15, sra, 0xfffe0606, 0x81818181, 14 );
  TEST_RR_OP( 16, sra, 0xffffffff, 0x81818181, 31 );

  # Verify that shifts only use bottom five bits

  TEST_RR_OP( 17, sra, 0x81818181, 0x81818181, 0xffffffc0 );
  TEST_RR_OP( 18, sra, 0xc0c0c0c0, 0x81818181, 0xffffffc1 );
  TEST_RR_OP( 19, sra, 0xff030303, 0x81818181, 0xffffffc7 );
  TEST_RR_OP( 20, sra, 0xfffe0606, 0x81818181, 0xffffffce );
  TEST_RR_OP( 21, sra, 0xffffffff, 0x81818181, 0xffffffff );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_RR_SRC1_EQ_DEST( 22, sra, 0xff000000, 0x80000000, 7  );
  TEST_RR_SRC2_EQ_DEST( 23, sra, 0xfffe0000, 0x80000000, 14 );
  TEST_RR_SRC12_EQ_DEST( 24, sra, 0, 7 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_RR_DEST_BYPASS( 25, 0, sra, 0xff000000, 0x80000000, 7  );
  TEST_RR_DEST_BYPASS( 26, 1, sra, 0xfffe0000, 0x80000000, 14 );
  TEST_RR_DEST_BYPASS( 27, 2, sra, 0xffffffff, 0x80000000, 31 );

  TEST_RR_SRC12_BYPASS( 28, 0, 0, sra, 0xff000000, 0x80000000, 7  );
  TEST_RR_SRC12_BYPASS( 29, 0, 1, sra, 0xfffe0000, 0x80000000, 14 );
  TEST_RR_SRC12_BYPASS( 30, 0, 2, sra, 0xffffffff, 0x80000000, 31 );
  TEST_RR_SRC12_BYPASS( 31, 1, 0, sra, 0xff000000, 0x80000000, 7  );
  TEST_RR_SRC12_BYPASS( 32, 1, 1, sra, 0xfffe0000, 0x80000000, 14 );
  TEST_RR_SRC12_BYPASS( 33, 2, 0, sra, 0xffffffff, 0x80000000, 31 );

  TEST_RR_SRC21_BYPASS( 34, 0, 0, sra, 0xff000000, 0x80000000, 7  );
  TEST_RR_SRC21_BYPASS( 35, 0, 1, sra, 0xfffe0000, 0x80000000, 14 );
  TEST_RR_SRC21_BYPASS( 36, 0, 2, sra, 0xffffffff, 0x80000000, 31 );
  TEST_RR_SRC21_BYPASS( 37, 1, 0, sra, 0xff000000, 0x80000000, 7  );
  TEST_RR_SRC21_BYPASS( 38, 1, 1, sra, 0xfffe0000, 0x80000000, 14 );
  TEST_RR_SRC21_BYPASS( 39, 2, 0, sra, 0xffffffff, 0x80000000, 31 );

  TEST_RR_ZEROSRC1( 40, sra, 0, 15 );
  TEST_RR_ZEROSRC2( 41, sra, 32, 32 );
  TEST_RR_ZEROSRC12( 42, sra, 0 );
  TEST_RR_ZERODEST( 43, sra, 1024, 2048 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
