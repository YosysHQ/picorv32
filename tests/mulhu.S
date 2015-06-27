# See LICENSE for license details.

#*****************************************************************************
# mulhu.S
#-----------------------------------------------------------------------------
#
# Test mulhu instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2,  mulhu, 0x00000000, 0x00000000, 0x00000000 );
  TEST_RR_OP( 3,  mulhu, 0x00000000, 0x00000001, 0x00000001 );
  TEST_RR_OP( 4,  mulhu, 0x00000000, 0x00000003, 0x00000007 );

  TEST_RR_OP( 5,  mulhu, 0x00000000, 0x00000000, 0xffff8000 );
  TEST_RR_OP( 6,  mulhu, 0x00000000, 0x80000000, 0x00000000 );
  TEST_RR_OP( 7,  mulhu, 0x7fffc000, 0x80000000, 0xffff8000 );

  TEST_RR_OP(30,  mulhu, 0x0001fefe, 0xaaaaaaab, 0x0002fe7d );
  TEST_RR_OP(31,  mulhu, 0x0001fefe, 0x0002fe7d, 0xaaaaaaab );

  TEST_RR_OP(32,  mulhu, 0xfe010000, 0xff000000, 0xff000000 );

  TEST_RR_OP(33,  mulhu, 0xfffffffe, 0xffffffff, 0xffffffff );
  TEST_RR_OP(34,  mulhu, 0x00000000, 0xffffffff, 0x00000001 );
  TEST_RR_OP(35,  mulhu, 0x00000000, 0x00000001, 0xffffffff );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_RR_SRC1_EQ_DEST( 8, mulhu, 36608, 13<<20, 11<<20 );
  TEST_RR_SRC2_EQ_DEST( 9, mulhu, 39424, 14<<20, 11<<20 );
  TEST_RR_SRC12_EQ_DEST( 10, mulhu, 43264, 13<<20 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_RR_DEST_BYPASS( 11, 0, mulhu, 36608, 13<<20, 11<<20 );
  TEST_RR_DEST_BYPASS( 12, 1, mulhu, 39424, 14<<20, 11<<20 );
  TEST_RR_DEST_BYPASS( 13, 2, mulhu, 42240, 15<<20, 11<<20 );

  TEST_RR_SRC12_BYPASS( 14, 0, 0, mulhu, 36608, 13<<20, 11<<20 );
  TEST_RR_SRC12_BYPASS( 15, 0, 1, mulhu, 39424, 14<<20, 11<<20 );
  TEST_RR_SRC12_BYPASS( 16, 0, 2, mulhu, 42240, 15<<20, 11<<20 );
  TEST_RR_SRC12_BYPASS( 17, 1, 0, mulhu, 36608, 13<<20, 11<<20 );
  TEST_RR_SRC12_BYPASS( 18, 1, 1, mulhu, 39424, 14<<20, 11<<20 );
  TEST_RR_SRC12_BYPASS( 19, 2, 0, mulhu, 42240, 15<<20, 11<<20 );

  TEST_RR_SRC21_BYPASS( 20, 0, 0, mulhu, 36608, 13<<20, 11<<20 );
  TEST_RR_SRC21_BYPASS( 21, 0, 1, mulhu, 39424, 14<<20, 11<<20 );
  TEST_RR_SRC21_BYPASS( 22, 0, 2, mulhu, 42240, 15<<20, 11<<20 );
  TEST_RR_SRC21_BYPASS( 23, 1, 0, mulhu, 36608, 13<<20, 11<<20 );
  TEST_RR_SRC21_BYPASS( 24, 1, 1, mulhu, 39424, 14<<20, 11<<20 );
  TEST_RR_SRC21_BYPASS( 25, 2, 0, mulhu, 42240, 15<<20, 11<<20 );

  TEST_RR_ZEROSRC1( 26, mulhu, 0, 31<<26 );
  TEST_RR_ZEROSRC2( 27, mulhu, 0, 32<<26 );
  TEST_RR_ZEROSRC12( 28, mulhu, 0 );
  TEST_RR_ZERODEST( 29, mulhu, 33<<20, 34<<20 );


  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
