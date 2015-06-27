# See LICENSE for license details.

#*****************************************************************************
# mulhsu.S
#-----------------------------------------------------------------------------
#
# Test mulhsu instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2,  mulhsu, 0x00000000, 0x00000000, 0x00000000 );
  TEST_RR_OP( 3,  mulhsu, 0x00000000, 0x00000001, 0x00000001 );
  TEST_RR_OP( 4,  mulhsu, 0x00000000, 0x00000003, 0x00000007 );

  TEST_RR_OP( 5,  mulhsu, 0x00000000, 0x00000000, 0xffff8000 );
  TEST_RR_OP( 6,  mulhsu, 0x00000000, 0x80000000, 0x00000000 );
  TEST_RR_OP( 7,  mulhsu, 0x80004000, 0x80000000, 0xffff8000 );

  TEST_RR_OP(30,  mulhsu, 0xffff0081, 0xaaaaaaab, 0x0002fe7d );
  TEST_RR_OP(31,  mulhsu, 0x0001fefe, 0x0002fe7d, 0xaaaaaaab );

  TEST_RR_OP(32,  mulhsu, 0xff010000, 0xff000000, 0xff000000 );

  TEST_RR_OP(33,  mulhsu, 0xffffffff, 0xffffffff, 0xffffffff );
  TEST_RR_OP(34,  mulhsu, 0xffffffff, 0xffffffff, 0x00000001 );
  TEST_RR_OP(35,  mulhsu, 0x00000000, 0x00000001, 0xffffffff );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_RR_SRC1_EQ_DEST( 8, mulhsu, 36608, 13<<20, 11<<20 );
  TEST_RR_SRC2_EQ_DEST( 9, mulhsu, 39424, 14<<20, 11<<20 );
  TEST_RR_SRC12_EQ_DEST( 10, mulhsu, 43264, 13<<20 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_RR_DEST_BYPASS( 11, 0, mulhsu, 36608, 13<<20, 11<<20 );
  TEST_RR_DEST_BYPASS( 12, 1, mulhsu, 39424, 14<<20, 11<<20 );
  TEST_RR_DEST_BYPASS( 13, 2, mulhsu, 42240, 15<<20, 11<<20 );

  TEST_RR_SRC12_BYPASS( 14, 0, 0, mulhsu, 36608, 13<<20, 11<<20 );
  TEST_RR_SRC12_BYPASS( 15, 0, 1, mulhsu, 39424, 14<<20, 11<<20 );
  TEST_RR_SRC12_BYPASS( 16, 0, 2, mulhsu, 42240, 15<<20, 11<<20 );
  TEST_RR_SRC12_BYPASS( 17, 1, 0, mulhsu, 36608, 13<<20, 11<<20 );
  TEST_RR_SRC12_BYPASS( 18, 1, 1, mulhsu, 39424, 14<<20, 11<<20 );
  TEST_RR_SRC12_BYPASS( 19, 2, 0, mulhsu, 42240, 15<<20, 11<<20 );

  TEST_RR_SRC21_BYPASS( 20, 0, 0, mulhsu, 36608, 13<<20, 11<<20 );
  TEST_RR_SRC21_BYPASS( 21, 0, 1, mulhsu, 39424, 14<<20, 11<<20 );
  TEST_RR_SRC21_BYPASS( 22, 0, 2, mulhsu, 42240, 15<<20, 11<<20 );
  TEST_RR_SRC21_BYPASS( 23, 1, 0, mulhsu, 36608, 13<<20, 11<<20 );
  TEST_RR_SRC21_BYPASS( 24, 1, 1, mulhsu, 39424, 14<<20, 11<<20 );
  TEST_RR_SRC21_BYPASS( 25, 2, 0, mulhsu, 42240, 15<<20, 11<<20 );

  TEST_RR_ZEROSRC1( 26, mulhsu, 0, 31<<26 );
  TEST_RR_ZEROSRC2( 27, mulhsu, 0, 32<<26 );
  TEST_RR_ZEROSRC12( 28, mulhsu, 0 );
  TEST_RR_ZERODEST( 29, mulhsu, 33<<20, 34<<20 );



  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
