#include <stdio.h>

int main ()
{
     unsigned int I, I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11, I12, I13, I14, I15, I16;
     unsigned int J, J1, J2, J3, J4, J5, J6, J7, J8, J9, J10, J11, J12, J13, J14, J15, J16;
     unsigned int H, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16; 
     unsigned int L, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, L12, L13, L14, L15, L16; 
     for (I = 0; I < 65536; I += 767)
	  for (J = 0; J < 65536; J += 1279) {
	       I1 = (I & 32768) ? 1 : 0;
	       I2 = (I & 16384) ? 1 : 0;
	       I3 = (I & 8192) ? 1 : 0;
	       I4 = (I & 4096) ? 1 : 0;
	       I5 = (I & 2048) ? 1 : 0;
	       I6 = (I & 1024) ? 1 : 0;
	       I7 = (I & 512) ? 1 : 0;
	       I8 = (I & 256) ? 1 : 0;
	       I9 = (I & 128) ? 1 : 0;
	       I10 = (I & 64) ? 1 : 0;
	       I11 = (I & 32) ? 1 : 0;
	       I12 = (I & 16) ? 1 : 0;
	       I13 = (I & 8) ? 1 : 0;
	       I14 = (I & 4) ? 1 : 0;
	       I15 = (I & 2) ? 1 : 0;
	       I16 = (I & 1) ? 1 : 0;

	       J1 = (J & 32768) ? 1 : 0;
	       J2 = (J & 16384) ? 1 : 0;
	       J3 = (J & 8192) ? 1 : 0;
	       J4 = (J & 4096) ? 1 : 0;
	       J5 = (J & 2048) ? 1 : 0;
	       J6 = (J & 1024) ? 1 : 0;
	       J7 = (J & 512) ? 1 : 0;
	       J8 = (J & 256) ? 1 : 0;
	       J9 = (J & 128) ? 1 : 0;
	       J10 = (J & 64) ? 1 : 0;
	       J11 = (J & 32) ? 1 : 0;
	       J12 = (J & 16) ? 1 : 0;
	       J13 = (J & 8) ? 1 : 0;
	       J14 = (J & 4) ? 1 : 0;
	       J15 = (J & 2) ? 1 : 0;
	       J16 = (J & 1) ? 1 : 0;

	       H = ((I * J) >> 16) & 0xFFFF;

	       H1 = (H & 32768) ? 1 : 0;
	       H2 = (H & 16384) ? 1 : 0;
	       H3 = (H & 8192) ? 1 : 0;
	       H4 = (H & 4096) ? 1 : 0;
	       H5 = (H & 2048) ? 1 : 0;
	       H6 = (H & 1024) ? 1 : 0;
	       H7 = (H & 512) ? 1 : 0;
	       H8 = (H & 256) ? 1 : 0;
	       H9 = (H & 128) ? 1 : 0;
	       H10 = (H & 64) ? 1 : 0;
	       H11 = (H & 32) ? 1 : 0;
	       H12 = (H & 16) ? 1 : 0;
	       H13 = (H & 8) ? 1 : 0;
	       H14 = (H & 4) ? 1 : 0;
	       H15 = (H & 2) ? 1 : 0;
	       H16 = (H & 1) ? 1 : 0;

	       L = (I * J) & 0xFFFF;

	       L1 = (L & 32768) ? 1 : 0;
	       L2 = (L & 16384) ? 1 : 0;
	       L3 = (L & 8192) ? 1 : 0;
	       L4 = (L & 4096) ? 1 : 0;
	       L5 = (L & 2048) ? 1 : 0;
	       L6 = (L & 1024) ? 1 : 0;
	       L7 = (L & 512) ? 1 : 0;
	       L8 = (L & 256) ? 1 : 0;
	       L9 = (L & 128) ? 1 : 0;
	       L10 = (L & 64) ? 1 : 0;
	       L11 = (L & 32) ? 1 : 0;
	       L12 = (L & 16) ? 1 : 0;
	       L13 = (L & 8) ? 1 : 0;
	       L14 = (L & 4) ? 1 : 0;
	       L15 = (L & 2) ? 1 : 0;
	       L16 = (L & 1) ? 1 : 0;

	       printf ("get normal form for: testMulHalf (buildHalf (buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X)), buildHalf (buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X)), buildBlock (buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X)))\n\n", 
I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11, I12, I13, I14, I15, I16, 
J1, J2, J3, J4, J5, J6, J7, J8, J9, J10, J11, J12, J13, J14, J15, J16, 
H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16,
L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, L12, L13, L14, L15, L16);
	  }
}
