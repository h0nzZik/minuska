#include <stdio.h>

int main ()
{
     unsigned int I, I1, I2, I3, I4, I5, I6, I7, I8;
     unsigned int J, J1, J2, J3, J4, J5, J6, J7, J8;
     unsigned int H, H1, H2, H3, H4, H5, H6, H7, H8;
     unsigned int L, L1, L2, L3, L4, L5, L6, L7, L8;

     for (I = 0; I < 256; I += 3)
	  for (J = 0; J < 256; J += 5) {
	       I1 = (I & 128) ? 1 : 0;
	       I2 = (I & 64) ? 1 : 0;
	       I3 = (I & 32) ? 1 : 0;
	       I4 = (I & 16) ? 1 : 0;
	       I5 = (I & 8) ? 1 : 0;
	       I6 = (I & 4) ? 1 : 0;
	       I7 = (I & 2) ? 1 : 0;
	       I8 = (I & 1) ? 1 : 0;

	       J1 = (J & 128) ? 1 : 0;
	       J2 = (J & 64) ? 1 : 0;
	       J3 = (J & 32) ? 1 : 0;
	       J4 = (J & 16) ? 1 : 0;
	       J5 = (J & 8) ? 1 : 0;
	       J6 = (J & 4) ? 1 : 0;
	       J7 = (J & 2) ? 1 : 0;
	       J8 = (J & 1) ? 1 : 0;

	       H = ((I * J) >> 8) & 0xFF;
	       L = (I * J) & 0xFF;

	       H1 = (H & 128) ? 1 : 0;
	       H2 = (H & 64) ? 1 : 0;
	       H3 = (H & 32) ? 1 : 0;
	       H4 = (H & 16) ? 1 : 0;
	       H5 = (H & 8) ? 1 : 0;
	       H6 = (H & 4) ? 1 : 0;
	       H7 = (H & 2) ? 1 : 0;
	       H8 = (H & 1) ? 1 : 0;

	       L1 = (L & 128) ? 1 : 0;
	       L2 = (L & 64) ? 1 : 0;
	       L3 = (L & 32) ? 1 : 0;
	       L4 = (L & 16) ? 1 : 0;
	       L5 = (L & 8) ? 1 : 0;
	       L6 = (L & 4) ? 1 : 0;
	       L7 = (L & 2) ? 1 : 0;
	       L8 = (L & 1) ? 1 : 0;


	       printf ("get normal form for: testMulOctet (buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X))\n\n", I1, I2, I3, I4, I5, I6, I7, I8, J1, J2, J3, J4, J5, J6, J7, J8, H1, H2, H3, H4, H5, H6, H7, H8, L1, L2, L3, L4, L5, L6, L7, L8);
	  }
}
