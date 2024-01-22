#include <stdio.h>

int main ()
{
     unsigned int I, I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11, I12, I13, I14, I15, I16;
     unsigned int J, J1, J2, J3, J4, J5, J6, J7, J8, J9, J10, J11, J12, J13, J14, J15, J16;
     unsigned int K, K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, K13, K14, K15, K16; 
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

	       K = I + J;

	       K1 = (K & 32768) ? 1 : 0;
	       K2 = (K & 16384) ? 1 : 0;
	       K3 = (K & 8192) ? 1 : 0;
	       K4 = (K & 4096) ? 1 : 0;
	       K5 = (K & 2048) ? 1 : 0;
	       K6 = (K & 1024) ? 1 : 0;
	       K7 = (K & 512) ? 1 : 0;
	       K8 = (K & 256) ? 1 : 0;
	       K9 = (K & 128) ? 1 : 0;
	       K10 = (K & 64) ? 1 : 0;
	       K11 = (K & 32) ? 1 : 0;
	       K12 = (K & 16) ? 1 : 0;
	       K13 = (K & 8) ? 1 : 0;
	       K14 = (K & 4) ? 1 : 0;
	       K15 = (K & 2) ? 1 : 0;
	       K16 = (K & 1) ? 1 : 0;

	       printf ("get normal form for: andBool (eqHalf (addHalf (buildHalf (buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X)), buildHalf (buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X))), buildHalf (buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X))), ",
		    I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11, I12, I13, I14, I15, I16, J1, J2, J3, J4, J5, J6, J7, J8, J9, J10, J11, J12, J13, J14, J15, J16, K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, K13, K14, K15, K16);

	       printf ("eqHalf (addHalf (buildHalf (buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X)), buildHalf (buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X))), buildHalf (buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X))))\n\n",
		    J1, J2, J3, J4, J5, J6, J7, J8, J9, J10, J11, J12, J13, J14, J15, J16, I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11, I12, I13, I14, I15, I16, K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, K13, K14, K15, K16);
	  }
}
