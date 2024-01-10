#include <stdio.h>

int main ()
{
     unsigned int I, I1, I2, I3, I4, I5, I6, I7, I8;
     unsigned int J, J1, J2, J3, J4, J5, J6, J7, J8;
     unsigned int K, K1, K2, K3, K4, K5, K6, K7, K8;
     unsigned int C, KC;

     for (I = 0; I < 256; I += 3)
	  for (J = 0; J < 256; J += 5)
	       for (C = 0; C <= 1; ++C) {
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

		    K = I + J + C;

		    KC = (K & 256) ? 1 : 0;
		    K1 = (K & 128) ? 1 : 0;
		    K2 = (K & 64) ? 1 : 0;
		    K3 = (K & 32) ? 1 : 0;
		    K4 = (K & 16) ? 1 : 0;
		    K5 = (K & 8) ? 1 : 0;
		    K6 = (K & 4) ? 1 : 0;
		    K7 = (K & 2) ? 1 : 0;
		    K8 = (K & 1) ? 1 : 0;

		    printf ("get normal form for: andBool (eqOctetSum (addOctetSum (buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), x%01X), buildOctetSum (x%01x, buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X))), ", I1, I2, I3, I4, I5, I6, I7, I8, J1, J2, J3, J4, J5, J6, J7, J8, C, KC, K1, K2, K3, K4, K5, K6, K7, K8);

		    printf ("eqOctetSum (addOctetSum (buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X), x%01X), buildOctetSum (x%01x, buildOctet (x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X, x%1X))))\n\n", J1, J2, J3, J4, J5, J6, J7, J8, I1, I2, I3, I4, I5, I6, I7, I8, C, KC, K1, K2, K3, K4, K5, K6, K7, K8);
	       }
}
