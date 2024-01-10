
#include <stdio.h>

#define BOUND 10
/* #define DIV */

/* ------------------------------------------------------------------------- */

void print_int (n, SIGNED)
int n;
int SIGNED;
{
     int  i;
     if (SIGNED) {
          if (n < 0) {
	       n = -n - 1;
	       printf ("neg (");
          } else {
	       printf ("pos (");
          }
     }
     for (i = 0; i < n; ++i)
	  printf ("succ (");
     printf ("zero");
     for (i = 0; i < n; ++i)
	  printf (")");
     if (SIGNED) {
          printf (")");
     }
}

/* ------------------------------------------------------------------------- */

void print_check (OP, I, J, K)
char *OP;
int I, J, K;

{
     int SIGNED;

     printf ("%% assert %s (%d, %d) = %d\n", OP, I, J, K);
     printf ("get normal form for: check_%s (", OP);
     SIGNED = (OP [0] == 'i') ? 1 : 0;
     print_int (I, SIGNED);
     printf (", ");
     print_int (J, SIGNED);
     printf (", ");
     print_int (K, SIGNED);
     printf (")\n\n");
}

/* ------------------------------------------------------------------------- */

int main ()
{
     int  I, J, K; 
     for (I = -BOUND; I <= BOUND; ++I)
	  for (J = -BOUND; J <= BOUND; ++J) {
#ifdef DIV
              if ((I >= 0) && (J > 0)) {
                   K = I / J;
		   print_check ("div", I, J, K);
              }
#endif
#ifdef MOD
              if ((I >= 0) && (J > 0)) {
                   K = I % J;
		   print_check ("mod", I, J, K);
              }
#endif
#ifdef IMULT
	       K = I * J;
	       print_check ("imult", I, J, K);
#endif
#ifdef IDIV
	       if (J != 0) {
		    K = (int) (I / J);
		    print_check ("idiv", I, J, K);
	       }
#endif
#ifdef IMOD
	       if (J != 0) {
		    K = I % J;
		    if ((K == 0) || (I * J >= 0)) {
			 /* K is zero or both I and J have the same sign */
			 /* keep K unchanged */
		    } else if (I < 0 && J > 0) {
			 /* assert K < 0 : give K the same sign as J */
			 K += J;
		    } else if (I > 0 && J < 0) {
			 /* assert K > 0 : give K the same sign as J */
			 K += J;
		    }
		    print_check ("imod", I, J, K);
	       }
#endif
#ifdef IREM
	       if (J != 0) {
		    K = I % J;	/* Gcc implements % as rem */
		    print_check ("irem", I, J, K);
	       }
#endif
	  }
}

/* ------------------------------------------------------------------------- */

