#include "bmh.h"

int nondet_int();
unsigned int nondet_uint();

int main() {
  int i;
  unsigned int v;

  char itext[TSIZE];
  char ipat[PSIZE];

  unsigned int itext_s = nondet_uint();
  __CPROVER_assume(itext_s < TSIZE);
  unsigned int ipat_s = nondet_uint();
  __CPROVER_assume(ipat_s < PSIZE);

  printf ("LOG: text size = %u, pat size = %u\n", itext_s, ipat_s);

  for (i = 0; i < itext_s; i++) {
    v = nondet_unit();
    __CPROVER_assume((long)v < (long)BMH_CHARSET_SIZE);
    itext[i] = v;
    printf ("LOG: text[%d] = %u\n", i, itext[i]);
    __CPROVER_assume(itext[i] < BMH_CHARSET_SIZE);
  }

  for (i = 0; i < ipat_s; i++) {
    v = nondet_uint();
    __CPROVER_assume((long)v < (long)BMH_CHARSET_SIZE);
    ipat[i] = v;
    printf ("LOG: pat[%d] = %u\n", i, ipat[i]);
    __CPROVER_assume(ipat[i] < BMH_CHARSET_SIZE);
  }

  jsint r = js_BoyerMooreHorspool(itext, itext_s, ipat, ipat_s, 0);

  printf ("LOG: return = %d\n", r);
  
  if (r == -1) {
    v = nondet_uint();
    printf ("LOG: looking at %u\n", v);
    __CPROVER_assume(v < itext_s);
    int pos = v;
    int ppos = 0;
    int found = 1;
    while (ppos < ipat_s) {
      if (pos >= itext_s) {
	found = 0;
	break;
      }
      if (itext[pos] != ipat[ppos]) {
	found = 0;
	break;
      }
      pos++;
      ppos++;
    }
    __CPROVER_assume (!found);
  } else {
    int pos = r;
    int ppos = 0;
    while (ppos < ipat_s) {
      __CPROVER_assume (itext[pos] == ipat[ppos]);
      pos++;
      ppos++;
    }
  }
  assert(0);
}
