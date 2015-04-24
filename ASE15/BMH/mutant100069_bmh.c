#include "bmh.h"

jsint
js_BoyerMooreHorspool(const jschar *text, jsint textlen,
                      const jschar *pat, jsint patlen,
                      jsint start)
{
  jsint i, j, k, m;
  uint8 skip[BMH_CHARSET_SIZE];
  jschar c;

  __CPROVER_assume(0 < patlen && patlen <= BMH_PATLEN_MAX);
  for (i = 0; i < BMH_CHARSET_SIZE; i++)
    skip[i] = (uint8)patlen;
  m = patlen - 1;
  for (i = 0; i < m; i++) {
    c = pat[i];
    if (c >= BMH_CHARSET_SIZE)
      return BMH_BAD_PATTERN;
    skip[c] = (uint8)(m - i);
  }
  for (k = start + m;
       k < textlen;
       k += ((c = text[k]) >= BMH_CHARSET_SIZE) ? patlen : skip[c]) {
    for (i = k, j = m; ; i--, j--) {
 /* MUTANT (rep_const) */      if (j < 1)
	return i + 1;
      if (text[i] != pat[j])
	break;
    }
  }
  return -1;
}
