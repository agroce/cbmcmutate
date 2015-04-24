#ifndef BHM_H
#define BHM_H

#define BMH_CHARSET_SIZE CSIZE
#define BMH_PATLEN_MAX PSIZE
#define BMH_BAD_PATTERN -1

typedef char jschar;
typedef int jsint;
typedef unsigned char uint8;

jsint
js_BoyerMooreHorspool(const jschar *text, jsint textlen,
                      const jschar *pat, jsint patlen,
                      jsint start);

#endif
