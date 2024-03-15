/*
 * Doc.h
 *
 * Memory allocation routines
 *
 * (C) 2006, Kenneth Roe
 *
 * Confidential and proprietary information.  May not be used or distributed
 * except as stated in an agreement controlling such use and distribution.
 */
#define GDEF(x)

#ifdef FAST
#define LDEF(s)
#else
extern void LDEF(char *s);
#endif
