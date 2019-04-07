/*
 * memset.c
 *
 * Copyright (c) 2019 Juan I. Carrano
 * Copyright (c) 2012 Petteri Aimonen
 * Copyright (c) The Regents of the University of California.
 *
 * SPDX-License-Identifier: BSD-3-CLAUSE
 */


/*@
  requires n ≥ 0;
  requires \valid((char*)dst + (0..n-1));

  assigns ((char*)dst)[0..n-1];

  ensures \result ≡ dst;
  ensures ∀ int i; 0 ≤ i < n ⇒ ((char*)dst)[i] ≡ (char)c;
*/
void *memset(void *dst, int c, int n)
{
	char *q = dst;
	/*@ ghost char *q0 = dst;
		  int n0 = n;
		  int i = 0;
	 */

	/*@
	   loop assigns n, i, q, q0[0..n0-1];
	   loop invariant bound: 0 ≤ i ≤ n0;
	   loop invariant index: n ≡ n0-i;
	   loop invariant pointer: q ≡ q0+i;
	   loop invariant ∀ int j; 0 ≤ j < i ⇒ q0[j] ≡ (char)c;
	 */
	while (n--) {
		*q++ = c;
		/*@ ghost i++; */
	}


	return dst;
}
