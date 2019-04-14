/*
 * memset.c
 *
 * Copyright (c) 2019 Juan I. Carrano
 * Copyright (c) 2012 Petteri Aimonen
 * Copyright (c) The Regents of the University of California.
 *
 * SPDX-License-Identifier: BSD-3-CLAUSE
 */

#include <string.h>

void *memset(void *dst, int c, size_t n)
{
	char *q = dst;
	/*@ ghost char *q0 = dst;
		  size_t n0 = n;
		  size_t i = 0;
	 */

	//~ /*@
	   //~ loop assigns n, i, q, q0[0..n0-n-1];
	   //~ loop invariant bound: 0 ≤ i ≤ n0;
	   //~ loop invariant index: n ≡ n0-i;
	   //~ loop invariant pointer: q ≡ q0+i;
	   //~ loop invariant ∀ int j; 0 ≤ j < i ⇒ q0[j] ≡ (char)c;
	 //~ */
	//~ while (n--) {
		//~ *q++ = c;
		//~ /*@ ghost i++; */
	//~ }

	if (!n)
		return dst;
	/*@ assert n>0; */

	/*@
	   loop assigns n, i, q, q0[0..n0-n-1];
	   loop invariant bound: 0 ≤ i ≤ n0-1;
	   loop invariant index: n ≡ n0-i;
	   loop invariant pointer: q ≡ q0+i;
	   loop invariant ∀ int j; 0 ≤ j < i ⇒ q0[j] ≡ (char)c;
	 */
	do {
		*q++ = c;
		/*@ ghost i++; */
		n--;
	} while (n);

	return dst;
}
