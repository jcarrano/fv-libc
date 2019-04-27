/*
 * memset.c
 *
 * Copyright (c) 2019 Juan I. Carrano
 * See LICENSE in the root directory for other contributors.
 *
 * SPDX-License-Identifier: BSD-3-CLAUSE
 */

#include <string.h>
/* #include <stdint.h> */

void *memset(void *dst, int c, size_t n)
{
	char *q = dst;
	/*@ ghost size_t i = 0; */

/* // We cannot prove assembly, so disable this.
#if defined(__i386__)
	size_t nl = n >> 2;
	asm volatile ("cld ; rep ; stosl ; movl %3,%0 ; rep ; stosb"
		      : "+c" (nl), "+D" (q)
		      : "a" ((unsigned char)c * 0x01010101U), "r" (n & 3));
#elif defined(__x86_64__)
	size_t nq = n >> 3;
	asm volatile ("cld ; rep ; stosq ; movl %3,%%ecx ; rep ; stosb"
		      :"+c" (nq), "+D" (q)
		      : "a" ((unsigned char)c * 0x0101010101010101U),
			"r" ((uint32_t) n & 7));
#else
*/

	/*@
	  loop assigns n, q, i;
	  loop assigns ((char*)dst)[0..\at(n, Pre)-n-1];
	  loop invariant index: q ≡ ((char*)dst) + i;
	  loop invariant index2: n ≡ \at(n, Pre) - i;
	  loop invariant set: ∀ size_t j; 0 ≤ j < i ⇒ ((char*)dst)[j] ≡ (char)c;
	 */
	while (n--) {
		*q++ = c;
		/*@ ghost i++; */
	}

/*#endif*/

	return dst;
}
