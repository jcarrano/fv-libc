/*
 * strcpy()
 *
 * Copyright (c) 2019 Juan I. Carrano
 * See LICENSE in the root directory for other contributors.
 *
 * SPDX-License-Identifier: BSD-3-CLAUSE
 */

#include <string.h>

// This one is proving to be veeeery tricky!!!!
char *strcpy(char *dst, const char *src)
{
	char *q = dst;
	const char *p = src;
	char ch;
	/*@ ghost size_t i = 0; */
	/*@ ghost char ch1 = *p; */

	/*@
	  loop assigns q, ch, ch1, p, i;
	  loop assigns dst[0..i-1];
	  loop invariant string_length{Pre}(src) == i + string_length{Pre}(p);
	  loop invariant srcindex: p ≡ src + i;
	  loop invariant dstindex: q ≡ dst + i;
	  loop invariant ∀ integer j; 0 ≤ j < i ⇒ src[j] ≢ 0;
	  loop invariant eq: memory_equal(src, dst, (0..src-p-1));
	  loop invariant separation: \separated(src + (0..i), dst + (0..i));
	 */
	do {
		*q++ = ch = *p++;
		/*@ ghost ch1 = *p; */
		if (!ch)
			break;
		/*@ ghost i++; */
	} while (ch);

	// /*@ assert string_length{Pre}(src) == k; */

	return dst;
}
