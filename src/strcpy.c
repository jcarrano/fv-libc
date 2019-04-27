/*
 * strcpy()
 *
 * Copyright (c) 2019 Juan I. Carrano
 * See LICENSE in the root directory for other contributors.
 *
 * SPDX-License-Identifier: BSD-3-CLAUSE
 */

#include <string.h>

char *strcpy(char *dst, const char *src)
{
	char *q = dst;
	const char *p = src;
	char ch;
	/*@ ghost size_t is; */
	/*@ ghost size_t is0, i = 0; */

	/*@ ghost is = strlen(src); */
	/*@ assert \separated(src + (0..is), dst + (0..is)); */

	/*@ ghost is0 = is; */

	/*@
	 loop assigns is, i, q, p, ch;
	 loop assigns dst[0..is0];
	 loop invariant bound: 0 ≤ i ≤ is0;
	 loop invariant index: is ≡ is0-i;
	 loop invariant srcindex: p ≡ src + i;
	 loop invariant dstindex: q ≡ dst + i;
	 loop invariant memory_equal{Here, Here}(src, dst, i);
	 */
	do {
		*q++ = ch = *p++;
		/*@ ghost i++; */
		/*@ ghost is--; */
	} while (ch);

	return dst;
}
