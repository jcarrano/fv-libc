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
	/*@ ghost size_t is = 0; */
	/*@ ghost size_t is0, i = 0; */

	/*@ ghost
	/@@
	  loop assigns is;
	  loop invariant t1: string_length(src) == is + string_length(src+is);
	  loop invariant t2: ∀ size_t j; 0 ≤ j < is ⇒ src[j] ≢ 0;
	  loop invariant t3: \separated(src + (0..is), dst + (0..is));
	 @/
	while(src[is]) {
		is++;
	}
	*/

	/*@ assert is == string_length(src); */
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
