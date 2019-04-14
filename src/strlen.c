/*
 * strlen()
 *
 * Copyright (c) 2019 Juan I. Carrano
 * See LICENSE in the root directory for other contributors.
 *
 * SPDX-License-Identifier: BSD-3-CLAUSE
 */

#include <string.h>

size_t strlen(const char *s)
{
	const char *ss = s;
	/*@ ghost size_t i = 0; */

	/*@
	  loop assigns ss, i;
	  loop invariant ss ≡ s + i;
	  loop invariant string_length(s) == i + string_length(ss);
	  loop invariant ∀ size_t j; 0 ≤ j < i ⇒ s[j] ≢ 0;
	 */
	while (*ss) {
		ss++;
		/*@ ghost i++; */
	}

	return ss - s;
}
