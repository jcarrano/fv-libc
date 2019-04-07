/*
 * strlen()
 *
 * Copyright (c) 2019 Juan I. Carrano
 * Copyright (c) 2012 Petteri Aimonen
 * Copyright (c) The Regents of the University of California.
 *
 * SPDX-License-Identifier: BSD-3-CLAUSE
 */

#include <string.h>

/*@
  requires ∃ size_t term_idx; \valid_read(s + (0..term_idx)) ∧ s[term_idx] ≡ 0;

  assigns \nothing;

  ensures ∀ size_t i; 0 ≤ i < \result ⇒ s[i] ≢ 0;
  ensures s[\result] ≡ 0;
 */
size_t strlen(const char *s)
{
	const char *ss = s;
	/*@ ghost size_t i = 0; */

	/*@
	  loop assigns ss, i;
	  loop invariant ss ≡ s + i;
	  loop invariant ∀ size_t j; 0 ≤ j < i ⇒ s[j] ≢ 0;
	 */
	while (*ss) {
		ss++;
		/*@ ghost i++; */
	}

	return ss - s;
}
