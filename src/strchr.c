/*
 * strchr.c
 */

#include <string.h>

char *strchr(const char *s, int c)
{
	/*@ ghost size_t i = 0;
		  size_t n = strlen(s);
		  const char *s0 = s;
	 */

	/*@
	  loop assigns s, i;
	  loop invariant length: string_length(s0) == i + string_length(s);
	  loop invariant index: s == s0 + i;
	  loop invariant ∀ size_t j; 0 ≤ j < i ⇒ s0[j] ≢ (char)c && s0[j] ≢ 0;
	 */
	while (*s != (char)c) {
		if (!*s)
			return NULL;
		s++;
		/*@ ghost i++; */
	}

	return (char *)s;
}

