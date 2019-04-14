/*
 * strnlen()
 */

#include <string.h>

size_t strnlen(const char *s, size_t maxlen)
{
	const char *ss = s;
	/*@ ghost size_t i = 0; */
	/*@ ghost size_t maxlen0 = maxlen; */

	/*@
	  loop assigns ss, maxlen, i;
	  loop invariant indexing: ss ≡ s + i;
	  loop invariant indexing2: i ≡ maxlen0 - maxlen;
	  loop invariant limit: i ≤ maxlen0;
	  loop invariant firstzero: ∀ size_t j; 0 ≤ j < i ⇒ s[j] ≢ 0;
	 */
	while ((maxlen > 0) && *ss) {
		ss++;
		maxlen--;
		/*@ ghost i++; */
	}
	return ss - s;
}
