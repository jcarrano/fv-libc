/*
 * memchr.c
 */

#include <string.h>
#include <stddef.h>

/* NOTE: Frama-C is having some trouble with unsigned char, so we will use
   signed chars instead. It should not change anything.
 */
void *memchr(const void *s, int c, size_t n)
{
	const char *sp = s;
	/*@ ghost size_t i = 0;
	          char cc = c;
	 */

	/*@
	  loop assigns n, i, sp;
	  loop invariant index: sp ≡ \at(sp, LoopEntry) + i;
	  loop invariant index2: n ≡ \at(n, Pre) - i;
	  loop invariant ∀ size_t j; 0 ≤ j < i ⇒ \at(sp, LoopEntry)[j] ≢ cc;
	 */
	while (n--) {
		if (*sp == (char)c)
			return (void *)sp;
		sp++;
		/*@ ghost i++; */
	}

	return NULL;
}
