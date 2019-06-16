/*
 * memcmp.c
 */

#include <string.h>

int memcmp(const void *s1, const void *s2, size_t n)
{
	const char *c1 = s1, *c2 = s2;
	int d = 0;
	/*@ ghost size_t i = 0; */

	/*@
	  loop assigns n, c1, c2, d, i;
	  loop invariant equal: memory_equal_u{Here, Here}(s1, s2, i);
	  loop invariant d == 0;
	  loop invariant index: n ≡ \at(n, LoopEntry) - i;
	  loop invariant bounds: 0 <= i <= \at(n, LoopEntry);
	  loop invariant c1index: c1 ≡ ((char*)s1) + i;
	  loop invariant c2index: c2 ≡ ((char*)s2) + i;
	 */
	while (n--) {
		d = (unsigned char)*c1++ - (unsigned char)*c2++;
		if (d)
			break;
		/*@ ghost i++; */
	}

	return d;
}
