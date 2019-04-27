/*
 * memcpy.c
 */

#include <string.h>
#include <stdint.h>

void *memcpy(void *dst, const void *src, size_t n)
{
	const char *p = src;
	char *q = dst;
	/*@ ghost size_t i = 0; */
	/*@ ghost size_t n0 = n; */
/*
#if defined(__i386__)
	size_t nl = n >> 2;
	asm volatile ("cld ; rep ; movsl ; movl %3,%0 ; rep ; movsb":"+c" (nl),
		      "+S"(p), "+D"(q)
		      :"r"(n & 3));
#elif defined(__x86_64__)
	size_t nq = n >> 3;
	asm volatile ("cld ; rep ; movsq ; movl %3,%%ecx ; rep ; movsb":"+c"
		      (nq), "+S"(p), "+D"(q)
		      :"r"((uint32_t) (n & 7)));
#else
*/
	/*@
	 loop assigns n, i, q, p;
	 loop assigns ((char*)dst)[0..n0-n-1];
	 loop invariant bound: 0 ≤ i ≤ n0;
	 loop invariant index: n ≡ n0-i;
	 loop invariant srcindex: p ≡ ((char*)src) + i;
	 loop invariant dstindex: q ≡ ((char*)dst) + i;
	 loop invariant memory_equal{Here, Here}(src, dst, i);
	 */
	while (n--) {
		*q++ = *p++;
		/*@ ghost i++; */
	}

//#endif

	return dst;
}
