/*
 * string.h
 */

#ifndef _STRING_H
#define _STRING_H

#include <klibc/extern.h>
#include <stddef.h>

/*@
  predicate valid_string(char *s) = ∃ size_t term_idx;
				   \valid(s + (0..term_idx)) ∧ s[term_idx] ≡ 0;
  predicate valid_string_read(char *s) = ∃ size_t term_idx;
			      \valid_read(s + (0..term_idx)) ∧ s[term_idx] ≡ 0;

*/

__extern void *memccpy(void *, const void *, int, size_t);
__extern void *memchr(const void *, int, size_t);
__extern void *memrchr(const void *, int, size_t);
__extern int memcmp(const void *, const void *, size_t);
__extern void *memcpy(void *, const void *, size_t);
__extern void *memmove(void *, const void *, size_t);
__extern void *memset(void *, int, size_t);
__extern void *memmem(const void *, size_t, const void *, size_t);
__extern void memswap(void *, void *, size_t);
__extern void bzero(void *, size_t);
__extern int strcasecmp(const char *, const char *);
__extern int strncasecmp(const char *, const char *, size_t);
__extern char *strcat(char *, const char *);
__extern char *strchr(const char *, int);
__extern char *index(const char *, int);
__extern char *strrchr(const char *, int);
__extern char *rindex(const char *, int);
__extern int strcmp(const char *, const char *);
__extern char *strcpy(char *, const char *);
__extern size_t strcspn(const char *, const char *);
__extern char *strdup(const char *);
__extern char *strndup(const char *, size_t);

/*@
  requires valid_string_read(s);

  assigns \nothing;

  ensures ∀ size_t i; 0 ≤ i < \result ⇒ s[i] ≢ 0;
  ensures s[\result] ≡ 0;
 */
__extern size_t strlen(const char *s);

__extern size_t strnlen(const char *, size_t);
__extern char *strncat(char *, const char *, size_t);
__extern size_t strlcat(char *, const char *, size_t);
__extern int strncmp(const char *, const char *, size_t);
__extern char *strncpy(char *, const char *, size_t);
__extern size_t strlcpy(char *, const char *, size_t);
__extern char *strpbrk(const char *, const char *);
__extern char *strsep(char **, const char *);
__extern size_t strspn(const char *, const char *);
__extern char *strstr(const char *, const char *);
__extern char *strtok(char *, const char *);
__extern char *strtok_r(char *, const char *, char **);

#ifndef FRAMAC_SOURCE

/* Some dummy functions to avoid errors with C++ cstring */
inline static int strcoll(const char *s1, const char *s2)
{
	return strcmp(s1, s2);
}

inline static size_t strxfrm(char *dest, const char *src, size_t n)
{
	strncpy(dest, src, n);
	return strlen(src);
}

#endif	/* FRAMAC_SOURCE */

#endif				/* _STRING_H */
