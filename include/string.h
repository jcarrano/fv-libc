/*
 * string.h
 *
 * Copyright (c) 2019 Juan I. Carrano
 * See LICENSE in the root directory for other contributors.
 *
 * SPDX-License-Identifier: BSD-3-CLAUSE
 */

#ifndef _STRING_H
#define _STRING_H

#include <klibc/extern.h>
#include <stddef.h>
#include <stdint.h>

/*@
  predicate valid_string(char *s, size_t len) =
				   \valid(s + (0..len)) ∧ s[len] ≡ 0;

  predicate valid_string(char *s) = ∃ size_t term_idx;
				   \valid(s + (0..term_idx)) ∧ s[term_idx] ≡ 0;

  predicate valid_string_read(char *s, size_t len) =
			      \valid_read(s + (0..len)) ∧ s[len] ≡ 0;

  predicate valid_string_read(char *s) = ∃ size_t term_idx;
			      \valid_read(s + (0..term_idx)) ∧ s[term_idx] ≡ 0;

  predicate s_terminated{L}(char *s) = ∃ size_t term_idx; s[term_idx] ≡ 0;

  logic ℤ string_length{L}(char *s) = ((*s ≡ 0)?  0 : 1 + string_length(s+1));

  predicate memory_equal{Lx, Ly}(void *x, void *y, ℤ size) =
	∀ size_t i; 0 ≤ i < size ⇒ \at(((char*)x)[i], Lx) ≡ \at(((char*)y)[i], Ly);

  predicate string_equal{Lx, Ly}(char *x, char *y) = ∃ size_t term_idx;
	term_idx ≥ 0 ∧ memory_equal{Lx, Ly}(x, y, term_idx+1)
	∧ \at(x[term_idx], Lx) ≡ 0;
*/

/*@
  // NOTE: Frama-C is having some trouble with unsigned char, so we will use
  // signed chars instead. It should not change anything.
  requires \valid_read((char*)s + (0..n-1));

  assigns \nothing;

  behavior find:
	assumes (char)c ∈ ((char*)s)[0..n-1];

	ensures matches: *(char*)\result ≡ (char)c;
	ensures within_bounds: (char*)s ≤ (char*)\result < (char*)s + n;
	ensures is_first: ∀ size_t i; (char*)s + i < (char*)\result
	                               ⇒ ((char*)s)[i] ≢ (char)c;

  behavior no_find:
	assumes ¬ ((char)c ∈ ((char*)s)[0..n-1]);

	ensures \result ≡ NULL;

  complete behaviors;
  disjoint behaviors;
*/
__extern void *memchr(const void *s, int c, size_t n);
__extern void *memrchr(const void *, int, size_t);
__extern int memcmp(const void *, const void *, size_t);

/*@
  requires \valid_read((char*)src + (0..n-1));
  requires \valid((char*)dst + (0..n-1));
  requires \separated((char*)src + (0..n-1), (char*)dst + (0..n-1));

  assigns ((char*)dst)[0..n-1];

  ensures memory_equal{Post,Post}(src, dst, n);
  ensures \result ≡ dst;
*/
__extern void *memcpy(void *dst, const void *src, size_t n);
__extern void *memmove(void *, const void *, size_t);

/*@
  requires n ≥ 0;
  requires \valid((char*)dst + (0..n-1));

  assigns ((char*)dst)[0..n-1];

  ensures \result ≡ dst;
  ensures ∀ int i; 0 ≤ i < n ⇒ ((char*)dst)[i] ≡ (char)c;
*/
__extern void *memset(void *dst, int c, size_t n);

/* TODO: nonstandard, remove me. BEGIN LIST OF NONSTANDARD STUFF*/
__extern void *memccpy(void *, const void *, int, size_t);
__extern void *memmem(const void *, size_t, const void *, size_t);
__extern void memswap(void *, void *, size_t);
__extern void bzero(void *, size_t);
/* END LIST OF NONSTANDARD STUFF*/

/* These are POSIX. */
__extern int strcasecmp(const char *, const char *);
__extern int strncasecmp(const char *, const char *, size_t);
__extern char *strcat(char *, const char *);
__extern char *strchr(const char *, int);
__extern char *index(const char *, int);
__extern char *strrchr(const char *, int);
__extern char *rindex(const char *, int);
__extern int strcmp(const char *, const char *);

/*@
  requires valid_string_read(src);
  requires ∀ ℤ i; \valid_read(src + i) ⇒ \valid(dst + i);
  requires \separated(src + (0..string_length(src)), dst + (0..string_length(src)));

  assigns dst[0..string_length{Pre}(src)];

  ensures string_equal{Pre,Post}(src, dst);
  ensures \result ≡ dst;
*/
__extern char * strcpy(char *dst, const char *src);
__extern size_t strcspn(const char *, const char *);
__extern char *strdup(const char *);
__extern char *strndup(const char *, size_t);

/*@
  requires valid_string_read(s);

  assigns \nothing;

  ensures ∀ size_t i; 0 ≤ i < \result ⇒ s[i] ≢ 0;
  ensures s[\result] ≡ 0;
  ensures string_length(s) ≡ \result;
 */
__extern size_t strlen(const char *s);

/*@
  requires \valid_read(s + (0..maxlen-1));

  assigns \nothing;

  ensures ∀ size_t i; 0 ≤ i < \result ⇒ s[i] ≢ 0;
  ensures \result ≤ maxlen;
  ensures s[\result] ≡ 0 ∨ \result ≡ maxlen;
 */
__extern size_t strnlen(const char *s, size_t maxlen);

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
