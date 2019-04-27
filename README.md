FV-Libc
=======

This is an attempt at a formally-verified variant of klibc/baselibc.

It is directly derived from Baselibc, which is a fork of klibc with GPL code
removed and tinyprintf.

Verification is being carried out using Frama-C/WP and ACSL. See
https://frama-c.com/index.html for more information.


# Targets

Just like Baselibc, this library targets small microcontrollers and deeply
embedded systems. Therefore it is _not_ an objective to support POSIX system
calls.

# Goals

- Have all non I/O functions fully verified.
- For functions that require I/O (and thus some board support or os support)
  have at least the specification for functions that should be provided.
- Have something that is usable as a stand-alone C library (i.e., no need for
  newlib or any of that stuff.)
- Keep the original C code as is: the way klibc is written makes it harder to
  verify, but that's the challenge.
- Be independent of other C libraries' headers (using the compiler provided
  headers is OK). This includes Frama-C headers too.

# Non goals

Things I will _not_ do:

- Support non C99 functions: this means no POSIX and no non-standard stuff.
- Architecture or OS-specific code if not _strictly_ needed: this means NO board
  support packages.

# Usage / Building

## Requirements

In addition to a compiler, you need Frama-C / Alt-Ergo. The easiest way to get
it is via [OPAM](https://opam.ocaml.org/).

## Building

Typing `make` or `make all` will verify all currently proven files and build
the library, producing a static archive.

`make library` only compiles, while `make proofs` only runs Frama-C/WP without
compiling.

# TODO

- Finish verifying all of string.h.
- Weed out POSIX and BSD functions.
- Add proper Makefiles to run th verification/compile, etc.
- Figure out what's needed to cut dependencies on other C libraries in bare
  metal projects.
- More stuff.
