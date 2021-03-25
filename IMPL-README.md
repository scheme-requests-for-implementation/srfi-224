# Integer Mappings

This is an implementation of integer mappings for R7RS Scheme.
See the pre-SRFI document (currently named `integer-map.html`)
for more details.

# Tests

There are several ways to run the provided tests.  On a Scheme which
provides SRFI 64 or 78, load the library, then either
`test-srfi-64.scm` or `test-srfi-78.scm`, respectively.

The implementation has primarily been tested with chibi-scheme.
To run the tests on chibi, execute:

    chibi-scheme -D debug test-chibi.scm

More test shims may be added in the future.
