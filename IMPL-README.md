# Integer Mappings

This is an implementation of SRFI 224 integer mappings for R7RS Scheme.
See the SRFI document (`srfi-224.html`) for more details.

# Dependencies

SRFIs 1, 128, 143, 158, 189, and 217 are required.  SRFI 145 is an
optional dependency.

# Tests

There are several ways to run the provided tests.  On a Scheme which
provides SRFI 64 or 78, load the library, then either
`test-srfi-64.scm` or `test-srfi-78.scm`, respectively.

Test shims are also provided for chibi-scheme and CHICKEN.
More test shims may be added in the future.

## chibi-scheme

The chibi-scheme test shim uses the `(chibi test)` library.

From the top directory, execute

    chibi-scheme -D debug test-chibi.scm

## CHICKEN

The CHICKEN test shim uses the popular `test` egg.  To run the
implementation on CHICKEN, the `r7rs` egg must also be loaded.

First, cd to the `srfi/` directory and execute

    csi -R r7rs 224.sld

then evaluate

    ,l ../test-chicken.scm
