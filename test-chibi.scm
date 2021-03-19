;;; Test framework for chibi-scheme.

(import (scheme base)
        (chibi test)
        (srfi 1)
        (srfi 128)
        (srfi 189)
        (srfi 217)
        (integer-map))

;;; SRFI 64 shim

;; chibi's test-equal is not SRFI 64's test-equal.
(define-syntax test-equal
  (syntax-rules ()
    ((test-equal . rest)
     (test . rest))))

(define-syntax test-eqv
  (syntax-rules ()
    ((test-eqv . rest)
     (test-equal eqv? . rest))))

(include "test-body.scm")
