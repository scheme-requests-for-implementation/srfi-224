(define-library (srfi 224)
  (import (scheme base)
          (scheme case-lambda)
          (only (srfi 1) fold every)
          (only (srfi 128) comparator? =?)
          (srfi 189)
          (srfi 143)
          (only (srfi 158) make-coroutine-generator)
          (only (srfi 217) list->iset iset-contains?))

  (cond-expand
    ((library (srfi 145))
     (import (srfi 145)))
    (else
     (begin
      (define-syntax assume
        (syntax-rules ()
          ((_ expr . _)
           (or expr (car 0))))))))

  (export
   ;; Constructors
   fxmapping fxmapping-unfold fxmapping-unfold-maybe alist->fxmapping
   alist->fxmapping/combinator

   ;; Predicates
   fxmapping? fxmapping-contains? fxmapping-empty? fxmapping-disjoint?

   ;; Accessors
   fxmapping-min fxmapping-max fxmapping-lookup fxmapping-ref
   fxmapping-lookup-min fxmapping-lookup-max fxmapping-ref/default

   ;; Updaters
   fxmapping-adjoin fxmapping-adjoin/combinator fxmapping-adjust
   fxmapping-set fxmapping-delete fxmapping-delete-all fxmapping-alter
   fxmapping-update fxmapping-delete-min fxmapping-delete-max
   fxmapping-update-min fxmapping-update-max fxmapping-pop-min
   fxmapping-pop-max

   ;; The whole fxmapping
   fxmapping-size fxmapping-count fxmapping-any? fxmapping-find
   fxmapping-query fxmapping-every?

   ;; Traversal
   fxmapping-fold fxmapping-fold-right fxmapping-map fxmapping-map->list
   fxmapping-for-each fxmapping-filter-map fxmapping-map-either
   fxmapping-relation-map

   ;; Filter
   fxmapping-filter fxmapping-remove fxmapping-partition

   ;; Copying and conversion
   fxmapping-keys fxmapping-values fxmapping->alist
   fxmapping->decreasing-alist fxmapping->generator
   fxmapping->decreasing-generator

   ;; Comparison
   fxmapping=? fxmapping<? fxmapping>? fxmapping<=? fxmapping>=?

   ;; Set theory operations
   fxmapping-union fxmapping-intersection fxmapping-difference fxmapping-xor
   fxmapping-union/combinator fxmapping-intersection/combinator

   ;; Submappings
   fxmapping-open-interval fxmapping-closed-interval
   fxmapping-open-closed-interval fxmapping-closed-open-interval
   fxsubmapping= fxsubmapping< fxsubmapping<= fxsubmapping>= fxsubmapping>
   fxmapping-split
   )

  (include "matchers.scm")
  (include "trie.scm")
  (include "224.scm"))
