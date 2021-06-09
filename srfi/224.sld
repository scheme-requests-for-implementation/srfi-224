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
   imapping imapping-unfold imapping-unfold-maybe alist->imapping
   alist->imapping/combinator

   ;; Predicates
   imapping? imapping-contains? imapping-empty? imapping-disjoint?

   ;; Accessors
   imapping-min imapping-max imapping-lookup imapping-ref
   imapping-lookup-min imapping-lookup-max imapping-ref/default

   ;; Updaters
   imapping-adjoin imapping-adjoin/combinator imapping-adjust
   imapping-set imapping-delete imapping-delete-all imapping-alter
   imapping-update imapping-delete-min imapping-delete-max
   imapping-update-min imapping-update-max imapping-pop-min
   imapping-pop-max

   ;; The whole imapping
   imapping-size imapping-count imapping-any? imapping-find
   imapping-query imapping-every?

   ;; Traversal
   imapping-fold imapping-fold-right imapping-map imapping-map->list
   imapping-for-each imapping-filter-map imapping-map-either
   imapping-relation-map

   ;; Filter
   imapping-filter imapping-remove imapping-partition

   ;; Copying and conversion
   imapping-keys imapping-values imapping-copy imapping->alist
   imapping->decreasing-alist imapping->generator
   imapping->decreasing-generator

   ;; Comparison
   imapping=? imapping<? imapping>? imapping<=? imapping>=?

   ;; Set theory operations
   imapping-union imapping-intersection imapping-difference imapping-xor
   imapping-union/combinator imapping-intersection/combinator

   ;; Submappings
   imapping-open-interval imapping-closed-interval
   imapping-open-closed-interval imapping-closed-open-interval
   isubmapping= isubmapping< isubmapping<= isubmapping>= isubmapping>
   imapping-split
   )

  (include "matchers.scm")
  (include "trie.scm")
  (include "224.scm"))
