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

   ;; Predicates
   imapping? imapping-contains? imapping-empty? imapping-disjoint?

   ;; Accessors
   imapping-min imapping-max imapping-lookup imapping-ref
   imapping-ref/default

   ;; Updaters
   imapping-adjoin imapping-adjoin/combinator imapping-adjust
   imapping-adjust/key imapping-adjoin! imapping-adjoin/combinator!
   imapping-set imapping-set!
   imapping-adjust! imapping-adjust/key! imapping-delete
   imapping-delete-all imapping-alter imapping-update
   imapping-update/key imapping-delete! imapping-delete-all!
   imapping-alter! imapping-update! imapping-update/key!
   imapping-delete-min imapping-delete-max imapping-update-min
   imapping-update-max imapping-update-min/key imapping-update-max/key
   imapping-pop-min imapping-pop-max imapping-delete-min!
   imapping-delete-max! imapping-update-min! imapping-update-max!
   imapping-update-min/key! imapping-update-max/key!
   imapping-pop-min! imapping-pop-max!

   ;; The whole imapping
   imapping-size imapping-count imapping-count/key imapping-any?
   imapping-every?

   ;; Traversal
   imapping-fold imapping-fold-right imapping-fold/key
   imapping-fold-right/key imapping-map imapping-map/key imapping-map->list
   imapping-map/key->list imapping-for-each imapping-for-each/key
   imapping-filter-map imapping-filter-map/key imapping-filter-map!
   imapping-filter-map/key! imapping-map-either imapping-map-either/key
   imapping-map-either! imapping-map-either/key!
   imapping-relation-map

   ;; Filter
   imapping-filter imapping-filter/key imapping-remove imapping-remove/key
   imapping-partition imapping-partition/key
   imapping-filter! imapping-filter/key! imapping-remove!
   imapping-remove/key! imapping-partition! imapping-partition/key!

   ;; Copying and conversion
   imapping-keys imapping-values imapping-copy
   imapping->alist imapping->decreasing-alist imapping->generator
   imapping->decreasing-generator

   ;; Comparison
   imapping=? imapping<? imapping>? imapping<=? imapping>=?

   ;; Set theory operations
   imapping-union imapping-intersection imapping-difference imapping-xor
   imapping-union! imapping-intersection! imapping-difference! imapping-xor!
   imapping-union/combinator imapping-intersection/combinator
   imapping-union/combinator! imapping-intersection/combinator!

   ;; Submappings
   imapping-open-interval imapping-closed-interval
   imapping-open-closed-interval imapping-closed-open-interval
   imapping-open-interval! imapping-closed-interval!
   imapping-open-closed-interval! imapping-closed-open-interval!
   isubmapping= isubmapping< isubmapping<= isubmapping>= isubmapping>
   isubmapping=! isubmapping<! isubmapping<=! isubmapping>=!
   isubmapping>!
   imapping-split
   )

  (include "matchers.scm")
  (include "trie.scm")
  (include "224.scm"))
