;;; Copyright (C) 2020 Wolfgang Corcoran-Mathe
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining a
;;; copy of this software and associated documentation files (the
;;; "Software"), to deal in the Software without restriction, including
;;; without limitation the rights to use, copy, modify, merge, publish,
;;; distribute, sublicense, and/or sell copies of the Software, and to
;;; permit persons to whom the Software is furnished to do so, subject to
;;; the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be included
;;; in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
;;; OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

;;;; Utility

(define (plist-fold proc nil ps)
  (let loop ((b nil) (ps ps))
    (pmatch ps
      (() b)
      ((,k ,v . ,ps*)
       (loop (proc k v b) ps*))
      (else (error "plist-fold: invalid plist")))))

(define (first-arg _k x _y) x)
(define (second-arg _k _x y) y)

(define (constantly x)
  (lambda (_) x))

;;;; Type

(define-record-type <imapping>
  (raw-imapping trie)
  imapping?
  (trie imapping-trie))

;;;; Constructors

(define (imapping . args)
  (raw-imapping
    (plist-fold (lambda (k v trie)
                  (trie-insert/combine trie k v second-arg))
                the-empty-trie
                args)))

(define (pair-or-null? x)
  (or (pair? x) (null? x)))

(define (alist->imapping/combinator comb as)
  (assume (procedure? comb))
  (assume (pair-or-null? as))
  (raw-imapping
    (fold (lambda (p trie)
            (assume (pair? p) "alist->imapping/combinator: not a pair")
            (trie-insert/combine trie (car p) (cdr p) comb))
          the-empty-trie
          as)))

(define (alist->imapping as)
  (alist->imapping/combinator second-arg as))

(define (imapping-unfold stop? mapper successor seed)
  (assume (procedure? stop?))
  (assume (procedure? mapper))
  (assume (procedure? successor))
  (let lp ((trie the-empty-trie) (seed seed))
    (if (stop? seed)
        (raw-imapping trie)
        (let-values (((k v) (mapper seed)))
          (assume (valid-integer? k))
          (lp (trie-insert trie k v) (successor seed))))))

(define (imapping-unfold-maybe proc seed)
  (assume (procedure? proc))
  (let lp ((trie the-empty-trie) (seed seed))
    (mmatch (proc seed)
      (nothing (raw-imapping trie))
      (just (k v seed*) (lp (trie-insert trie k v) seed*)))))

;;;; Predicates

(define (imapping-contains? imap n)
  (just? (imapping-lookup imap n)))

(define (imapping-empty? imap)
  (assume (imapping? imap))
  (not (imapping-trie imap)))

(define (imapping-disjoint? imap1 imap2)
  (assume (imapping? imap1))
  (assume (imapping? imap2))
  (trie-disjoint? (imapping-trie imap1) (imapping-trie imap2)))

;;;; Accessors

(define (imapping-lookup imap key)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (trie-assoc (imapping-trie imap) key))

(define imapping-ref
  (case-lambda
    ((imap key)
     (imapping-ref imap
                   key
                   (lambda () (error "imapping-ref: key not found"
                                     key
                                     imap))
                   values))
    ((imap key failure)
     (imapping-ref imap key failure values))
    ((imap key failure success)
     (assume (imapping? imap))
     (assume (valid-integer? key))
     (assume (procedure? failure))
     (assume (procedure? success))
     (maybe-ref (trie-assoc (imapping-trie imap) key)
                failure
                success))))

(define (imapping-ref/default imap key default)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (maybe-ref/default (trie-assoc (imapping-trie imap) key)
                     default))

(define (imapping-lookup-min imap)
  (assume (imapping? imap))
  (trie-min (imapping-trie imap)))

(define (imapping-min imap)
  (maybe-ref (imapping-lookup-min imap)
             (lambda () (error "imapping-min: empty imapping" imap))))

(define (imapping-lookup-max imap)
  (assume (imapping? imap))
  (trie-max (imapping-trie imap)))

(define (imapping-max imap)
  (maybe-ref (imapping-lookup-max imap)
             (lambda () (error "imapping-max: empty imapping" imap))))

;;;; Updaters

(define imapping-adjoin/combinator
  (case-lambda
    ((imap combine key value)      ; one-assoc fast path
     (raw-imapping
      (trie-insert/combine (imapping-trie imap) key value combine)))
    ((imap combine . ps)
     (raw-imapping
      (plist-fold (lambda (k v t)
                    (trie-insert/combine t k v combine))
                  (imapping-trie imap)
                  ps)))))

;; Preserve existing associations for keys.
(define imapping-adjoin
  (case-lambda
    ((imap key value)              ; one-assoc fast path
     (raw-imapping
      (trie-insert/combine (imapping-trie imap) key value second-arg)))
    ((imap . ps)
     (raw-imapping
      (plist-fold (lambda (k v t)
                    (trie-insert/combine t k v second-arg))
                  (imapping-trie imap)
                  ps)))))

;; Replace existing associations for keys.
(define imapping-set
  (case-lambda
    ((imap key value)      ; one-assoc fast path
     (raw-imapping
      (trie-insert (imapping-trie imap) key value)))
    ((imap . ps)
     (raw-imapping
      (plist-fold (lambda (k v t) (trie-insert t k v))
                  (imapping-trie imap)
                  ps)))))

(define (imapping-adjust imap key proc)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (assume (procedure? proc))
  (raw-imapping (trie-adjust (imapping-trie imap) key proc)))

(define imapping-delete
  (case-lambda
    ((imap key)      ; fast path
     (assume (imapping? imap))
     (assume (valid-integer? key))
     (raw-imapping (trie-delete (imapping-trie imap) key)))
    ((imap . keys)
     (imapping-delete-all imap keys))))

(define (imapping-delete-all imap keys)
  (assume (imapping? imap))
  (assume (or (pair? keys) (null? keys)))
  (let ((key-set (list->iset keys)))
    (imapping-remove (lambda (k _) (iset-contains? key-set k))
                     imap)))

;; Update the association (key, value) in trie with the result of
;; (mproc value), which is a Maybe value.
(define (imapping-update imap key mproc)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (assume (procedure? mproc))
  (raw-imapping (trie-update (imapping-trie imap) key mproc)))

;; Update the association (key, value) (or lack thereof) in imap
;; using proc, which is an endomap on Maybes.
(define (imapping-alter imap key proc)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (assume (procedure? proc))
  (raw-imapping (trie-alter (imapping-trie imap) key proc)))

;; Delete the element with the least key, or return an empty
;; mapping if `imap' is empty.
(define (imapping-delete-min imap)
  (imapping-update-min imap (lambda (_k _v) (nothing))))

(define (imapping-update-min imap success)
  (assume (imapping? imap))
  (assume (not (imapping-empty? imap)))
  (assume (procedure? success))
  (raw-imapping
   (trie-update-min (imapping-trie imap) success)))

(define (imapping-pop-min imap)
  (assume (imapping? imap))
  (if (imapping-empty? imap)
      (nothing)
      (let-values (((k v trie) (trie-pop-min (imapping-trie imap))))
        (just k v (raw-imapping trie)))))

;; Delete the element with the greatest key, or return an empty
;; mapping if `imap' is empty.
(define (imapping-delete-max imap)
  (imapping-update-max imap (lambda (_k _v) (nothing))))

(define (imapping-update-max imap success)
  (assume (imapping? imap))
  (assume (not (imapping-empty? imap)))
  (assume (procedure? success))
  (raw-imapping
   (trie-update-max (imapping-trie imap) success)))

(define (imapping-pop-max imap)
  (assume (imapping? imap))
  (if (imapping-empty? imap)
      (nothing)
      (let-values (((k v trie) (trie-pop-max (imapping-trie imap))))
        (just k v (raw-imapping trie)))))

;;;; The whole imapping

(define (imapping-size imap)
  (assume (imapping? imap))
  (let lp ((acc 0) (t (imapping-trie imap)))
    (cond ((not t) acc)
          ((leaf? t) (+ acc 1))
          (else
           (lp (lp acc (branch-left t)) (branch-right t))))))

(define (imapping-query pred imap)
  (assume (procedure? pred))
  (assume (imapping? imap))
  (let ((trie (imapping-trie imap)))
    (tmatch trie
      ((branch ? ,m ,l ,r) (guard (negative? m))
       (let ((m (trie-query pred r)))
         (if (just? m)
             m
             (trie-query pred l))))
      (else (trie-query pred trie)))))

(define (imapping-find pred imap failure)
  (assume (procedure? pred))
  (assume (imapping? imap))
  (assume (procedure? failure))
  (maybe-ref (imapping-query pred imap) failure))

(define (imapping-count pred imap)
  (assume (procedure? pred))
  (imapping-fold (lambda (k v acc)
                   (if (pred k v) (+ 1 acc) acc))
                 0
                 imap))

(define (imapping-any? pred imap)
  (assume (procedure? pred))
  (call-with-current-continuation
   (lambda (return)
     (imapping-fold (lambda (k v _)
                      (and (pred k v) (return #t)))
                    #f
                    imap))))

(define (imapping-every? pred imap)
  (assume (procedure? pred))
  (call-with-current-continuation
   (lambda (return)
     (imapping-fold (lambda (k v _)
                      (or (pred k v) (return #f)))
                    #t
                    imap))))

;;;; Mapping and folding

;; Map proc over the assocs. of imap, inserting result values under
;; the same key.
;; This is *not* the same as SRFI 146's mapping-map.
(define (imapping-map proc imap)
  (assume (procedure? proc))
  (assume (imapping? imap))
  (raw-imapping (trie-map proc (imapping-trie imap))))

(define (unspecified)
  (if #f #f))

(define (imapping-for-each proc imap)
  (assume (procedure? proc))
  (imapping-fold (lambda (k v _)
                   (proc k v)
                   (unspecified))
                 (unspecified)
                 imap))

(define (imapping-fold proc nil imap)
  (assume (procedure? proc))
  (assume (imapping? imap))
  (let ((trie (imapping-trie imap)))
    (tmatch trie
      ((branch ? ,m ,l ,r) (guard (negative? m))
       (trie-fold-left proc (trie-fold-left proc nil r) l))
      ((branch ? ? ,l ,r)
       (trie-fold-left proc (trie-fold-left proc nil l) r))
      (else (trie-fold-left proc nil trie)))))

(define (imapping-fold-right proc nil imap)
  (assume (procedure? proc))
  (assume (imapping? imap))
  (let ((trie (imapping-trie imap)))
    (tmatch trie
      ((branch ? ,m ,l ,r) (guard (negative? m))
       (trie-fold-right proc (trie-fold-right proc nil l) r))
      ((branch ? ? ,l ,r)
       (trie-fold-right proc (trie-fold-right proc nil r) l))
      (else (trie-fold-right proc nil trie)))))

(define (imapping-map->list proc imap)
  (assume (procedure? proc))
  (imapping-fold-right (lambda (k v us)
                         (cons (proc k v) us))
                       '()
                       imap))

(define (imapping-filter-map proc imap)
  (assume (procedure? proc))
  (assume (imapping? imap))
  (raw-imapping
   (imapping-fold (lambda (k v t)
                    (pmatch (proc k v)
                      (#f t)
                      (,v* (trie-insert t k v*))))
                  the-empty-trie
                  imap)))

(define (imapping-map-either proc imap)
  (assume (procedure? proc))
  (assume (imapping? imap))
  (let-values (((trie-left trie-right)
                (trie-map-either proc (imapping-trie imap))))
    (values (raw-imapping trie-left) (raw-imapping trie-right))))

(define (imapping-filter pred imap)
  (assume (procedure? pred))
  (assume (imapping? imap))
  (raw-imapping (trie-filter pred (imapping-trie imap))))

(define (imapping-remove pred imap)
  (imapping-filter (lambda (k v) (not (pred k v))) imap))

(define (imapping-partition pred imap)
  (assume (procedure? pred))
  (assume (imapping? imap))
  (let-values (((tin tout)
                (trie-partition pred (imapping-trie imap))))
    (values (raw-imapping tin) (raw-imapping tout))))

;;;; Copying & Conversion

(define (imapping-copy imap)
  (assume (imapping? imap))
  imap)

(define (imapping->alist imap)
  (imapping-fold-right (lambda (k v as) (cons (cons k v) as))
                       '()
                       imap))

(define (imapping->decreasing-alist imap)
  (imapping-fold (lambda (k v as) (cons (cons k v) as))
                 '()
                 imap))

(define (imapping-keys imap)
  (imapping-fold-right (lambda (k _ ks) (cons k ks)) '() imap))

(define (imapping-values imap)
  (imapping-fold-right (lambda (_ v vs) (cons v vs)) '() imap))

(define (imapping->generator imap)
  (assume (imapping? imap))
  (make-coroutine-generator
   (lambda (yield)
     (imapping-fold (lambda (k v _) (yield (cons k v)))
                    #f
                    imap))))

(define (imapping->decreasing-generator imap)
  (assume (imapping? imap))
  (make-coroutine-generator
   (lambda (yield)
     (imapping-fold-right (lambda (k v _) (yield (cons k v)))
                          #f
                          imap))))

;;;; Comparison

(define (imapping=? comp imap1 imap2 . imaps)
  (assume (comparator? comp))
  (assume (imapping? imap1))
  (let ((imap-eq1 (lambda (imap)
                    (assume (imapping? imap))
                    (or (eqv? imap1 imap)
                        (trie=? comp
                                (imapping-trie imap1)
                                (imapping-trie imap))))))
    (and (imap-eq1 imap2)
         (or (null? imaps)
             (every imap-eq1 imaps)))))

(define (imapping<? comp imap1 imap2 . imaps)
  (assume (comparator? comp))
  (assume (imapping? imap1))
  (assume (imapping? imap2))
  (let lp ((t1 (imapping-trie imap1))
           (t2 (imapping-trie imap2))
           (imaps imaps))
    (and (trie-proper-subset? comp t1 t2)
         (pmatch imaps
           (() #t)
           ((,m . ,imaps*) (lp t2 (imapping-trie m) imaps*))))))

(define (imapping>? comp imap1 imap2 . imaps)
  (assume (comparator? comp))
  (assume (imapping? imap1))
  (assume (imapping? imap2))
  (let lp ((t1 (imapping-trie imap1))
           (t2 (imapping-trie imap2))
           (imaps imaps))
    (and (trie-proper-subset? comp t2 t1)
         (pmatch imaps
           (() #t)
           ((,m . ,imaps*) (lp t2 (imapping-trie m) imaps*))))))

(define (imapping<=? comp imap1 imap2 . imaps)
  (assume (comparator? comp))
  (assume (imapping? imap1))
  (assume (imapping? imap2))
  (let lp ((t1 (imapping-trie imap1))
           (t2 (imapping-trie imap2))
           (imaps imaps))
    (and (memv (trie-subset-compare comp t1 t2) '(less equal))
         (pmatch imaps
           (() #t)
           ((,m . ,imaps*) (lp t2 (imapping-trie m) imaps*))))))

(define (imapping>=? comp imap1 imap2 . imaps)
  (assume (comparator? comp))
  (assume (imapping? imap1))
  (assume (imapping? imap2))
  (let lp ((t1 (imapping-trie imap1))
           (t2 (imapping-trie imap2))
           (imaps imaps))
    (and (memv (trie-subset-compare comp t2 t1) '(less equal))
         (pmatch imaps
           (() #t)
           ((,m . ,imaps*) (lp t2 (imapping-trie m) imaps*))))))

;;;; Set theory operations

(define (imapping-union . args)
  (apply imapping-union/combinator first-arg args))

(define (imapping-intersection . args)
  (apply imapping-intersection/combinator first-arg args))

(define imapping-difference
  (case-lambda
    ((imap1 imap2)
     (assume (imapping? imap1))
     (assume (imapping? imap2))
     (raw-imapping
      (trie-difference (imapping-trie imap1) (imapping-trie imap2))))
    ((imap . rest)
     (assume (imapping? imap))
     (assume (pair? rest))
     (raw-imapping
      (trie-difference (imapping-trie imap)
                       (imapping-trie (apply imapping-union rest)))))))

(define (imapping-xor imap1 imap2)
  (assume (imapping? imap1))
  (assume (imapping? imap2))
  (raw-imapping
   (trie-xor (imapping-trie imap1) (imapping-trie imap2))))

(define (imapping-union/combinator proc imap . rest)
  (assume (procedure? proc))
  (assume (imapping? imap))
  (assume (pair? rest))
  (raw-imapping
   (fold (lambda (im t)
           (assume (imapping? im))
           (trie-merge proc t (imapping-trie im)))
         (imapping-trie imap)
         rest)))

(define (imapping-intersection/combinator proc imap . rest)
  (assume (procedure? proc))
  (assume (imapping? imap))
  (assume (pair? rest))
  (raw-imapping
   (fold (lambda (im t)
           (assume (imapping? im))
           (trie-intersection proc t (imapping-trie im)))
         (imapping-trie imap)
         rest)))

;;;; Subsets

(define (isubmapping= imap key)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (mmatch (imapping-lookup imap key)
          (nothing (imapping))
          (just (v) (imapping key v))))

(define (imapping-open-interval imap low high)
  (assume (imapping? imap))
  (assume (valid-integer? low))
  (assume (valid-integer? high))
  (assume (fx>=? high low))
  (raw-imapping
   (subtrie-interval (imapping-trie imap) low high #f #f)))

(define (imapping-closed-interval imap low high)
  (assume (imapping? imap))
  (assume (valid-integer? low))
  (assume (valid-integer? high))
  (assume (fx>=? high low))
  (raw-imapping
   (subtrie-interval (imapping-trie imap) low high #t #t)))

(define (imapping-open-closed-interval imap low high)
  (assume (imapping? imap))
  (assume (valid-integer? low))
  (assume (valid-integer? high))
  (assume (fx>=? high low))
  (raw-imapping
   (subtrie-interval (imapping-trie imap) low high #f #t)))

(define (imapping-closed-open-interval imap low high)
  (assume (imapping? imap))
  (assume (valid-integer? low))
  (assume (valid-integer? high))
  (assume (fx>=? high low))
  (raw-imapping
   (subtrie-interval (imapping-trie imap) low high #t #f)))

(define (isubmapping< imap key)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (raw-imapping (subtrie< (imapping-trie imap) key #f)))

(define (isubmapping<= imap key)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (raw-imapping (subtrie< (imapping-trie imap) key #t)))

(define (isubmapping> imap key)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (raw-imapping (subtrie> (imapping-trie imap) key #f)))

(define (isubmapping>= imap key)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (raw-imapping (subtrie> (imapping-trie imap) key #t)))

(define (imapping-split imap k)
  (assume (imapping? imap))
  (assume (integer? k))
  (let-values (((trie-low trie-high) (trie-split (imapping-trie imap) k)))
    (values (raw-imapping trie-low) (raw-imapping trie-high))))

;;;; imappings as relations

(define (imapping-relation-map proc imap)
  (assume (procedure? proc))
  (assume (imapping? imap))
  (raw-imapping (trie-relation-map proc (imapping-trie imap))))
