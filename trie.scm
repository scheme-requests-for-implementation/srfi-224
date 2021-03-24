;;; This file implements integers maps as compressed binary radix
;;; trees (AKA Patricia tries), as described by Chris Okasaki and
;;; Andrew Gill in "Fast Mergeable Integer Maps" (1998).  Integers
;;; in big-endian binary encoding are stored in a trie structure
;;; which allows fast lookup, insertion, and set-theoretical
;;; operations (union, intersection, etc.)
;;;
;;; A trie is represented by #f (the empty trie), a leaf, or a branch.
;;;
;;; Throughout this code, the empty trie (#f) is always returned
;;; as an explicit value, not, e.g. as the default value of an
;;; (and ...) expression, to clarify its use as a trie value.

;;;; Utility

(define (swap-args proc)
  (lambda (x y) (proc y x)))

(define the-empty-trie #f)

(define (trie-empty? t) (not t))

(define-record-type <leaf>
  (leaf key value)
  leaf?
  (key leaf-key)
  (value leaf-value))

(define-record-type <branch>
  (raw-branch prefix branching-bit left right)
  branch?
  (prefix branch-prefix)
  (branching-bit branch-branching-bit)
  (left branch-left)
  (right branch-right))

(define (valid-integer? x) (fixnum? x))

;; Zero the bits of k at and below (BE) the set bit of m.
(define (mask k m)
  (if (fx=? m fx-least)
      0
      (fxand k (fxxor (fxnot (fx- m 1)) m))))

;; Does the m-masked prefix of k match p?
(define (match-prefix? k p m)
  (fx=? (mask k m) p))

(define (branching-bit p1 m1 p2 m2)
  (if (fxnegative? (fxxor p1 p2))
      fx-least        ; different signs
      (highest-bit-mask (fxxor p1 p2) (fxmax 1 (fx* 2 (fxmax m1 m2))))))

;; Two's-complement trick.
(define (lowest-set-bit b)
  (fxand b (fxneg b)))

(define (highest-bit-mask k guess-m)
  (let lp ((x (fxand k (fxnot (fx- guess-m 1)))))
    (let ((m (lowest-set-bit x)))
      (if (fx=? x m)
          m
          (lp (fx- x m))))))

(define (zero-bit? k m)
  (fxzero? (fxand k m)))

;; Insert the association (key, value) into trie, replacing any old
;; association.
(define (trie-insert trie key value)
  (trie-insert/combine trie key value (lambda (new _) new)))

;; Insert (key, value) into trie if key doesn't already have an
;; association.  If it does, add a new association for key and
;; the result of calling combine on the new and old values.
(define (trie-insert/combine trie key value combine)
  (letrec
   ((new-leaf (leaf key value))
    (insert
     (lambda (t)
       (tmatch t
         (empty (leaf key value))
         ((leaf ,k ,v)
          (if (fx=? key k)
              (leaf k (combine value v))
              (trie-join key 0 new-leaf k 0 t)))
         ((branch ,p ,m ,l ,r)
          (if (match-prefix? key p m)
              (if (zero-bit? key m)
                  (branch p m (insert l) r)
                  (branch p m l (insert r)))
              (trie-join key 0 new-leaf p m t)))))))
    (insert trie)))

(define (trie-join prefix1 mask1 trie1 prefix2 mask2 trie2)
  (let ((m (branching-bit prefix1 mask1 prefix2 mask2)))
    (if (zero-bit? prefix1 m)
        (branch (mask prefix1 m) m trie1 trie2)
        (branch (mask prefix1 m) m trie2 trie1))))

;; If (key, value) is an association in trie, then replace it
;; with (key, (proc value)).  Otherwise, return a copy of trie.
(define (trie-adjust trie key proc with-key)
  (letrec
   ((update
     (lambda (t)
       (tmatch t
         (empty t)
         ((leaf ,k ,v)
          (if (fx=? key k)
              (leaf k (if with-key (proc k v) (proc v)))
              t))
         ((branch ,p ,m ,l ,r)
          (if (match-prefix? key p m)
              (if (zero-bit? key m)
                  (branch p m (update l) r)
                  (branch p m l (update r)))
              t))))))
    (update trie)))

(define (trie-update trie key mproc with-key)
  (letrec
   ((update
     (lambda (t)
       (tmatch t
         (empty t)
         ((leaf ,k ,v)
          (if (fx=? key k)
              (mmatch (if with-key (mproc k v) (mproc v))
                (nothing #f)
                (just (v*) (leaf k v*)))
              t))
         ((branch ,p ,m ,l ,r)
          (if (match-prefix? key p m)
              (if (zero-bit? key m)
                  (branch p m (update l) r)
                  (branch p m l (update r)))
              t))))))
    (update trie)))

;; This is the sane person's trie-search.
(define (trie-alter trie key proc)
  (letrec
   ((update
     (lambda (t)
       (tmatch t
         (empty
          (mmatch (proc (nothing))
            (nothing the-empty-trie)
            (just (v) (leaf key v))))
         ((leaf ,k ,v)
          (if (fx=? key k)
              (mmatch (proc (just v))
                (nothing the-empty-trie)
                (just (v*) (leaf k v*)))
              (mmatch (proc (nothing))
                (nothing t)
                (just (u) (trie-join key 0 (leaf key u) k 0 t)))))
         ((branch ,p ,m ,l ,r) (guard (match-prefix? key p m))
          (if (zero-bit? key m)
              (branch p m (update l) r)
              (branch p m l (update r))))
         ((branch ,p ,m ? ?)
          (mmatch (proc (nothing))
            (nothing t)
            (just (v) (trie-join key 0 (leaf key v) p m t))))))))
    (update trie)))

;; Return the value associated with key in trie; if there is
;; none, return #f.
(define (trie-assoc trie key)
  (letrec
   ((search
     (tmatch-lambda
       ((leaf ,k ,v) (and (fx=? k key) v))
       ((branch ,p ,m ,l ,r) (guard (match-prefix? key p m))
        (if (zero-bit? key m) (search l) (search r)))
       (else #f))))
    (search trie)))

(define (branching-bit-higher? mask1 mask2)
  (if (negative? (fxxor mask1 mask2))  ; signs differ
      (negative? mask1)
      (fx>? mask1 mask2)))

;; Merge two tries.  `combine' is used to merge duplicated mappings.
(define (trie-merge combine trie1 trie2)
  (letrec
    ((merge
      (lambda (s t)
        (cond ((trie-empty? s) t)
              ((trie-empty? t) s)
              ((leaf? s)
               (trie-insert/combine t (leaf-key s) (leaf-value s) combine))
              ((leaf? t)
               (trie-insert/combine s
                                    (leaf-key t)
                                    (leaf-value t)
                                    (swap-args combine)))
              ((and (branch? s) (branch? t)) (merge-branches s t)))))
     (merge-branches
      (lambda (s t)
        (tmatch s
          ((branch ,p ,m ,s1 ,s2)
           (tmatch t
             ((branch ,q ,n ,t1 ,t2)
              (cond ((and (fx=? m n) (fx=? p q))
                     (branch p m (merge s1 t1) (merge s2 t2)))
                    ((and (branching-bit-higher? m n)
                          (match-prefix? q p m))
                     (if (zero-bit? q m)
                         (branch p m (merge s1 t) s2)
                         (branch p m s1 (merge s2 t))))
                    ((and (branching-bit-higher? n m)
                          (match-prefix? p q n))
                     (if (zero-bit? p n)
                         (branch q n (merge s t1) t2)
                         (branch q n t1 (merge s t2))))
                    (else (trie-join p m s q n t))))))))))
    (merge trie1 trie2)))

;; Construct a branch only if the subtrees are non-empty.
(define (branch prefix mask trie1 trie2)
  (cond ((not trie1) trie2)
        ((not trie2) trie1)
        (else (raw-branch prefix mask trie1 trie2))))

(define (trie-union s t)
  (trie-merge trie-insert s t))

(define (trie-partition pred trie with-key)
  (letrec
   ((part
     (lambda (t)
       (tmatch t
         (empty (values the-empty-trie the-empty-trie))
         ((leaf ,k ,v)
          (if (if with-key (pred k v) (pred v))
              (values t the-empty-trie)
              (values the-empty-trie t)))
         ((branch ,p ,m ,l ,r)
          (let-values (((il ol) (part l))
                       ((ir or) (part r)))
            (values (branch p m il ir) (branch p m ol or))))))))
    (part trie)))

;;;; Map and fold

(define (trie-map proc trie with-key)
  (letrec
   ((tmap
     (tmatch-lambda
       (empty the-empty-trie)
       ((leaf ,k ,v)
        (leaf k (if with-key (proc k v) (proc v))))
       ((branch ,p ,m ,l ,r)
        (branch p m (tmap l) (tmap r))))))
    (tmap trie)))

(define (trie-fold-left proc nil trie)
  (letrec
   ((cata
     (lambda (b t)
       (tmatch t
         (empty b)
         ((leaf ? ,v) (proc v b))
         ((branch ? ? ,l ,r) (cata (cata b l) r))))))
    (cata nil trie)))

(define (trie-fold-left/key proc nil trie)
  (letrec
   ((cata
     (lambda (b t)
       (tmatch t
         (empty b)
         ((leaf ,k ,v) (proc k v b))
         ((branch ? ? ,l ,r) (cata (cata b l) r))))))
    (cata nil trie)))

(define (trie-fold-right proc nil trie)
  (letrec
   ((cata
     (lambda (b t)
       (tmatch t
         (empty b)
         ((leaf ? ,v) (proc v b))
         ((branch ? ? ,l ,r) (cata (cata b r) l))))))
    (cata nil trie)))

(define (trie-fold-right/key proc nil trie)
  (letrec
   ((cata
     (lambda (b t)
       (tmatch t
         (empty b)
         ((leaf ,k ,v) (proc k v b))
         ((branch ? ? ,l ,r) (cata (cata b r) l))))))
    (cata nil trie)))

(define (trie-map-either proc trie with-key)
  (letrec
   ((split-map
     (lambda (t)
       (tmatch t
         (empty (values the-empty-trie the-empty-trie))
         ((leaf ,k ,v)
          (ematch (if with-key (proc k v) (proc v))
            (left (v*) (values (leaf k v*) the-empty-trie))
            (right (v*) (values the-empty-trie (leaf k v*)))))
         ((branch ,p ,m ,l ,r)  ; slight naming confusion here.
          (let-values (((l-lefts l-rights) (split-map l))
                       ((r-lefts r-rights) (split-map r)))
            (values (branch p m l-lefts r-lefts)
                    (branch p m l-rights r-rights))))))))
    (split-map trie)))

(define (trie-filter pred trie)
  (letrec ((filter
            (lambda (t)
              (tmatch t
                (empty the-empty-trie)
                ((leaf ? ,v) (guard (pred v)) t)
                ((leaf ? ?) the-empty-trie)
                ((branch ,p ,m ,l ,r)
                 (branch p m (filter l) (filter r)))))))
    (filter trie)))

(define (trie-filter/key pred trie)
  (letrec ((filter
            (lambda (t)
              (tmatch t
                (empty the-empty-trie)
                ((leaf ,k ,v) (guard (pred k v)) t)
                ((leaf ? ?) the-empty-trie)
                ((branch ,p ,m ,l ,r)
                 (branch p m (filter l) (filter r)))))))
    (filter trie)))

;; Return a Just containing the least key and value of trie,
;; or Nothing if trie is empty.
(define (trie-min trie)
  (letrec
   ((search
     (tmatch-lambda
       ((leaf ,k ,v) (just k v))
       ((branch ? ? ,l ?) (search l)))))
    (tmatch trie
      (empty (nothing))
      ((leaf ,k ,v) (just k v))
      ((branch ? ,m ,l ,r)
       (if (fxnegative? m) (search r) (search l))))))

;; Call success on the key and value of the leftmost leaf and use
;; the resulting Maybe to update the value.
(define (%trie-update-min/key trie success)
  (letrec
   ((update
     (tmatch-lambda
       (empty the-empty-trie)
       ((leaf ,k ,v)
        (mmatch (success k v)
          (nothing the-empty-trie)
          (just (v*) (leaf k v*))))
       ((branch ,p ,m ,l ,r) (branch p m (update l) r)))))
    (tmatch trie
      ((branch ,p ,m ,l ,r)
       (if (negative? m)
           (branch p m l (update r))
           (branch p m (update l) r)))
      (else (update trie)))))

(define (trie-pop-min trie)
  (letrec
   ((pop
     (tmatch-lambda
       (empty (error "trie-pop-min: empty trie"))
       ((leaf ,k ,v) (values k v the-empty-trie))
       ((branch ,p ,m ,l ,r)
        (let-values (((k v l*) (pop l)))
          (values k v (branch p m l* r)))))))
    (tmatch trie
      ((branch ,p ,m ,l ,r)
       (if (fxnegative? m)
           (let-values (((k v r*) (pop r)))
             (values k v (branch p m l r*)))
           (let-values (((k v l*) (pop l)))
             (values k v (branch p m l* r)))))
      (else (pop trie)))))

(define (trie-max trie)
  (letrec
   ((search
     (tmatch-lambda
       ((leaf ,k ,v) (just k v))
       ((branch ? ? ? ,r) (search r)))))
    (tmatch trie
      (empty (nothing))
      ((branch ? ,m ,l ,r)
       (if (fxnegative? m) (search l) (search r)))
      (else (search trie)))))

;; Call success on the key and value of the greatest-keyed leaf
;; and use the resulting Maybe to update the value.
(define (%trie-update-max/key trie success)
  (letrec
   ((update
     (tmatch-lambda
       (empty the-empty-trie)
       ((leaf ,k ,v)
        (mmatch (success k v)
          (nothing the-empty-trie)
          (just (v*) (leaf k v*))))
       ((branch ,p ,m ,l ,r) (branch p m l (update r))))))
    (tmatch trie
      ((branch ,p ,m ,l ,r)
       (if (negative? m)
           (branch p m (update l) r)
           (branch p m l (update r))))
      (else (update trie)))))

(define (trie-pop-max trie)
  (letrec
   ((pop
     (tmatch-lambda
       (empty (error "trie-pop-max: empty trie"))
       ((leaf ,k ,v) (values k v the-empty-trie))
       ((branch ,p ,m ,l ,r)
        (let-values (((k v r*) (pop r)))
          (values k v (branch p m l r*)))))))
    (tmatch trie
      ((branch ,p ,m ,l ,r)
       (if (fxnegative? m)
           (let-values (((k v l*) (pop l)))
             (values k v (branch p m l* r)))
           (let-values (((k v r*) (pop r)))
             (values k v (branch p m l r*)))))
      (else (pop trie)))))

;;;; Comparisons

(define (trie=? comp trie1 trie2)
  (let loop ((s trie1) (t trie2))
    (cond ((and (trie-empty? s) (trie-empty? t)) #t)
          ((leaf? s)
           (and (leaf? t)
                (fx=? (leaf-key s) (leaf-key t))
                (=? comp (leaf-value s) (leaf-value t))))
          ((and (branch? s) (branch? t))
           (tmatch s
            ((branch ,p ,m ,l1 ,r1)
             (tmatch t
               ((branch ,q ,n ,l2 ,r2)
                (and (fx=? m n)
                     (fx=? p q)
                     (loop l1 l2)
                     (loop r1 r2)))))))
          (else #f))))

;; Returns the symbol 'less' if trie1 is a proper subset of trie2,
;; 'equal' if they are the same, and 'greater' otherwise.  NB that
;; disjoint mappings will compare as greater.
(define (trie-subset-compare comp trie1 trie2)
  (letrec
   ((compare
     (lambda (s t)
       (cond ((eqv? s t) 'equal)
             ((trie-empty? s) 'less)
             ((trie-empty? t) 'greater)  ; disjoint
             ((and (leaf? s) (leaf? t))
              (if (and (fx=? (leaf-key s) (leaf-key t))
                       (=? comp (leaf-value s) (leaf-value t)))
                  'equal
                  'greater))
             ((leaf? s)             ; leaf / branch
              (tmatch t
                ((branch ,p ,m ,l ,r)
                 (let ((k (leaf-key s)))
                   (if (match-prefix? k p m)
                       (case (compare s (if (zero-bit? k m) l r))
                         ((greater) 'greater)
                         (else 'less)))))))
             ((leaf? t) 'greater)   ; branch / leaf
             (else (compare-branches s t)))))
    (compare-branches
     (lambda (s t)
       (tmatch s
         ((branch ,p ,m ,sl ,sr)
          (tmatch t
            ((branch ,q ,n ,tl ,tr)
             (cond ((branching-bit-higher? m n) 'greater)
                   ((branching-bit-higher? n m)
                    (if (match-prefix? p q n)
                        (let ((res (if (zero-bit? p n)
                                       (compare s tl)
                                       (compare s tr))))
                          (if (eqv? res 'greater) res 'less))
                        'greater))
                   ((fx=? p q)  ; same prefix, compare subtrees
                    (let ((cl (compare sl tl)) (cr (compare sr tr)))
                      (cond ((or (eqv? cl 'greater) (eqv? cr 'greater))
                             'greater)
                            ((and (eqv? cl 'equal) (eqv? cr 'equal))
                             'equal)
                            (else 'less))))
                   (else 'greater)))))))))  ; disjoint
    (compare trie1 trie2)))

(define (trie-proper-subset? comp trie1 trie2)
  (eqv? (trie-subset-compare comp trie1 trie2) 'less))

;; Two tries are disjoint if they have no keys in common.
(define (trie-disjoint? trie1 trie2)
  (letrec
   ((disjoint?
     (lambda (s t)
       (or (trie-empty? s)
           (trie-empty? t)
           (cond ((leaf? s)
                  (let ((k (leaf-key s)))
                    (if (leaf? t)
                        (not (fx=? k (leaf-key t)))
                        (not (trie-assoc t k)))))
                 ((leaf? t) (not (trie-assoc s (leaf-key t))))
                 (else (branches-disjoint? s t))))))
    (branches-disjoint?
     (lambda (s t)
       (tmatch s
         ((branch ,p ,m ,sl ,sr)
          (tmatch t
            ((branch ,q ,n ,tl ,tr)
             (cond ((and (fx=? m n) (fx=? p q))
                    (and (disjoint? sl tl) (disjoint? sr tr)))
                   ((and (branching-bit-higher? m n)
                         (match-prefix? q p m))
                    (if (zero-bit? q m)
                        (disjoint? sl t)
                        (disjoint? sr t)))
                   ((and (branching-bit-higher? n m)
                         (match-prefix? p q n))
                    (if (zero-bit? p n)
                        (disjoint? s tl)
                        (disjoint? s tr)))
                   (else #t)))))))))      ; the prefixes disagree
    (disjoint? trie1 trie2)))

(define (trie-delete trie key)
  (letrec
   ((update
     (lambda (t)
       (tmatch t
         (empty the-empty-trie)
         ((leaf ,k ?) (if (fx=? k key) the-empty-trie t))
         ((branch ,p ,m ,l ,r) (guard (match-prefix? key p m))
          (if (zero-bit? key m)
               (branch p m (update l) r)
               (branch p m l (update r))))
         (else t)))))  ; key doesn't occur in t
    (update trie)))

(define (trie-intersection combine trie1 trie2)
  (letrec
   ((intersect
     (lambda (s t)
       (cond ((or (trie-empty? s) (trie-empty? t)) the-empty-trie)
             ((and (leaf? s) (leaf? t))
              (tmatch s
                ((leaf ,sk ,sv)
                 (tmatch t
                   ((leaf ,tk ,tv) (guard (fx=? sk tk))
                    (leaf sk (combine sv tv)))
                   (else the-empty-trie)))))
             ((leaf? s) (insert-leaf combine s t))
             ((leaf? t) (insert-leaf (swap-args combine) t s))
             (else (intersect-branches s t)))))
    (insert-leaf
     (lambda (comb lf t)
       (tmatch lf
         ((leaf ,k ,v)
          (let lp ((t t))
            (tmatch t
              ((leaf ,tk ,tv) (guard (fx=? k tk)) (leaf k (comb v tv)))
              ((leaf ? ?) the-empty-trie)
              ((branch ,p ,m ,l ,r)
               (and (match-prefix? k p m)
                    (if (zero-bit? k m) (lp l) (lp r))))
              (else the-empty-trie)))))))
    (intersect-branches
     (lambda (s t)
       (tmatch s
         ((branch ,p ,m ,sl ,sr)
          (tmatch t
            ((branch ,q ,n ,tl ,tr)
             (cond ((branching-bit-higher? m n)
                    (and (match-prefix? q p m)
                         (if (zero-bit? q m)
                             (intersect sl t)
                             (intersect sr t))))
                   ((branching-bit-higher? n m)
                    (and (match-prefix? p q n)
                         (if (zero-bit? p n)
                             (intersect s tl)
                             (intersect s tr))))
                   ((fx=? p q)
                    (branch p m (intersect sl tl) (intersect sr tr)))
                   (else the-empty-trie)))))))))
    (intersect trie1 trie2)))

(define (trie-difference trie1 trie2)
  (letrec
   ((difference
     (lambda (s t)
       (cond ((trie-empty? s) the-empty-trie)
             ((trie-empty? t) s)
             ((leaf? s)
              (if (trie-assoc t (leaf-key s)) the-empty-trie s))
             ((leaf? t) (trie-delete s (leaf-key t)))
             (else (branch-difference s t)))))
    (branch-difference
     (lambda (s t)
       (tmatch s
         ((branch ,p ,m ,sl ,sr)
          (tmatch t
            ((branch ,q ,n ,tl ,tr)
             (cond ((and (fx=? m n) (fx=? p q))
                    (branch p m (difference sl tl) (difference sr tr)))
                   ((and (branching-bit-higher? m n)
                         (match-prefix? q p m))
                    (if (zero-bit? q m)
                        (branch p m (difference sl t) sr)
                        (branch p m sl (difference sr t))))
                   ((and (branching-bit-higher? n m)
                         (match-prefix? p q n))
                    (if (zero-bit? p n)
                        (difference s tl)
                        (difference s tr)))
                   (else s)))))))))
    (difference trie1 trie2)))

;; Remove the assoc for key if it exists in trie; otherwise, add the
;; assoc (key, value).
(define (%trie-insert-xor trie key value)
  (trie-alter trie
              key
              (lambda (mv)
                (if (nothing? mv)
                    (just value)
                    (nothing)))))

(define (trie-xor trie1 trie2)
  (letrec
    ((merge
      (lambda (s t)
        (cond ((trie-empty? s) t)
              ((trie-empty? t) s)
              ((leaf? s)
               (%trie-insert-xor t (leaf-key s) (leaf-value s)))
              ((leaf? t)
               (%trie-insert-xor s (leaf-key t) (leaf-value t)))
              (else (merge-branches s t)))))
     (merge-branches
      (lambda (s t)
        (tmatch s
          ((branch ,p ,m ,s1 ,s2)
           (tmatch t
             ((branch ,q ,n ,t1 ,t2)
              (cond ((and (fx=? m n) (fx=? p q))
                     (branch p m (merge s1 t1) (merge s2 t2)))
                    ((and (branching-bit-higher? m n) (match-prefix? q p m))
                     (if (zero-bit? q m)
                         (branch p m (merge s1 t) s2)
                         (branch p m s1 (merge s2 t))))
                    ((and (branching-bit-higher? n m) (match-prefix? p q n))
                     (if (zero-bit? p n)
                         (branch q n (merge s t1) t2)
                         (branch q n t1 (merge s t2))))
                    (else
                     (trie-join p m s q n t))))))))))
    (merge trie1 trie2)))

;; Return a trie containing all the elements of `trie' which are
;; less than k, if `inclusive' is false, or less than or equal to
;; k if `inclusive' is true.
(define (subtrie< trie k inclusive)
  (letrec
    ((split
      (lambda (t)
        (tmatch t
          (empty the-empty-trie)
          ((leaf ,tk ?)
           (cond ((fx<? tk k) t)
                 ((and (fx=? tk k) inclusive) t)
                 (else the-empty-trie)))
          ((branch ,p ,m ,l ,r)
           (if (match-prefix? k p m)
               (if (zero-bit? k m)
                   (split l)
                   (trie-union l (split r)))
               (and (fx<? p k) t)))))))
    (tmatch trie
      ((branch ? ,m ,l ,r) (guard (fxnegative? m))
       (if (fxnegative? k) (split r) (trie-union (split l) r)))
      (else (split trie)))))

;; Return a trie containing all the elements of `trie' which are
;; greater than k, if `inclusive' is false, or greater than or equal
;; to k if `inclusive' is true.
(define (subtrie> trie k inclusive)
  (letrec
   ((split
     (lambda (t)
       (tmatch t
         (empty the-empty-trie)
         ((leaf ,tk ?)
          (cond ((fx>? tk k) t)
                ((and (fx=? tk k) inclusive) t)
                (else the-empty-trie)))
         ((branch ,p ,m ,l ,r)
          (if (match-prefix? k p m)
              (if (zero-bit? k m)
                  (trie-union (split l) r)
                  (split r))
              (and (fx>? p k) t)))))))
    (tmatch trie
      ((branch ? ,m ,l ,r) (guard (fxnegative? m))
       (if (fxnegative? k) (trie-union (split r) l) (split l)))
      (else (split trie)))))

;; Return a trie containing all the elements of `trie' which are
;; greater than/greater than or equal to a and less than/less than
;; or equal to b, depending on the truth values of
;; low-/high-inclusive.
(define (subtrie-interval trie a b low-inclusive high-inclusive)
  (letrec
   ((interval
     (lambda (t)
       (tmatch t
         (empty the-empty-trie)
         ((leaf ,tk ?)
          (and ((if low-inclusive fx>=? fx>?) tk a)
               ((if high-inclusive fx<=? fx<?) tk b)
               t))
         (else (branch-interval t)))))
    (branch-interval
     (lambda (t)
       (tmatch t
         ((branch ,p ,m ,l ,r)
          (if (match-prefix? a p m)
              (if (zero-bit? a m)
                  (if (match-prefix? b p m)
                      (if (zero-bit? b m)
                          (interval l)  ; all x < b is in l
                          (trie-union (subtrie> l a low-inclusive)
                                      (subtrie< r b high-inclusive)))
                      ;; everything or nothing is less than b
                      (and (fx<? b p)
                           (trie-union (subtrie> l a low-inclusive) r)))
                  (interval r)) ; all x > b is in r
              ;; everything or nothing is greater than a
              (and (fx>? p a) (subtrie< t b high-inclusive))))))))
    (tmatch trie
      ((branch ? ,m ,l ,r) (guard (fxnegative? m))
       (cond ((and (fxnegative? a) (fxnegative? b)) (interval r))
             ((and (fxpositive? a) (fxpositive? b)) (interval l))
              ;; (a, 0) U (0, b)
              (else (trie-union (subtrie> r a low-inclusive)
                                (subtrie< l b high-inclusive)))))
      (else (interval trie)))))

;;;; Tries as (Integer, *) relations

(define (trie-relation-map proc trie)
  (trie-fold-left/key (lambda (k v t)
                        (let-values (((k* v*) (proc k v)))
                          (assume (valid-integer? k*))
                          (trie-insert t k* v*)))
                      the-empty-trie
                      trie))

(define trie-copy
  (tmatch-lambda
    (empty the-empty-trie)
    ((leaf ,k ,v) (leaf k v))
    ((branch ,p ,m ,l ,r)
     (branch p m (trie-copy l) (trie-copy r)))))
