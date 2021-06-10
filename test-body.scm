;;;; Utility

(define default-comp (make-default-comparator))

(define (constantly x) (lambda _ x))

(define (first-arg _k x _y) x)
(define (second-arg _k _x y) y)
(define (nth n) (lambda args (list-ref args n)))

(define (square x) (* x x))

(define (list->dup-alist xs)
  (map cons xs xs))

;; From SRFI 210, reduced.
(define-syntax value/mv
  (syntax-rules ()
    ((value/mv i producer)
     (let-values ((vs producer))
       (list-ref vs i)))))

;;;; Test fxmappings

(define empty-fxmap (fxmapping))

(define letter-fxmap
  (let* ((cs "abcdefghijklmnopqrstuvwxyz")
         (len (string-length cs)))
    (fxmapping-unfold
     (lambda (i) (= i len))
     (lambda (i) (values i (string->symbol (string (string-ref cs i)))))
     (lambda (i) (+ i 1))
     0)))

;; (-100 . -100), (-75 . -75), ..., (0 . 0), ..., (100 . 100)
(define mixed-seq
  (unfold (lambda (i) (> i 100))
          (lambda (i) (cons i i))
          (lambda (i) (+ i 25))
          -100))

(define mixed-fxmap (alist->fxmapping mixed-seq))

;; From -65536 to 65536 in steps of 4096.  Key = value.
(define sparse-seq
  (unfold (lambda (i) (> i 65536))
          (lambda (i) (cons i i))
          (lambda (i) (+ i 4096))
          -65536))

(define sparse-fxmap (alist->fxmapping sparse-seq))

(define all-test-fxmaps
  (list empty-fxmap mixed-fxmap letter-fxmap sparse-fxmap))

;;; fxmapping=? and the alist conversions are used in many other tests,
;;; so we test these first.  These also test the basic fxmapping
;;; constructor.

(test-group "Equality"
  (test-eqv #t (fxmapping=? default-comp empty-fxmap (fxmapping)))
  (test-eqv #t (fxmapping=? default-comp (fxmapping 10 'a) (fxmapping 10 'a)))
  (test-eqv #f (fxmapping=? default-comp empty-fxmap (fxmapping 10 'a)))
  (test-eqv #t (fxmapping=? default-comp mixed-fxmap mixed-fxmap))
  (test-eqv #t (fxmapping=? default-comp letter-fxmap letter-fxmap))
  )

(test-group "Conversion"
  (test-eqv #t (null? (fxmapping->alist empty-fxmap)))
  (test-equal '((10 . a)) (fxmapping->alist (fxmapping 10 'a)))
  (test-equal mixed-seq (fxmapping->alist mixed-fxmap))
  (test-equal sparse-seq (fxmapping->alist sparse-fxmap))

  (test-eqv #t (null? (fxmapping->decreasing-alist empty-fxmap)))
  (test-equal '((10 . a)) (fxmapping->decreasing-alist (fxmapping 10 'a)))
  (test-equal (reverse mixed-seq) (fxmapping->decreasing-alist mixed-fxmap))
  (test-equal (reverse sparse-seq) (fxmapping->decreasing-alist sparse-fxmap))

  (test-eqv #t (null? (fxmapping-keys empty-fxmap)))
  (test-equal (map car mixed-seq) (fxmapping-keys mixed-fxmap))
  (test-equal (map car sparse-seq) (fxmapping-keys sparse-fxmap))

  (test-eqv #t (null? (fxmapping-values empty-fxmap)))
  (test-equal (map cdr mixed-seq) (fxmapping-values mixed-fxmap))
  (test-equal (map cdr sparse-seq) (fxmapping-values sparse-fxmap))

  (test-eqv #t
            (every
             (lambda (im)
               (equal? (fxmapping->alist im)
                       (generator->list (fxmapping->generator im))))
             all-test-fxmaps))
  (test-eqv #t
            (every
             (lambda (im)
               (equal? (fxmapping->decreasing-alist im)
                       (generator->list (fxmapping->decreasing-generator im))))
             all-test-fxmaps))
  )

(test-group "Constructors"
  (test-equal '((1 . a) (2 . b) (3 . c))
              (fxmapping->alist (fxmapping 1 'a 2 'b 3 'c)))

  ;;; unfolds

  (test-eqv #t (null? (fxmapping->alist (fxmapping-unfold
                                         values
                                         (lambda (b) (values 1 b))
                                         (lambda (b) (not b))
                                         #t))))
  (test-equal '((1 . #f)) (fxmapping->alist (fxmapping-unfold
                                             values
                                             (lambda (b) (values 1 b))
                                             (lambda (b) (not b))
                                             #f)))
  (test-equal '((-3 . -3) (-2 . -2) (-1 . -1))
              (fxmapping->alist (fxmapping-unfold
                                 (lambda (i) (< i -3))
                                 (lambda (i) (values i i))
                                 (lambda (i) (- i 1))
                                 -1)))

  (test-eqv #t (null? (fxmapping->alist (fxmapping-unfold-maybe
                                         (lambda (b)
                                           (if b (nothing) (just 1 b (not b))))
                                         #t))))
  (test-equal '((1 . #f))
              (fxmapping->alist (fxmapping-unfold-maybe
                                 (lambda (b)
                                   (if b (nothing) (just 1 b (not b))))
                                 #f)))
  (test-equal '((-3 . -3) (-2 . -2) (-1 . -1))
              (fxmapping->alist
               (fxmapping-unfold-maybe
                (lambda (i)
                  (if (< i -3) (nothing) (just i i (- i 1))))
                -1)))

  ;;; alist->fxmapping

  (test-eqv #t (null? (fxmapping->alist (alist->fxmapping '()))))
  (test-equal mixed-seq (fxmapping->alist (alist->fxmapping mixed-seq)))
  (test-equal sparse-seq (fxmapping->alist (alist->fxmapping sparse-seq)))

  (test-equal '((0 . a) (1 . b) (2 . c))
              (fxmapping->alist
               (alist->fxmapping '((0 . a) (1 . b) (2 . c) (2 . #t)))))

  (test-equal '((0 . a) (1 . b) (2 . #t))
              (fxmapping->alist
               (alist->fxmapping/combinator
                first-arg
                '((0 . a) (1 . b) (2 . c) (2 . #t)))))
  )

(test-group "Predicates"
  (test-eqv #f (fxmapping-contains? empty-fxmap 1))
  (test-eqv #t (fxmapping-contains? letter-fxmap 0))
  (test-eqv #f (fxmapping-contains? letter-fxmap 100))
  (test-eqv #t (fxmapping-contains? sparse-fxmap 4096))
  (test-eqv #f (fxmapping-contains? sparse-fxmap -4097))

  (test-eqv #t (fxmapping-empty? empty-fxmap))
  (test-eqv #f (fxmapping-empty? letter-fxmap))
  (test-eqv #f (fxmapping-empty? mixed-fxmap))
  (test-eqv #f (fxmapping-empty? sparse-fxmap))

  (test-eqv #t (fxmapping-disjoint? empty-fxmap letter-fxmap))
  (test-eqv #t (fxmapping-disjoint? (fxmapping 1 'a) (fxmapping 2 'b)))
  (test-eqv #f (fxmapping-disjoint? (fxmapping 1 'a) (fxmapping 1 'b)))
  )


(test-group "Accessors"
  ;;; lookups

  (test-eqv #t (nothing? (fxmapping-lookup empty-fxmap 1)))
  (test-eqv #t (maybe= eqv? (just 'a) (fxmapping-lookup letter-fxmap 0)))
  (test-eqv #t (maybe= eqv? (just -50) (fxmapping-lookup mixed-fxmap -50)))
  (test-eqv #t (nothing? (fxmapping-lookup mixed-fxmap -51)))
  (test-eqv #t (maybe= eqv? (just 36864) (fxmapping-lookup sparse-fxmap 36864)))
  (test-eqv #t (nothing? (fxmapping-lookup sparse-fxmap 36800)))
  ;; Ensure that false values are not conflated with missing assocs.
  (test-eqv #t (maybe= eqv?
                       (just #f)
                       (fxmapping-lookup (fxmapping 0 #f) 0)))

  (test-eqv -50 (fxmapping-ref mixed-fxmap -50))
  (test-eqv 36864 (fxmapping-ref sparse-fxmap 36864))
  (test-eqv 'z (fxmapping-ref sparse-fxmap 17 (lambda () 'z)))
  (test-eqv 625 (fxmapping-ref mixed-fxmap 25 (lambda () #f) square))

  (test-eqv 'z (fxmapping-ref/default empty-fxmap 1 'z))
  (test-eqv 'a (fxmapping-ref/default letter-fxmap 0 #f))
  (test-eqv -50 (fxmapping-ref/default mixed-fxmap -50 #f))
  (test-eqv 'z (fxmapping-ref/default mixed-fxmap -51 'z))
  (test-eqv 36864 (fxmapping-ref/default sparse-fxmap 36864 #f))
  (test-eqv 'z (fxmapping-ref/default sparse-fxmap 36800 'z))

  ;;; min/max

  (test-eqv #t (nothing? (fxmapping-lookup-min empty-fxmap)))
  (test-equal '(0 a) (maybe-ref (fxmapping-lookup-min letter-fxmap)
                                (lambda () #f)
                                list))
  (test-equal '(-100 -100) (maybe-ref (fxmapping-lookup-min mixed-fxmap)
                                      (lambda () #f)
                                      list))
  (test-equal '(-65536 -65536)
              (maybe-ref (fxmapping-lookup-min sparse-fxmap)
                         (lambda () #f)
                         list))

  (test-equal '(0 a)
              (let-values ((xs (fxmapping-min letter-fxmap)))
                xs))
  (test-equal '(-100 -100)
              (let-values ((xs (fxmapping-min mixed-fxmap)))
                xs))

  (test-eqv #t (nothing? (fxmapping-lookup-max empty-fxmap)))
  (test-equal '(25 z) (maybe-ref (fxmapping-lookup-max letter-fxmap)
                                 (lambda () #f)
                                 list))
  (test-equal '(100 100) (maybe-ref (fxmapping-lookup-max mixed-fxmap)
                                    (lambda () #f)
                                    list))
  (test-equal '(65536 65536)
              (maybe-ref (fxmapping-lookup-max sparse-fxmap)
                         (lambda () #f)
                         list))

  (test-equal '(25 z)
              (let-values ((xs (fxmapping-max letter-fxmap)))
                xs))
  (test-equal '(100 100)
              (let-values ((xs (fxmapping-max mixed-fxmap)))
                xs))
  )

(test-group "Updaters"
  ;;; adjoins

  (test-eqv #t (fxmapping=? default-comp
                            (fxmapping 0 'a)
                            (fxmapping-adjoin empty-fxmap 0 'a)))
  (test-eqv #t (fxmapping-contains? (fxmapping-adjoin mixed-fxmap 200 #t) 200))
  (test-eqv #t (fxmapping-contains? (fxmapping-adjoin sparse-fxmap -200 #t)
                                    -200))
  (test-eqv #t (fxmapping=? default-comp
                            (fxmapping 0 'a 1 'b 2 'c)
                            (fxmapping-adjoin empty-fxmap 0 'a 1 'b 2 'c)))
  (test-eqv (fxmapping-ref sparse-fxmap -4096)
            (fxmapping-ref (fxmapping-adjoin sparse-fxmap -4096 'z) -4096))

  (test-eqv 'U (fxmapping-ref/default
                (fxmapping-adjoin/combinator letter-fxmap first-arg 20 'U)
                20
                #f))
  (test-eqv 'u (fxmapping-ref/default
                (fxmapping-adjoin/combinator letter-fxmap second-arg 20 'U)
                20
                #f))
  (test-eqv #t
            (fxmapping=?
             default-comp
             (fxmapping 0 'a 1 'b 2 'c)
             (fxmapping-adjoin/combinator empty-fxmap
                                          first-arg
                                          0 'a 1 'b 2 'c)))

  ;;; set

  (test-eqv #t (fxmapping=? default-comp
                            (fxmapping 0 'a)
                            (fxmapping-set empty-fxmap 0 'a)))
  (test-eqv #t (fxmapping-contains? (fxmapping-set mixed-fxmap 200 #t) 200))
  (test-eqv #t (fxmapping-contains? (fxmapping-set sparse-fxmap -200 #t) -200))
  (test-eqv #t (fxmapping=? default-comp
                            (fxmapping 0 'a 1 'b 2 'c)
                            (fxmapping-set empty-fxmap 0 'a 1 'b 2 'c)))
  (test-eqv 'z
            (fxmapping-ref (fxmapping-set sparse-fxmap -4096 'z) -4096))

  ;;; adjusts

  (test-equal '(20 u) (fxmapping-ref/default
                       (fxmapping-adjust letter-fxmap 20 list)
                       20
                       #f))
  (test-eqv 16384 (fxmapping-ref/default
                   (fxmapping-adjust sparse-fxmap
                                     8192
                                     (lambda (k v) (+ k v)))
                   8192
                   #f))
  (test-eqv #t (fxmapping-empty? (fxmapping-adjust empty-fxmap 1 list)))

  ;;; delete & delete-all

  (test-eqv #f (fxmapping-contains? (fxmapping-delete letter-fxmap 10) 10))
  (test-eqv #f (fxmapping-contains? (fxmapping-delete mixed-fxmap 50) 50))
  (test-eqv #t (fxmapping=? default-comp
                            mixed-fxmap
                            (fxmapping-delete mixed-fxmap 1)))
  (let* ((ks '(4096 8192 16384))
         (sm (apply fxmapping-delete sparse-fxmap ks)))
    (test-eqv #f (any (lambda (k) (fxmapping-contains? sm k)) ks)))

  (test-eqv #f (fxmapping-contains? (fxmapping-delete-all letter-fxmap '(10))
                                    10))
  (test-eqv #f (fxmapping-contains? (fxmapping-delete-all mixed-fxmap '(50))
                                    50))
  (test-eqv #t (fxmapping=? default-comp
                            mixed-fxmap
                            (fxmapping-delete-all mixed-fxmap '(1))))
  (let* ((ks '(4096 8192 16384))
         (sm (fxmapping-delete-all sparse-fxmap ks)))
    (test-eqv #f (any (lambda (k) (fxmapping-contains? sm k)) ks)))

  ;;; update

  (test-eqv #t (fxmapping=?
                default-comp
                (fxmapping 0 '(0 a))
                (fxmapping-update (fxmapping 0 'a)
                                  0
                                  (lambda (k v) (just (list k v))))))
  (test-eqv 'U (fxmapping-ref/default
                (fxmapping-update letter-fxmap 20 (constantly (just 'U)))
                20
                #f))
  (test-eqv #f (fxmapping-contains?
                (fxmapping-update letter-fxmap 20 (constantly (nothing)))
                20))
  (test-eqv #f (fxmapping-contains?
                (fxmapping-update sparse-fxmap -8192 (constantly (nothing)))
                -8192))

  ;;; alter

  (test-eqv #t (fxmapping=? default-comp
                            (fxmapping 0 'a)
                            (fxmapping-alter (fxmapping 0 'a)
                                            1
                                            (constantly (nothing)))))
  (test-eqv #t (fxmapping=? default-comp
                            (fxmapping 0 'a 1 'b)
                            (fxmapping-alter (fxmapping 0 'a)
                                            1
                                            (constantly (just 'b)))))
  (test-eqv 101 (fxmapping-ref/default
                 (fxmapping-alter mixed-fxmap
                                  101
                                  (constantly (just 101)))
                 101
                 #f))
  (test-eqv 101 (fxmapping-ref/default
                 (fxmapping-alter mixed-fxmap
                                  100
                                  (lambda (m)
                                    (maybe-map (lambda (_k n) (+ n 1)) m)))
                 100
                 #f))
  (test-eqv 'z (fxmapping-ref/default
                (fxmapping-alter mixed-fxmap
                                 100
                                 (constantly (nothing)))
                100
                'z))
  (test-eqv -16383 (fxmapping-ref/default
                    (fxmapping-alter sparse-fxmap
                                     -16384
                                     (lambda (m)
                                       (maybe-map (lambda (_k n) (+ n 1)) m)))
                    -16384
                    #f))
  (test-eqv 'z (fxmapping-ref/default
                (fxmapping-alter sparse-fxmap
                                 -16384
                                 (constantly (nothing)))
                -16384
                'z))

  ;;; delete-min/-max

  (test-eqv #t (fxmapping=? default-comp
                            empty-fxmap
                            (fxmapping-delete-min (fxmapping 0 'a))))
  (test-eqv #f (fxmapping-contains? (fxmapping-delete-min letter-fxmap) 0))
  (test-eqv #f (fxmapping-contains? (fxmapping-delete-min sparse-fxmap) -65536))

  (test-eqv #t (fxmapping=? default-comp
                            empty-fxmap
                            (fxmapping-delete-max (fxmapping 0 'a))))
  (test-eqv #f (fxmapping-contains? (fxmapping-delete-max letter-fxmap) 25))
  (test-eqv #f (fxmapping-contains? (fxmapping-delete-max sparse-fxmap) 65536))

  ;;; min updaters

  (test-eqv -200 (fxmapping-ref/default
                    (fxmapping-update-min mixed-fxmap
                                         (lambda (k v) (just (+ k v))))
                    -100
                    #f))
  (test-equal '(0 a)
              (fxmapping-ref/default
               (fxmapping-update-min letter-fxmap
                                     (lambda (k v) (just (list k v))))
               0
               #f))

  ;;; max updaters

  (test-eqv 200 (fxmapping-ref/default
                 (fxmapping-update-max mixed-fxmap
                                       (lambda (k v) (just (+ k v))))
                 100
                 #f))
  (test-equal '(25 z)
              (fxmapping-ref/default
               (fxmapping-update-max letter-fxmap
                                     (lambda (k v) (just (list k v))))
               25
               #f))

  ;;; pop-min

  (test-eqv #t (nothing? (fxmapping-pop-min empty-fxmap)))
  (test-eqv #t
            (every
             (lambda (im)
               (let-values (((k v im*)
                             (maybe-ref/default (fxmapping-pop-min im) #f))
                            ((test-k test-v)
                             (maybe-ref/default (fxmapping-lookup-min im) #f)))
                 (and (= k test-k)
                      (eqv? v test-v)
                      (fxmapping=? default-comp
                                   (fxmapping-delete-min im)
                                   im*))))
             (list mixed-fxmap letter-fxmap sparse-fxmap)))  ; non-empty only

  ;;; pop-max

  (test-eqv #t (nothing? (fxmapping-pop-max empty-fxmap)))
  (test-eqv #t
            (every
             (lambda (im)
               (let-values (((k v im*)
                             (maybe-ref/default (fxmapping-pop-max im) #f))
                            ((test-k test-v)
                             (maybe-ref/default (fxmapping-lookup-max im) #f)))
                 (and (= k test-k)
                      (eqv? v test-v)
                      (fxmapping=? default-comp
                                   (fxmapping-delete-max im)
                                   im*))))
             (list mixed-fxmap letter-fxmap sparse-fxmap)))  ; non-empty only
  )

(test-group "Whole fxmappings"
  (test-eqv 0 (fxmapping-size empty-fxmap))
  (test-eqv 26 (fxmapping-size letter-fxmap))

  ;;; find

  (test-eqv 'z (fxmapping-find even? empty-fxmap (constantly 'z)))
  (test-equal '(0 a)
              (let-values ((p (fxmapping-find (lambda (_ v) (symbol? v))
                                              letter-fxmap
                                              (lambda () (values #f #f)))))
                p))
  (let ((ss '(f r o b)))
    (test-equal '(1 b)
                (let-values ((p (fxmapping-find (lambda (_ s) (memv s ss))
                                                letter-fxmap
                                                (lambda ()
                                                  (values #f #f)))))
                  p)))
  (test-equal '(4096 4096)
              (let-values ((p (fxmapping-find (lambda (_ v) (positive? v))
                                              sparse-fxmap
                                              (lambda () (values #f #f)))))
                p))
  ;; Ensure negative-keyed associations are tested first.
  (test-equal '(-65536 -65536)
              (let-values ((p (fxmapping-find (lambda (_ v) (integer? v))
                                              sparse-fxmap
                                              (lambda () (values #f #f)))))
                p))
  (test-equal '(z z)
              (let-values
               ((p (fxmapping-find eqv?
                                   letter-fxmap
                                   (lambda () (values 'z 'z)))))
                p))

  ;;; query

  (test-eqv 'z (maybe-ref/default
                (fxmapping-query (lambda (_ v) (even? v)) empty-fxmap) 'z))
  (test-equal '(0 a)
              (maybe->list
               (fxmapping-query (lambda (_ v) (symbol? v)) letter-fxmap)))
  (let ((ss '(f r o b)))
    (test-equal '(1 b)
                (maybe->list
                 (fxmapping-query (lambda (_ s) (memv s ss))
                                  letter-fxmap))))
  (test-equal '(4096 4096)
              (maybe->list
               (fxmapping-query (lambda (_ v) (positive? v)) sparse-fxmap)))
  ;; Ensure negative-keyed associations are tested first.
  (test-equal '(-65536 -65536)
              (maybe->list
               (fxmapping-query (lambda (_ v) (integer? v)) sparse-fxmap)))
  (test-equal '() (maybe->list (fxmapping-query eqv? letter-fxmap)))

  ;;; count

  (test-eqv 0 (fxmapping-count (lambda (_ v) (even? v)) empty-fxmap))
  (test-eqv 26 (fxmapping-count (lambda (_ v) (symbol? v)) letter-fxmap))
  (let ((ss '(f r o b)))
    (test-eqv (length ss)
              (fxmapping-count (lambda (_ s) (memv s ss)) letter-fxmap))
    (test-eqv (- (fxmapping-size letter-fxmap) (length ss))
              (fxmapping-count (lambda (_ s) (not (memv s ss))) letter-fxmap)))
  (test-eqv 4 (fxmapping-count (lambda (_ v) (positive? v)) mixed-fxmap))
  (test-eqv 2 (fxmapping-count (lambda (k v) (and (even? k) (positive? v)))
                               mixed-fxmap))

  ;;; any?/every?

  (test-eqv #f (fxmapping-any? (lambda (_ v) (even? v)) empty-fxmap))
  (test-eqv #t (fxmapping-any? (lambda (_ v) (positive? v)) mixed-fxmap))
  (test-eqv #f (fxmapping-any? (lambda (_ v) (odd? v)) sparse-fxmap))
  (test-eqv #t (fxmapping-any? (lambda (_ v) (negative? v)) sparse-fxmap))

  (test-eqv #t (fxmapping-every? (lambda (_ v) (even? v)) empty-fxmap))
  (test-eqv #f (fxmapping-every? (lambda (_ v) (positive? v)) mixed-fxmap))
  (test-eqv #t (fxmapping-every? (lambda (_ v) (even? v)) sparse-fxmap))
  (test-eqv #f (fxmapping-every? (lambda (_ v) (negative? v)) sparse-fxmap))
  )

(test-group "Iterators"
  ;;; map

  (test-eqv #t (fxmapping=? default-comp
                            empty-fxmap
                            (fxmapping-map (constantly #t) empty-fxmap)))
  (test-eqv #t (fxmapping=? default-comp
                            mixed-fxmap
                            (fxmapping-map (nth 1) mixed-fxmap)))
  (test-eqv #t (fxmapping=? default-comp
                            (fxmapping 0 "" 1 "b" 2 "cc")
                            (fxmapping-map make-string
                                          (fxmapping 0 #\a 1 #\b 2 #\c))))

  ;;; for-each

  (test-eqv 26
            (let ((size 0))
              (fxmapping-for-each (lambda (_k _v) (set! size (+ size 1)))
                                  letter-fxmap)
              size))
  (test-equal '(c b a)
              (let ((xs '()))
                (fxmapping-for-each (lambda (_ x) (set! xs (cons x xs)))
                                    (fxmapping 0 'a 1 'b 2 'c))
                xs))
  (test-equal '((2 . c) (1 . b) (0 . a))
              (let ((xs '()))
                (fxmapping-for-each
                 (lambda (k x) (set! xs (cons (cons k x) xs)))
                 (fxmapping 0 'a 1 'b 2 'c))
                xs))

  ;;; fold

  (test-eqv 'z (fxmapping-fold (nth 2) 'z empty-fxmap))
  (test-equal (reverse '(a b c d e f g h i j k l m n o p q r s t u v w x y z))
              (fxmapping-fold (lambda (_ v vs) (cons v vs))
                              '()
                              letter-fxmap))
  (test-equal (reverse (iota 9 -100 25))
              (fxmapping-fold (lambda (_ v vs) (cons v vs))
                             '()
                             mixed-fxmap))
  (test-eqv (fold + 0 (iota 9 -100 25))
            (fxmapping-fold (lambda (_ v sum) (+ v sum))
                            0
                            mixed-fxmap))
  (test-equal (reverse '((0 . "") (1 . "b") (2 . "cc")))
              (fxmapping-fold (lambda (k c as)
                                (cons (cons k (make-string k c)) as))
                              '()
                              (fxmapping 0 #\a 1 #\b 2 #\c)))

  ;;; fold-right

  (test-eqv 'z (fxmapping-fold-right (nth 2) 'z empty-fxmap))
  (test-equal '(a b c d e f g h i j k l m n o p q r s t u v w x y z)
              (fxmapping-fold-right (lambda (_ v vs) (cons v vs))
                                    '()
                                    letter-fxmap))
  (test-equal (iota 9 -100 25)
              (fxmapping-fold-right (lambda (_ v vs) (cons v vs))
                                    '()
                                    mixed-fxmap))
  (test-eqv (fold + 0 (iota 9 -100 25))
            (fxmapping-fold-right (lambda (_ v sum) (+ v sum))
                                  0
                                  mixed-fxmap))
  (test-equal '((0 . "") (1 . "b") (2 . "cc"))
              (fxmapping-fold-right (lambda (k c as)
                                      (cons (cons k (make-string k c)) as))
                                    '()
                                    (fxmapping 0 #\a 1 #\b 2 #\c)))

  ;;; map->list

  (test-eqv #t (null? (fxmapping-map->list (constantly #t) empty-fxmap)))
  (test-equal '(a b c d e f g h i j k l m n o p q r s t u v w x y z)
              (fxmapping-map->list (nth 1) letter-fxmap))
  (test-equal (map square (iota 9 -100 25))
              (fxmapping-map->list (lambda (_ v) (square v)) mixed-fxmap))
  (test-equal '("" "a" "aa")
              (fxmapping-map->list (lambda (_ n) (make-string n #\a))
                                   (fxmapping 0 0 1 1 2 2)))
  (test-equal (iota 26) (fxmapping-map->list (nth 0) letter-fxmap))
  (test-equal '((0 . "") (1 . "b") (2 . "cc"))
              (fxmapping-map->list (lambda (k c) (cons k (make-string k c)))
                                   (fxmapping 0 #\a 1 #\b 2 #\c)))

  ;;; filter-map

  ;; filter-map is equivalent to map if the mapped procedure
  ;; always returns a truthy value.  (Ignoring side-effects.)
  (test-eqv #t (fxmapping=? default-comp
                            empty-fxmap
                            (fxmapping-filter-map (constantly #t)
                                                  empty-fxmap)))
  (test-eqv #t (fxmapping=? default-comp
                            mixed-fxmap
                            (fxmapping-filter-map (nth 1) mixed-fxmap)))
  (test-eqv #t (fxmapping=? default-comp
                            (fxmapping 0 "" 1 "b" 2 "cc")
                            (fxmapping-filter-map
                             make-string
                             (fxmapping 0 #\a 1 #\b 2 #\c))))
  ;; filter-map empties a mapping if the mapped proc always returns #f.
  (test-eqv #t
            (every fxmapping-empty?
                   (map (lambda (m) (fxmapping-filter-map (constantly #f) m))
                        all-test-fxmaps)))
  ;; Using filter-map as filter.
  (test-equal (filter (lambda (p) (even? (cdr p))) mixed-seq)
              (fxmapping->alist
               (fxmapping-filter-map (lambda (k v) (and (even? v) v))
                                     mixed-fxmap)))
  ;; Filtering and transforming the values of a mapping.
  (test-equal (filter-map (lambda (p)
                            (let ((k (car p)) (v (cdr p)))
                              (and (even? k) (cons k (+ k v)))))
                          sparse-seq)
              (fxmapping->alist
               (fxmapping-filter-map (lambda (k v)
                                       (and (even? k) (+ k v)))
                                     sparse-fxmap)))

  ;;; map-either

  ;; Mapping `left' with map-either copies the fxmapping argument as
  ;; the first returned value.
  (test-eqv #t
            (every
             (lambda (im)
               (fxmapping=? default-comp
                           im
                           (let-values (((lm rm)
                                         (fxmapping-map-either
                                          (lambda (_ v) (left v))
                                          im)))
                             lm)))
             (list empty-fxmap letter-fxmap mixed-fxmap sparse-fxmap)))
  ;; Mapping `right' with map-either copies the fxmapping argument as
  ;; the second returned value.
  (test-eqv #t
            (every
             (lambda (im)
               (fxmapping=? default-comp
                           im
                           (let-values (((lm rm)
                                         (fxmapping-map-either
                                          (lambda (_ v) (right v))
                                          im)))
                             rm)))
             (list empty-fxmap letter-fxmap mixed-fxmap sparse-fxmap)))
  ;; Using map-either to partition an fxmapping.
  (test-eqv #t
            (let-values (((neg pos)
                          (fxmapping-map-either
                           (lambda (_ n)
                             (if (negative? n) (left n) (right n)))
                           sparse-fxmap)))
              (and (fxmapping-every? (lambda (_ x) (negative? x)) neg)
                   (fxmapping-every? (lambda (_ x) (not (negative? x))) pos))))
  ;; Using map-either to split and transform an fxmapping.
  (test-eqv #t
            (let-values (((lm rm)
                          (fxmapping-map-either
                           (lambda (k n)
                             (if (negative? n)
                                 (left (+ k (abs n)))
                                 (right (+ k n))))
                           (fxmapping -2 -2 -1 -1 3 3 5 5))))
              (and (fxmapping=? default-comp lm (fxmapping -2 0 -1 0))
                   (fxmapping=? default-comp rm (fxmapping 3 6 5 10)))))
  )

(test-group "Filters"
  (test-eqv #t
            (every values
                   (map (lambda (m)
                          (fxmapping=? default-comp
                                       m
                                       (fxmapping-filter (constantly #t) m)))
                        all-test-fxmaps)))
  (test-eqv #t
            (every fxmapping-empty?
                   (map (lambda (m) (fxmapping-filter (constantly #f) m))
                        all-test-fxmaps)))
  (test-eqv #t (fxmapping=? default-comp
                           (fxmapping 25 25 75 75)
                           (fxmapping-filter (lambda (k v)
                                               (and (odd? k) (positive? v)))
                                             mixed-fxmap)))

  ;;; remove

  (test-eqv #t
            (every (lambda (m)
                     (fxmapping=? default-comp
                                  m
                                  (fxmapping-remove (constantly #f) m)))
                   all-test-fxmaps))
  (test-eqv #t
            (every fxmapping-empty?
                   (map (lambda (m) (fxmapping-remove (constantly #t) m))
                        all-test-fxmaps)))
  (test-eqv #t
            (fxmapping=? default-comp
                         (fxmapping -100 -100 -50 -50 0 0)
                         (fxmapping-remove (lambda (k v)
                                             (or (odd? k) (positive? v)))
                                           mixed-fxmap)))

  ;;; partition

  (test-eqv #t
            (every (lambda (m)
                     (fxmapping=?
                      default-comp
                      m
                      (value/mv 0 (fxmapping-partition (constantly #t) m))))
                   all-test-fxmaps))
  (test-equal (call-with-values
               (lambda () (partition even? (map car mixed-seq)))
               list)
              (let-values (((em om)
                            (fxmapping-partition (lambda (_ v) (even? v))
                                                 mixed-fxmap)))
                (list (fxmapping-values em) (fxmapping-values om))))
  (test-eqv #t
            (let-values (((zm not-zm)
                          (fxmapping-partition (lambda (_ s) (eqv? s 'z))
                                               letter-fxmap)))
              (and (fxmapping=? default-comp zm (fxmapping 25 'z))
                   (fxmapping=? default-comp
                                not-zm
                                (fxmapping-delete letter-fxmap 25)))))
  (test-equal (unfold (lambda (i) (= i 26))
                      (lambda (i)
                        (string->symbol (string (integer->char (+ i #x61)))))
                      (lambda (i) (+ i 2))
                      0)
              (let-values (((em _)
                            (fxmapping-partition (lambda (k _) (even? k))
                                                 letter-fxmap)))
                (fxmapping-values em)))
  )

(test-group "Comparison"
  (let ((subfxmap (fxmapping-filter (lambda (_ v) (even? v)) mixed-fxmap)))
    (test-eqv #t (fxmapping<? default-comp (fxmapping) mixed-fxmap))
    (test-eqv #t (fxmapping<? default-comp subfxmap mixed-fxmap))
    (test-eqv #f (fxmapping<? default-comp mixed-fxmap subfxmap))
    (test-eqv #f (fxmapping<? default-comp mixed-fxmap mixed-fxmap))
    (test-eqv #f (fxmapping<? default-comp
                              (fxmapping 0 'z)
                              (fxmapping 0 'a 1 'b)))

    (test-eqv #t (fxmapping>? default-comp mixed-fxmap (fxmapping)))
    (test-eqv #f (fxmapping>? default-comp subfxmap mixed-fxmap))
    (test-eqv #t (fxmapping>? default-comp mixed-fxmap subfxmap))
    (test-eqv #f (fxmapping>? default-comp mixed-fxmap mixed-fxmap))
    (test-eqv #f (fxmapping>? default-comp
                              (fxmapping 0 'z 1 'b)
                              (fxmapping 0 'a)))

    (test-eqv #t (fxmapping<=? default-comp (fxmapping) mixed-fxmap))
    (test-eqv #t (fxmapping<=? default-comp subfxmap mixed-fxmap))
    (test-eqv #f (fxmapping<=? default-comp mixed-fxmap subfxmap))
    (test-eqv #t (fxmapping<=? default-comp mixed-fxmap mixed-fxmap))
    (test-eqv #f (fxmapping<=? default-comp
                               (fxmapping 0 'z 1 'b)
                               (fxmapping 0 'a 1 'b)))

    (test-eqv #t (fxmapping>=? default-comp mixed-fxmap (fxmapping)))
    (test-eqv #f (fxmapping>=? default-comp subfxmap mixed-fxmap))
    (test-eqv #t (fxmapping>=? default-comp mixed-fxmap subfxmap))
    (test-eqv #t (fxmapping>=? default-comp mixed-fxmap mixed-fxmap))
    (test-eqv #f (fxmapping<=? default-comp
                               (fxmapping 0 'z 1 'b)
                               (fxmapping 0 'a 1 'b)))

    ;; Variadic comparisons.
    (let ((subfxmap1 (fxmapping-filter (lambda (_ v) (positive? v)) subfxmap)))
      (test-eqv #t (fxmapping<? default-comp subfxmap1 subfxmap mixed-fxmap))
      (test-eqv #f (fxmapping<? default-comp subfxmap1 empty-fxmap mixed-fxmap))

      (test-eqv #t (fxmapping>? default-comp mixed-fxmap subfxmap subfxmap1))
      (test-eqv #f (fxmapping>? default-comp mixed-fxmap empty-fxmap subfxmap1))

      (test-eqv #t (fxmapping<=? default-comp
                                 subfxmap1
                                 subfxmap
                                 subfxmap
                                 mixed-fxmap))
      (test-eqv #f
                (fxmapping<=? default-comp subfxmap1 empty-fxmap mixed-fxmap))

      (test-eqv #t (fxmapping>=? default-comp
                                 mixed-fxmap
                                 subfxmap
                                 subfxmap
                                 subfxmap1))
      (test-eqv #f
                (fxmapping>=? default-comp mixed-fxmap empty-fxmap subfxmap1))
      ))
  )

(test-group "Set theory"
  (let ((fxmap1 (fxmapping -5 'a -2 'b 1 'c))
        (fxmap2 (fxmapping -2 'b 3 'd 5 'e))
        (fxmap3 (fxmapping 3 'd 5 'g 7 'f)))  ; assoc for 5 differs from fxmap2
    (test-eqv #t (fxmapping=? default-comp
                              sparse-fxmap
                              (fxmapping-union sparse-fxmap empty-fxmap)))
    (test-eqv #t (fxmapping=? default-comp
                              (fxmapping -5 'a -2 'b 1 'c 3 'd 5 'e)
                              (fxmapping-union fxmap1 fxmap2)))
    (test-eqv #t (fxmapping=? default-comp
                              (fxmapping -2 'b 3 'd 5 'e 7 'f)
                              (fxmapping-union fxmap2 fxmap3)))
    (test-eqv #t (fxmapping=? default-comp
                              (fxmapping -5 'a -2 'b 1 'c 3 'd 5 'e 7 'f)
                              (fxmapping-union fxmap1 fxmap2 fxmap3)))

    (test-eqv #t (fxmapping-empty?
                  (fxmapping-intersection sparse-fxmap empty-fxmap)))
    (test-eqv #t (fxmapping=? default-comp
                              (fxmapping -2 'b)
                              (fxmapping-intersection fxmap1 fxmap2)))
    (test-eqv #t (fxmapping=? default-comp
                              (fxmapping 3 'd 5 'e)
                              (fxmapping-intersection fxmap2 fxmap3)))
    (test-eqv #t (fxmapping=?
                  default-comp
                  (fxmapping -2 'b)
                  (fxmapping-intersection fxmap1 fxmap2 (fxmapping -2 'b))))

    (test-eqv #t (fxmapping=? default-comp
                              sparse-fxmap
                              (fxmapping-difference sparse-fxmap empty-fxmap)))
    (test-eqv #t (fxmapping=? default-comp
                              (fxmapping -5 'a 1 'c)
                              (fxmapping-difference fxmap1 fxmap2)))
    (test-eqv #t (fxmapping=? default-comp
                              (fxmapping -2 'b)
                              (fxmapping-difference fxmap2 fxmap3)))
    (test-eqv #t (fxmapping=? default-comp
                              (fxmapping -5 'a 1 'c)
                              (fxmapping-difference fxmap1 fxmap2 fxmap3)))

    (test-eqv #t (fxmapping=? default-comp
                              sparse-fxmap
                              (fxmapping-xor sparse-fxmap empty-fxmap)))
    (test-eqv #t (fxmapping=? default-comp
                              (fxmapping -5 'a 1 'c 3 'd 5 'e)
                              (fxmapping-xor fxmap1 fxmap2)))
    (test-eqv #t (fxmapping=? default-comp
                              (fxmapping -2 'b 7 'f)
                              (fxmapping-xor fxmap2 fxmap3)))

    ;;; /combinator variants

    (test-eqv #t (fxmapping=? default-comp
                             sparse-fxmap
                             (fxmapping-union/combinator second-arg
                                                         sparse-fxmap
                                                         empty-fxmap)))
    (test-eqv #t (fxmapping=?
                  default-comp
                  (fxmapping -2 'b 3 'd 5 'g 7 'f)
                  (fxmapping-union/combinator second-arg fxmap2 fxmap3)))
    (test-eqv #t (fxmapping=?
                  default-comp
                  (fxmapping -5 'a -2 'b 1 'c 3 'd 5 'g 7 'f)
                  (fxmapping-union/combinator second-arg fxmap1 fxmap2 fxmap3)))
    (test-eqv #t (fxmapping=?
                  default-comp
                  (fxmapping 0 "abc")
                  (fxmapping-union/combinator (lambda (_ s t)
                                                (string-append s t))
                                              (fxmapping 0 "a")
                                              (fxmapping 0 "b")
                                              (fxmapping 0 "c"))))

    (test-eqv #t (fxmapping=? default-comp
                             empty-fxmap
                             (fxmapping-intersection/combinator second-arg
                                                                sparse-fxmap
                                                                empty-fxmap)))
    (test-eqv #t (fxmapping=?
                  default-comp
                  (fxmapping 3 'd 5 'g)
                  (fxmapping-intersection/combinator second-arg fxmap2 fxmap3)))
    (test-eqv #t (fxmapping=?
                  default-comp
                  (fxmapping -2 'z)
                  (fxmapping-intersection/combinator second-arg
                                                     fxmap1
                                                     fxmap2
                                                     (fxmapping -2 'z))))
    (test-eqv #t (fxmapping=?
                  default-comp
                  (fxmapping 0 "abc")
                  (fxmapping-intersection/combinator (lambda (_ s t)
                                                       (string-append s t))
                                                     (fxmapping 0 "a")
                                                     (fxmapping 0 "b")
                                                     (fxmapping 0 "c"))))
    ))

(test-group "Intervals"
  (test-equal (list->dup-alist '(-25 0 25))
              (fxmapping->alist
               (fxmapping-open-interval mixed-fxmap -50 50)))
  (test-equal '((6 . g) (7 . h) (8 . i) (9 . j))
              (fxmapping->alist
               (fxmapping-open-interval letter-fxmap 5 10)))
  (test-equal (list->dup-alist '(-8192 -4096 0 4096 8192))
              (fxmapping->alist
               (fxmapping-open-interval sparse-fxmap -12288 12288)))

  (test-equal (list->dup-alist '(-50 -25 0 25 50))
              (fxmapping->alist
               (fxmapping-closed-interval mixed-fxmap -50 50)))
  (test-equal '((5 . f) (6 . g) (7 . h) (8 . i) (9 . j) (10 . k))
              (fxmapping->alist
               (fxmapping-closed-interval letter-fxmap 5 10)))
  (test-equal (list->dup-alist '(-12288 -8192 -4096 0 4096 8192 12288))
              (fxmapping->alist
               (fxmapping-closed-interval sparse-fxmap -12288 12288)))

  (test-equal (list->dup-alist '(-25 0 25 50))
              (fxmapping->alist
               (fxmapping-open-closed-interval mixed-fxmap -50 50)))
  (test-equal '((6 . g) (7 . h) (8 . i) (9 . j) (10 . k))
              (fxmapping->alist
               (fxmapping-open-closed-interval letter-fxmap 5 10)))
  (test-equal (list->dup-alist '(-8192 -4096 0 4096 8192 12288))
              (fxmapping->alist
               (fxmapping-open-closed-interval sparse-fxmap -12288 12288)))

  (test-equal (list->dup-alist '(-50 -25 0 25))
              (fxmapping->alist
               (fxmapping-closed-open-interval mixed-fxmap -50 50)))
  (test-equal '((5 . f) (6 . g) (7 . h) (8 . i) (9 . j))
              (fxmapping->alist
               (fxmapping-closed-open-interval letter-fxmap 5 10)))
  (test-equal (list->dup-alist '(-12288 -8192 -4096 0 4096 8192))
              (fxmapping->alist
               (fxmapping-closed-open-interval sparse-fxmap -12288 12288)))
  )

(test-group "Submappings"
  (test-equal '((100 . 100)) (fxmapping->alist (fxsubmapping= mixed-fxmap 100)))
  (test-equal '((7 . h)) (fxmapping->alist (fxsubmapping= letter-fxmap 7)))
  (test-equal '((16384 . 16384))
              (fxmapping->alist (fxsubmapping= sparse-fxmap 16384)))
  (test-eqv #t (fxmapping-empty? (fxsubmapping= sparse-fxmap 1)))

  (test-equal (list->dup-alist '(-100 -75 -50 -25))
              (fxmapping->alist (fxsubmapping< mixed-fxmap 0)))
  (test-equal '((0 . a) (1 . b) (2 . c))
              (fxmapping->alist (fxsubmapping< letter-fxmap 3)))
  (test-equal (list->dup-alist '(-65536 -61440 -57344))
              (fxmapping->alist (fxsubmapping< sparse-fxmap -53248)))

  (test-equal (list->dup-alist '(25 50 75 100))
              (fxmapping->alist (fxsubmapping> mixed-fxmap 0)))
  (test-equal '((23 . x) (24 . y) (25 . z))
              (fxmapping->alist (fxsubmapping> letter-fxmap 22)))
  (test-equal (list->dup-alist '(57344 61440 65536))
              (fxmapping->alist (fxsubmapping> sparse-fxmap 53248)))

  (test-equal (list->dup-alist '(-100 -75 -50 -25 0))
              (fxmapping->alist (fxsubmapping<= mixed-fxmap 0)))
  (test-equal '((0 . a) (1 . b) (2 . c) (3 . d))
              (fxmapping->alist (fxsubmapping<= letter-fxmap 3)))
  (test-equal (list->dup-alist '(-65536 -61440 -57344 -53248))
              (fxmapping->alist (fxsubmapping<= sparse-fxmap -53248)))

  (test-equal (list->dup-alist '(0 25 50 75 100))
              (fxmapping->alist (fxsubmapping>= mixed-fxmap 0)))
  (test-equal '((22 . w) (23 . x) (24 . y) (25 . z))
              (fxmapping->alist (fxsubmapping>= letter-fxmap 22)))
  (test-equal (list->dup-alist '(53248 57344 61440 65536))
              (fxmapping->alist (fxsubmapping>= sparse-fxmap 53248)))

  (test-equal (list (list->dup-alist (iota 5 -100 25))
                    (list->dup-alist (iota 4 25 25)))
              (let-values ((fxmaps (fxmapping-split mixed-fxmap 0)))
                (map fxmapping->alist fxmaps)))
  (test-equal (list '() sparse-seq)
              (maybe-ref
               (fxmapping-lookup-min sparse-fxmap)
               (constantly #f)
               (lambda (min-key _)
                 (let-values ((fxmaps (fxmapping-split sparse-fxmap
                                                       (- min-key 1))))
                   (map fxmapping->alist fxmaps)))))
  (test-equal (list sparse-seq '())
              (maybe-ref
               (fxmapping-lookup-max sparse-fxmap)
               (constantly #f)
               (lambda (max-key _)
                 (let-values ((fxmaps (fxmapping-split sparse-fxmap
                                                       (+ max-key 1))))
                   (map fxmapping->alist fxmaps)))))
  )

(test-group "Relation map"
  (test-eqv #t
            (fxmapping=? default-comp
                         (fxmapping 0 #t)
                         (fxmapping-relation-map (lambda (_k _v) (values 0 #t))
                                                 letter-fxmap)))
  (test-eqv #t
            (fxmapping=? default-comp
                         letter-fxmap
                         (fxmapping-relation-map values letter-fxmap)))
  (test-equal '((0 . a) (1 . b) (2 . c))
              (fxmapping->alist
               (fxmapping-relation-map (lambda (k v) (values (- k) v))
                                       (fxmapping 0 'a -1 'b -2 'c))))
  )

(test-group "Copying"
  (test-eqv #t
            (every
             (lambda (im) (fxmapping=? default-comp im (fxmapping-copy im)))
             all-test-fxmaps))
  )
