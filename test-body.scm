;;;; Utility

(define default-comp (make-default-comparator))

(define (constantly x) (lambda _ x))

(define (first x _) x)
(define (second _ y) y)
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

;;;; Test imappings

(define empty-imap (imapping))

(define letter-imap
  (let* ((cs "abcdefghijklmnopqrstuvwxyz")
         (len (string-length cs)))
    (imapping-unfold
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

(define mixed-imap (alist->imapping mixed-seq))

;; From -65536 to 65536 in steps of 4096.  Key = value.
(define sparse-seq
  (unfold (lambda (i) (> i 65536))
          (lambda (i) (cons i i))
          (lambda (i) (+ i 4096))
          -65536))

(define sparse-imap (alist->imapping sparse-seq))

(define all-test-imaps
  (list empty-imap mixed-imap letter-imap sparse-imap))

;;; imapping=? and the alist conversions are used in many other tests,
;;; so we test these first.  These also test the basic imapping
;;; constructor.

(test-group "Equality"
  (test-eqv #t (imapping=? default-comp empty-imap (imapping)))
  (test-eqv #t (imapping=? default-comp (imapping 10 'a) (imapping 10 'a)))
  (test-eqv #f (imapping=? default-comp empty-imap (imapping 10 'a)))
  (test-eqv #t (imapping=? default-comp mixed-imap mixed-imap))
  (test-eqv #t (imapping=? default-comp letter-imap letter-imap))
  )

(test-group "Conversion"
  (test-eqv #t (null? (imapping->alist empty-imap)))
  (test-equal '((10 . a)) (imapping->alist (imapping 10 'a)))
  (test-equal mixed-seq (imapping->alist mixed-imap))
  (test-equal sparse-seq (imapping->alist sparse-imap))

  (test-eqv #t (null? (imapping->decreasing-alist empty-imap)))
  (test-equal '((10 . a)) (imapping->decreasing-alist (imapping 10 'a)))
  (test-equal (reverse mixed-seq) (imapping->decreasing-alist mixed-imap))
  (test-equal (reverse sparse-seq) (imapping->decreasing-alist sparse-imap))

  (test-eqv #t (iset-empty? (imapping-keys-set empty-imap)))
  (let* ((ks '(-2 -1 0 1 2)) (set (list->iset ks)))
    (test-eqv #t (iset=? set (imapping-keys-set
                                (alist->imapping (list->dup-alist ks))))))

  (test-eqv #t (null? (imapping-keys empty-imap)))
  (test-equal (map car mixed-seq) (imapping-keys mixed-imap))
  (test-equal (map car sparse-seq) (imapping-keys sparse-imap))

  (test-eqv #t (null? (imapping-values empty-imap)))
  (test-equal (map cdr mixed-seq) (imapping-values mixed-imap))
  (test-equal (map cdr sparse-seq) (imapping-values sparse-imap))

  (test-eqv #t (imapping-empty? (iset->imapping values (iset))))
  (let* ((ks '(-2 -1 0 1 2)) (set (list->iset ks)))
    (test-eqv #t (imapping=? default-comp
                             (iset->imapping values set)
                             (alist->imapping (list->dup-alist ks))))
    (test-eqv #t (imapping=? default-comp
                         (iset->imapping abs set)
                         (alist->imapping
                          (map (lambda (k) (cons k (abs k))) ks)))))
  )

(test-group "Constructors"
  (test-equal '((1 . a) (2 . b) (3 . c))
              (imapping->alist (imapping 1 'a 2 'b 3 'c)))

  ;;; unfolds

  (test-eqv #t (null? (imapping->alist (imapping-unfold
                                        values
                                        (lambda (b) (values 1 b))
                                        (lambda (b) (not b))
                                        #t))))
  (test-equal '((1 . #f)) (imapping->alist (imapping-unfold
                                            values
                                            (lambda (b) (values 1 b))
                                            (lambda (b) (not b))
                                            #f)))
  (test-equal '((-3 . -3) (-2 . -2) (-1 . -1))
              (imapping->alist (imapping-unfold
                                (lambda (i) (< i -3))
                                (lambda (i) (values i i))
                                (lambda (i) (- i 1))
                                -1)))

  (test-eqv #t (null? (imapping->alist (imapping-unfold-maybe
                                        (lambda (b)
                                          (if b (nothing) (just 1 b (not b))))
                                        #t))))
  (test-equal '((1 . #f))
              (imapping->alist (imapping-unfold-maybe
                                (lambda (b)
                                  (if b (nothing) (just 1 b (not b))))
                                #f)))
  (test-equal '((-3 . -3) (-2 . -2) (-1 . -1))
              (imapping->alist
               (imapping-unfold-maybe
                (lambda (i)
                  (if (< i -3) (nothing) (just i i (- i 1))))
                -1)))

  ;;; alist->imapping

  (test-eqv #t (null? (imapping->alist (alist->imapping '()))))
  (test-equal mixed-seq (imapping->alist (alist->imapping mixed-seq)))
  (test-equal sparse-seq (imapping->alist (alist->imapping sparse-seq)))
  )

(test-group "Predicates"
  (test-eqv #f (imapping-contains? empty-imap 1))
  (test-eqv #t (imapping-contains? letter-imap 0))
  (test-eqv #f (imapping-contains? letter-imap 100))
  (test-eqv #t (imapping-contains? sparse-imap 4096))
  (test-eqv #f (imapping-contains? sparse-imap -4097))

  (test-eqv #t (imapping-empty? empty-imap))
  (test-eqv #f (imapping-empty? letter-imap))
  (test-eqv #f (imapping-empty? mixed-imap))
  (test-eqv #f (imapping-empty? sparse-imap))

  (test-eqv #t (imapping-disjoint? empty-imap letter-imap))
  (test-eqv #t (imapping-disjoint? (imapping 1 'a) (imapping 2 'b)))
  (test-eqv #f (imapping-disjoint? (imapping 1 'a) (imapping 1 'b)))
  )

(test-group "Accessors"
  ;;; lookups

  (test-eqv #t (nothing? (imapping-lookup empty-imap 1)))
  (test-equal (just 'a) (imapping-lookup letter-imap 0))
  (test-equal (just -50) (imapping-lookup mixed-imap -50))
  (test-eqv #t (nothing? (imapping-lookup mixed-imap -51)))
  (test-equal (just 36864) (imapping-lookup sparse-imap 36864))
  (test-eqv #t (nothing? (imapping-lookup sparse-imap 36800)))

  (test-equal -50 (imapping-ref mixed-imap -50))
  (test-equal 36864 (imapping-ref sparse-imap 36864))

  (test-eqv 'z (imapping-ref/default empty-imap 1 'z))
  (test-eqv 'a (imapping-ref/default letter-imap 0 #f))
  (test-equal -50 (imapping-ref/default mixed-imap -50 #f))
  (test-eqv 'z (imapping-ref/default mixed-imap -51 'z))
  (test-equal 36864 (imapping-ref/default sparse-imap 36864 #f))
  (test-eqv 'z (imapping-ref/default sparse-imap 36800 'z))

  ;;; min/max

  (test-eqv #t (nothing? (imapping-min empty-imap)))
  (test-equal '(0 a) (maybe-ref (imapping-min letter-imap)
                                (lambda () #f)
                                list))
  (test-equal '(-100 -100) (maybe-ref (imapping-min mixed-imap)
                                      (lambda () #f)
                                      list))
  (test-equal '(-65536 -65536)
              (maybe-ref (imapping-min sparse-imap)
                         (lambda () #f)
                         list))

  (test-eqv #t (nothing? (imapping-max empty-imap)))
  (test-equal '(25 z) (maybe-ref (imapping-max letter-imap)
                                 (lambda () #f)
                                 list))
  (test-equal '(100 100) (maybe-ref (imapping-max mixed-imap)
                                    (lambda () #f)
                                    list))
  (test-equal '(65536 65536)
              (maybe-ref (imapping-max sparse-imap)
                         (lambda () #f)
                         list))
  )

(test-group "Updaters"
  ;;; adjoins

  (test-eqv #t (imapping=? default-comp
                           (imapping 0 'a)
                           (imapping-adjoin empty-imap 0 'a)))
  (test-eqv #t (imapping-contains? (imapping-adjoin mixed-imap 200 #t) 200))
  (test-eqv #t (imapping-contains? (imapping-adjoin sparse-imap -200 #t) -200))
  (test-eqv #t (imapping=? default-comp
                           (imapping 0 'a 1 'b 2 'c)
                           (imapping-adjoin empty-imap 0 'a 1 'b 2 'c)))

  (test-eqv 'U (imapping-ref/default
                (imapping-adjoin/combinator letter-imap first 20 'U)
                20
                #f))
  (test-eqv 'u (imapping-ref/default
                (imapping-adjoin/combinator letter-imap second 20 'U)
                20
                #f))
  (test-eqv #t
            (imapping=?
             default-comp
             (imapping 0 'a 1 'b 2 'c)
             (imapping-adjoin/combinator empty-imap first 0 'a 1 'b 2 'c)))

  ;;; adjusts

  (test-eqv 'U (imapping-ref/default
                (imapping-adjust letter-imap 20 (constantly 'U))
                20
                #f))
  (test-eqv 'x (imapping-ref/default
                (imapping-adjust sparse-imap 8192 (constantly 'x))
                8192
                #f))
  (test-eqv #t (imapping-empty? (imapping-adjust empty-imap 1 (constantly 'x))))

  (test-equal '(20 u) (imapping-ref/default
                       (imapping-adjust/key letter-imap 20 list)
                       20
                       #f))
  (test-eqv 16384 (imapping-ref/default
                   (imapping-adjust/key sparse-imap
                                          8192
                                          (lambda (k v) (+ k v)))
                   8192
                   #f))
  (test-eqv #t (imapping-empty? (imapping-adjust/key empty-imap 1 list)))

  ;;; delete & delete-all

  (test-eqv #f (imapping-contains? (imapping-delete letter-imap 10) 10))
  (test-eqv #f (imapping-contains? (imapping-delete mixed-imap 50) 50))
  (test-eqv #t (imapping=? default-comp
                           mixed-imap
                           (imapping-delete mixed-imap 1)))
  (let* ((ks '(4096 8192 16384))
         (sm (apply imapping-delete sparse-imap ks)))
    (test-eqv #f (any (lambda (k) (imapping-contains? sm k)) ks)))

  (test-eqv #f (imapping-contains? (imapping-delete-all letter-imap '(10)) 10))
  (test-eqv #f (imapping-contains? (imapping-delete-all mixed-imap '(50)) 50))
  (test-eqv #t (imapping=? default-comp
                           mixed-imap
                           (imapping-delete-all mixed-imap '(1))))
  (let* ((ks '(4096 8192 16384))
         (sm (imapping-delete-all sparse-imap ks)))
    (test-eqv #f (any (lambda (k) (imapping-contains? sm k)) ks)))

  ;;; update

  (test-eqv #t (imapping=? default-comp
                           (imapping 0 'b)
                           (imapping-update (imapping 0 'a)
                                            0
                                            (constantly (just 'b)))))
  (test-eqv 'U (imapping-ref/default
                (imapping-update letter-imap 20 (constantly (just 'U)))
                20
                #f))
  (test-eqv #f (imapping-contains?
                (imapping-update letter-imap 20 (constantly (nothing)))
                20))
  (test-eqv #f (imapping-contains?
                (imapping-update sparse-imap -8192 (constantly (nothing)))
                -8192))

  (test-eqv #t (imapping=?
                default-comp
                (imapping 0 '(0 a))
                (imapping-update/key (imapping 0 'a)
                                     0
                                     (lambda (k v) (just (list k v))))))
  (test-eqv 'U (imapping-ref/default
                (imapping-update/key letter-imap 20 (constantly (just 'U)))
                20
                #f))
  (test-eqv #f (imapping-contains?
                (imapping-update/key letter-imap 20 (constantly (nothing)))
                20))
  (test-eqv #f (imapping-contains?
                (imapping-update/key sparse-imap -8192 (constantly (nothing)))
                -8192))

  ;;; alter

  (test-eqv #t (imapping=? default-comp
                           (imapping 0 'a)
                           (imapping-alter (imapping 0 'a)
                                           1
                                           (constantly (nothing)))))
  (test-eqv #t (imapping=? default-comp
                           (imapping 0 'a 1 'b)
                           (imapping-alter (imapping 0 'a)
                                           1
                                           (constantly (just 'b)))))
  (test-eqv 101 (imapping-ref/default
                 (imapping-alter mixed-imap
                                 101
                                 (constantly (just 101)))
                 101
                 #f))
  (test-eqv 101 (imapping-ref/default
                 (imapping-alter mixed-imap
                                 100
                                 (lambda (m)
                                   (maybe-map (lambda (n) (+ n 1)) m)))
                 100
                 #f))
  (test-eqv 'z (imapping-ref/default
                (imapping-alter mixed-imap
                                100
                                (constantly (nothing)))
                100
                'z))
  (test-equal -16383 (imapping-ref/default
                    (imapping-alter sparse-imap
                                    -16384
                                    (lambda (m)
                                      (maybe-map (lambda (n) (+ n 1)) m)))
                    -16384
                    #f))
  (test-eqv 'z (imapping-ref/default
                (imapping-alter sparse-imap
                                -16384
                                (constantly (nothing)))
                -16384
                'z))

  ;;; delete-min/-max

  (test-eqv #t (imapping=? default-comp
                           empty-imap
                           (imapping-delete-min (imapping 0 'a))))
  (test-eqv #f (imapping-contains? (imapping-delete-min letter-imap) 0))
  (test-eqv #f (imapping-contains? (imapping-delete-min sparse-imap) -65536))

  (test-eqv #t (imapping=? default-comp
                           empty-imap
                           (imapping-delete-max (imapping 0 'a))))
  (test-eqv #f (imapping-contains? (imapping-delete-max letter-imap) 25))
  (test-eqv #f (imapping-contains? (imapping-delete-max sparse-imap) 65536))

  ;;; min updaters

  (test-eqv 'A (imapping-ref/default
                (imapping-update-min letter-imap (constantly (just 'A)))
                0
                #f))
  (test-eqv #f (imapping-contains?
                (imapping-update-min letter-imap (constantly (nothing)))
                0))
  (test-equal -65535 (imapping-ref/default
                      (imapping-update-min sparse-imap
                                           (lambda (v) (just (+ v 1))))
                      -65536
                      #f))

  (test-equal -200 (imapping-ref/default
                    (imapping-update-min/key mixed-imap
                                             (lambda (k v) (just (+ k v))))
                    -100
                    #f))
  (test-equal '(0 a)
              (imapping-ref/default
               (imapping-update-min/key letter-imap
                                        (lambda (k v) (just (list k v))))
               0
               #f))

  ;;; max updaters

  (test-eqv 'Z (imapping-ref/default
                (imapping-update-max letter-imap (constantly (just 'Z)))
                25
                #f))
  (test-eqv #f (imapping-contains?
                (imapping-update-max letter-imap (constantly (nothing)))
                25))
  (test-eqv 65537 (imapping-ref/default
                   (imapping-update-max sparse-imap
                                        (lambda (v) (just (+ v 1))))
                   65536
                   #f))

  (test-eqv 200 (imapping-ref/default
                 (imapping-update-max/key mixed-imap
                                          (lambda (k v) (just (+ k v))))
                 100
                 #f))
  (test-equal '(25 z)
              (imapping-ref/default
               (imapping-update-max/key letter-imap
                                        (lambda (k v) (just (list k v))))
               25
               #f))

  ;;; pop-min

  (test-eqv #t (nothing? (imapping-pop-min empty-imap)))
  (test-eqv #t
            (every
             (lambda (im)
               (let-values (((k v im*)
                             (maybe-ref/default (imapping-pop-min im) #f))
                            ((test-k test-v)
                             (maybe-ref/default (imapping-min im) #f)))
                 (and (= k test-k)
                      (eqv? v test-v)
                      (imapping=? default-comp (imapping-delete-min im) im*))))
             (list mixed-imap letter-imap sparse-imap)))  ; non-empty only

  ;;; pop-min

  (test-eqv #t (nothing? (imapping-pop-min empty-imap)))
  (test-eqv #t
            (every
             (lambda (im)
               (let-values (((k v im*)
                             (maybe-ref/default (imapping-pop-max im) #f))
                            ((test-k test-v)
                             (maybe-ref/default (imapping-max im) #f)))
                 (and (= k test-k)
                      (eqv? v test-v)
                      (imapping=? default-comp (imapping-delete-max im) im*))))
             (list mixed-imap letter-imap sparse-imap)))  ; non-empty only
  )

(test-group "Whole imappings"
  (test-eqv 0 (imapping-size empty-imap))
  (test-eqv 26 (imapping-size letter-imap))

  (test-eqv 0 (imapping-count even? empty-imap))
  (test-eqv 26 (imapping-count symbol? letter-imap))
  (let ((ss '(f r o b)))
    (test-equal (length ss)
                (imapping-count (lambda (s) (memv s ss)) letter-imap))
    (test-equal (- (imapping-size letter-imap) (length ss))
                (imapping-count (lambda (s) (not (memv s ss))) letter-imap)))
  (test-eqv 4 (imapping-count positive? mixed-imap))

  (test-eqv 2 (imapping-count/key (lambda (k v) (and (even? k) (positive? v)))
                                  mixed-imap))

  ;;; any?/every?

  (test-eqv #f (imapping-any? even? empty-imap))
  (test-eqv #t (imapping-any? positive? mixed-imap))
  (test-eqv #f (imapping-any? odd? sparse-imap))
  (test-eqv #t (imapping-any? negative? sparse-imap))

  (test-eqv #t (imapping-every? even? empty-imap))
  (test-eqv #f (imapping-every? positive? mixed-imap))
  (test-eqv #t (imapping-every? even? sparse-imap))
  (test-eqv #f (imapping-every? negative? sparse-imap))
  )

(test-group "Iterators"
  ;;; map

  (test-eqv #t (imapping=? default-comp
                           empty-imap
                           (imapping-map (constantly #t) empty-imap)))
  (test-eqv #t (imapping=? default-comp
                           mixed-imap
                           (imapping-map values mixed-imap)))
  (test-eqv #t (imapping=? default-comp
                           (imapping 0 "" 1 "a" 2 "aa")
                           (imapping-map (lambda (m) (make-string m #\a))
                                         (imapping 0 0 1 1 2 2))))
  (test-eqv #f (imapping-any? negative? (imapping-map abs sparse-imap)))

  (test-eqv #t (imapping=? default-comp
                           empty-imap
                           (imapping-map/key (constantly #t) empty-imap)))
  (test-eqv #t (imapping=? default-comp
                           mixed-imap
                           (imapping-map/key (nth 1) mixed-imap)))
  (test-eqv #t (imapping=? default-comp
                           (imapping 0 "" 1 "b" 2 "cc")
                           (imapping-map/key make-string
                                             (imapping 0 #\a 1 #\b 2 #\c))))

  ;;; for-each

  (test-eqv 26
            (let ((size 0))
              (imapping-for-each (lambda (_) (set! size (+ size 1)))
                                 letter-imap)
              size))
  (test-equal '(c b a)
              (let ((xs '()))
                (imapping-for-each (lambda (x) (set! xs (cons x xs)))
                                   (imapping 0 'a 1 'b 2 'c))
                xs))

  (test-equal '((2 . c) (1 . b) (0 . a))
              (let ((xs '()))
                (imapping-for-each/key
                 (lambda (k x) (set! xs (cons (cons k x) xs)))
                 (imapping 0 'a 1 'b 2 'c))
                xs))

  ;;; fold

  (test-eqv 'z (imapping-fold (nth 1) 'z empty-imap))
  (test-equal (reverse '(a b c d e f g h i j k l m n o p q r s t u v w x y z))
              (imapping-fold cons '() letter-imap))
  (test-equal (reverse (iota 9 -100 25)) (imapping-fold cons '() mixed-imap))
  (test-equal (fold + 0 (iota 9 -100 25)) (imapping-fold + 0 mixed-imap))

  (test-equal (reverse '((0 . "") (1 . "b") (2 . "cc")))
              (imapping-fold/key (lambda (k c as)
                                   (cons (cons k (make-string k c)) as))
                                 '()
                                 (imapping 0 #\a 1 #\b 2 #\c)))

  ;;; fold-right

  (test-eqv 'z (imapping-fold-right (nth 1) 'z empty-imap))
  (test-equal '(a b c d e f g h i j k l m n o p q r s t u v w x y z)
              (imapping-fold-right cons '() letter-imap))
  (test-equal (iota 9 -100 25) (imapping-fold-right cons '() mixed-imap))
  (test-equal (fold + 0 (iota 9 -100 25)) (imapping-fold-right + 0 mixed-imap))

  (test-equal '((0 . "") (1 . "b") (2 . "cc"))
              (imapping-fold-right/key (lambda (k c as)
                                        (cons (cons k (make-string k c)) as))
                                       '()
                                       (imapping 0 #\a 1 #\b 2 #\c)))

  ;;; map->list

  (test-eqv #t (null? (imapping-map->list (constantly #t) empty-imap)))
  (test-equal '(a b c d e f g h i j k l m n o p q r s t u v w x y z)
              (imapping-map->list values letter-imap))
  (test-equal (map square (iota 9 -100 25))
              (imapping-map->list square mixed-imap))
  (test-equal '("" "a" "aa")
              (imapping-map->list (lambda (n) (make-string n #\a))
                                  (imapping 0 0 1 1 2 2)))

  (test-equal (iota 26) (imapping-map/key->list (nth 0) letter-imap))
  (test-equal '((0 . "") (1 . "b") (2 . "cc"))
              (imapping-map/key->list (lambda (k c) (cons k (make-string k c)))
                                      (imapping 0 #\a 1 #\b 2 #\c)))

  ;;; filter-map

  ;; filter-map is equivalent to map if the mapped proc always returns
  ;; a truthy value.  (Ignoring side-effects.)
  (test-eqv #t (imapping=? default-comp
                           empty-imap
                           (imapping-filter-map (constantly #t) empty-imap)))
  (test-eqv #t (imapping=? default-comp
                           mixed-imap
                           (imapping-filter-map values mixed-imap)))
  (test-eqv #t (imapping=? default-comp
                           (imapping 0 "" 1 "a" 2 "aa")
                           (imapping-filter-map
                            (lambda (m) (make-string m #\a))
                            (imapping 0 0 1 1 2 2))))
  (test-eqv #f (imapping-any? negative? (imapping-filter-map abs sparse-imap)))
  ;; filter-map empties a mapping if the mapped proc always returns #f.
  (test-eqv #t
            (every imapping-empty?
                   (map (lambda (m) (imapping-filter-map (constantly #f) m))
                        (list empty-imap letter-imap mixed-imap sparse-imap))))
  ;; Using filter-map as filter.
  (test-equal (filter (lambda (p) (even? (cdr p))) mixed-seq)
              (imapping->alist
               (imapping-filter-map (lambda (v) (and (even? v) v))
                                    mixed-imap)))
  ;; Filtering and transforming the values of a mapping.
  (test-equal (filter-map (lambda (p)
                            (and (even? (cdr p))
                                 (cons (car p) (abs (cdr p)))))
                          sparse-seq)
              (imapping->alist
               (imapping-filter-map (lambda (v) (and (even? v) (abs v)))
                                    sparse-imap)))

  ;; filter-map/key is equivalent to map/key if the mapped procedure
  ;; always returns a truthy value.  (Ignoring side-effects.)
  (test-eqv #t (imapping=? default-comp
                           empty-imap
                           (imapping-filter-map/key (constantly #t)
                                                    empty-imap)))
  (test-eqv #t (imapping=? default-comp
                           mixed-imap
                           (imapping-filter-map/key (nth 1) mixed-imap)))
  (test-eqv #t (imapping=? default-comp
                           (imapping 0 "" 1 "b" 2 "cc")
                           (imapping-filter-map/key
                            make-string
                            (imapping 0 #\a 1 #\b 2 #\c))))
  ;; filter-map/key empties a mapping if the mapped proc always returns #f.
  (test-eqv #t
            (every imapping-empty?
                   (map (lambda (m) (imapping-filter-map/key (constantly #f) m))
                        (list empty-imap letter-imap mixed-imap sparse-imap))))
  ;; Using filter-map/key as filter.
  (test-equal (filter (lambda (p) (even? (cdr p))) mixed-seq)
              (imapping->alist
               (imapping-filter-map/key (lambda (k v) (and (even? v) v))
                                        mixed-imap)))
  ;; Filtering and transforming the values of a mapping.
  (test-equal (filter-map (lambda (p)
                            (let ((k (car p)) (v (cdr p)))
                              (and (even? k) (cons k (+ k v)))))
                          sparse-seq)
              (imapping->alist
               (imapping-filter-map/key (lambda (k v)
                                          (and (even? k) (+ k v)))
                                        sparse-imap)))

  ;;; map-either

  ;; Mapping `left' with map-either copies the imapping argument as
  ;; the first returned value.
  (test-eqv #t
            (every
             (lambda (im)
               (imapping=? default-comp
                           im
                           (let-values (((lm rm)
                                         (imapping-map-either left im)))
                             lm)))
             (list empty-imap letter-imap mixed-imap sparse-imap)))
  ;; Mapping `right' with map-either copies the imapping argument as
  ;; the second returned value.
  (test-eqv #t
            (every
             (lambda (im)
               (imapping=? default-comp
                           im
                           (let-values (((lm rm)
                                         (imapping-map-either right im)))
                             rm)))
             (list empty-imap letter-imap mixed-imap sparse-imap)))
  ;; Using map-either to partition an imapping.
  (test-eqv #t
            (let-values (((neg pos)
                          (imapping-map-either
                           (lambda (n)
                             (if (negative? n) (left n) (right n)))
                           sparse-imap)))
              (and (imapping-every? negative? neg)
                   (imapping-every? (lambda (x) (not (negative? x))) pos))))
  ;; Using map-either to split and transform an imapping.
  (test-eqv #t
            (let-values (((lm rm)
                          (imapping-map-either
                           (lambda (n)
                             (if (negative? n) (left (abs n)) (right n)))
                           (imapping -2 -2 -1 -1 3 3 5 5))))
              (and (imapping=? default-comp lm (imapping -2 2 -1 1))
                   (imapping=? default-comp rm (imapping 3 3 5 5)))))

  ;; Using map-either/key to split and transform an imapping.
  (test-eqv #t
            (let-values (((lm rm)
                          (imapping-map-either/key
                           (lambda (k n)
                             (if (negative? n)
                                 (left (+ k (abs n)))
                                 (right (+ k n))))
                           (imapping -2 -2 -1 -1 3 3 5 5))))
              (and (imapping=? default-comp lm (imapping -2 0 -1 0))
                   (imapping=? default-comp rm (imapping 3 6 5 10)))))
  )

(test-group "Filters"
  (test-eqv #t
            (every values
                   (map (lambda (m)
                          (imapping=? default-comp
                                      m
                                      (imapping-filter (constantly #t) m)))
                        (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test-eqv #t
            (every imapping-empty?
                   (map (lambda (m) (imapping-filter (constantly #f) m))
                        (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test-eqv #t (imapping=? default-comp
                           (imapping 25 25 50 50 75 75 100 100)
                           (imapping-filter positive? mixed-imap)))
  (test-eqv #t (imapping=? default-comp
                           (imapping 22 'w)
                           (imapping-filter (lambda (s) (eqv? s 'w))
                                            letter-imap)))

  (test-eqv #t
            (every values
                   (map (lambda (m)
                          (imapping=? default-comp
                                      m
                                      (imapping-filter/key (constantly #t) m)))
                        (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test-eqv #t
            (every imapping-empty?
                   (map (lambda (m) (imapping-filter/key (constantly #f) m))
                        (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test-eqv #t (imapping=? default-comp
                           (imapping 25 25 75 75)
                           (imapping-filter/key (lambda (k v)
                                                  (and (odd? k) (positive? v)))
                                                mixed-imap)))

  ;;; remove

  (test-eqv #t
            (every values
                   (map (lambda (m)
                          (imapping=? default-comp
                                      m
                                      (imapping-remove (constantly #f) m)))
                        (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test-eqv #t
            (every imapping-empty?
                   (map (lambda (m) (imapping-remove (constantly #t) m))
                        (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test-eqv #t (imapping=? default-comp
                           (imapping 0 0 25 25 50 50 75 75 100 100)
                           (imapping-remove negative? mixed-imap)))
  (test-eqv #t (imapping=? default-comp
                           (imapping 22 'w)
                           (imapping-remove (lambda (s) (not (eqv? s 'w)))
                                            letter-imap)))

  (test-eqv #t
            (every (lambda (m)
                     (imapping=? default-comp
                                 m
                                 (imapping-remove/key (constantly #f) m)))
                   all-test-imaps))
  (test-eqv #t
            (every imapping-empty?
                   (map (lambda (m) (imapping-remove/key (constantly #t) m))
                        (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test-eqv #t
            (imapping=? default-comp
                        (imapping -100 -100 -50 -50 0 0)
                        (imapping-remove/key (lambda (k v)
                                               (or (odd? k) (positive? v)))
                                             mixed-imap)))

  ;;; partition

  (test-eqv #t
            (every (lambda (m)
                     (imapping=?
                      default-comp
                      m
                      (value/mv 0 (imapping-partition (constantly #t) m))))
                   all-test-imaps))
  (test-equal (call-with-values
               (lambda () (partition even? (map car mixed-seq)))
               list)
              (let-values (((em om) (imapping-partition even? mixed-imap)))
                (list (imapping-values em) (imapping-values om))))
  (test-eqv #t
            (let-values (((zm not-zm)
                          (imapping-partition (lambda (s) (eqv? s 'z))
                                              letter-imap)))
              (and (imapping=? default-comp zm (imapping 25 'z))
                   (imapping=? default-comp
                               not-zm
                               (imapping-delete letter-imap 25)))))

  (test-equal (unfold (lambda (i) (= i 26))
                      (lambda (i)
                        (string->symbol (string (integer->char (+ i #x61)))))
                      (lambda (i) (+ i 2))
                      0)
              (let-values (((em _)
                            (imapping-partition/key (lambda (k _) (even? k))
                                                    letter-imap)))
                (imapping-values em)))
  )

(test-group "Comparison"
  (let ((subimap (imapping-filter even? mixed-imap)))
    (test-eqv #t (imapping<? default-comp (imapping) mixed-imap))
    (test-eqv #t (imapping<? default-comp subimap mixed-imap))
    (test-eqv #f (imapping<? default-comp mixed-imap subimap))
    (test-eqv #f (imapping<? default-comp mixed-imap mixed-imap))
    (test-eqv #f (imapping<? default-comp
                             (imapping 0 'z)
                             (imapping 0 'a 1 'b)))

    (test-eqv #t (imapping>? default-comp mixed-imap (imapping)))
    (test-eqv #f (imapping>? default-comp subimap mixed-imap))
    (test-eqv #t (imapping>? default-comp mixed-imap subimap))
    (test-eqv #f (imapping>? default-comp mixed-imap mixed-imap))
    (test-eqv #f (imapping>? default-comp
                             (imapping 0 'z 1 'b)
                             (imapping 0 'a)))

    (test-eqv #t (imapping<=? default-comp (imapping) mixed-imap))
    (test-eqv #t (imapping<=? default-comp subimap mixed-imap))
    (test-eqv #f (imapping<=? default-comp mixed-imap subimap))
    (test-eqv #t (imapping<=? default-comp mixed-imap mixed-imap))
    (test-eqv #f (imapping<=? default-comp
                              (imapping 0 'z 1 'b)
                              (imapping 0 'a 1 'b)))

    (test-eqv #t (imapping>=? default-comp mixed-imap (imapping)))
    (test-eqv #f (imapping>=? default-comp subimap mixed-imap))
    (test-eqv #t (imapping>=? default-comp mixed-imap subimap))
    (test-eqv #t (imapping>=? default-comp mixed-imap mixed-imap))
    (test-eqv #f (imapping<=? default-comp
                              (imapping 0 'z 1 'b)
                              (imapping 0 'a 1 'b)))

    ;; Variadic comparisons.
    (let ((subimap1 (imapping-filter positive? subimap)))
      (test-eqv #t (imapping<? default-comp subimap1 subimap mixed-imap))
      (test-eqv #f (imapping<? default-comp subimap1 empty-imap mixed-imap))

      (test-eqv #t (imapping>? default-comp mixed-imap subimap subimap1))
      (test-eqv #f (imapping>? default-comp mixed-imap empty-imap subimap1))

      (test-eqv #t (imapping<=? default-comp
                                subimap1
                                subimap
                                subimap
                                mixed-imap))
      (test-eqv #f (imapping<=? default-comp subimap1 empty-imap mixed-imap))

      (test-eqv #t (imapping>=? default-comp
                                mixed-imap
                                subimap
                                subimap
                                subimap1))
      (test-eqv #f (imapping>=? default-comp mixed-imap empty-imap subimap1))
      ))
  )

(test-group "Set theory"
  (let ((imap1 (imapping -5 'a -2 'b 1 'c))
        (imap2 (imapping -2 'b 3 'd 5 'e))
        (imap3 (imapping 3 'd 5 'g 7 'f)))  ; assoc for 5 differs from imap2
    (test-eqv #t (imapping=? default-comp
                             sparse-imap
                             (imapping-union sparse-imap empty-imap)))
    (test-eqv #t (imapping=? default-comp
                             (imapping -5 'a -2 'b 1 'c 3 'd 5 'e)
                             (imapping-union imap1 imap2)))
    (test-eqv #t (imapping=? default-comp
                             (imapping -2 'b 3 'd 5 'e 7 'f)
                             (imapping-union imap2 imap3)))
    (test-eqv #t (imapping=? default-comp
                             (imapping -5 'a -2 'b 1 'c 3 'd 5 'e 7 'f)
                             (imapping-union imap1 imap2 imap3)))

    (test-eqv #t (imapping-empty?
                  (imapping-intersection sparse-imap empty-imap)))
    (test-eqv #t (imapping=? default-comp
                             (imapping -2 'b)
                             (imapping-intersection imap1 imap2)))
    (test-eqv #t (imapping=? default-comp
                             (imapping 3 'd 5 'e)
                             (imapping-intersection imap2 imap3)))
    (test-eqv #t (imapping=?
                  default-comp
                  (imapping -2 'b)
                  (imapping-intersection imap1 imap2 (imapping -2 'b))))

    (test-eqv #t (imapping=? default-comp
                             sparse-imap
                             (imapping-difference sparse-imap empty-imap)))
    (test-eqv #t (imapping=? default-comp
                             (imapping -5 'a 1 'c)
                             (imapping-difference imap1 imap2)))
    (test-eqv #t (imapping=? default-comp
                             (imapping -2 'b)
                             (imapping-difference imap2 imap3)))
    (test-eqv #t (imapping=? default-comp
                             (imapping -5 'a 1 'c)
                             (imapping-difference imap1 imap2 imap3)))

    (test-eqv #t (imapping=? default-comp
                             sparse-imap
                             (imapping-xor sparse-imap empty-imap)))
    (test-eqv #t (imapping=? default-comp
                             (imapping -5 'a 1 'c 3 'd 5 'e)
                             (imapping-xor imap1 imap2)))
    (test-eqv #t (imapping=? default-comp
                             (imapping -2 'b 7 'f)
                             (imapping-xor imap2 imap3)))
    ))

(test-group "Intervals"
  (test-equal (list->dup-alist '(-25 0 25))
              (imapping->alist
               (imapping-open-interval mixed-imap -50 50)))
  (test-equal '((6 . g) (7 . h) (8 . i) (9 . j))
              (imapping->alist
               (imapping-open-interval letter-imap 5 10)))
  (test-equal (list->dup-alist '(-8192 -4096 0 4096 8192))
              (imapping->alist
               (imapping-open-interval sparse-imap -12288 12288)))

  (test-equal (list->dup-alist '(-50 -25 0 25 50))
              (imapping->alist
               (imapping-closed-interval mixed-imap -50 50)))
  (test-equal '((5 . f) (6 . g) (7 . h) (8 . i) (9 . j) (10 . k))
              (imapping->alist
               (imapping-closed-interval letter-imap 5 10)))
  (test-equal (list->dup-alist '(-12288 -8192 -4096 0 4096 8192 12288))
              (imapping->alist
               (imapping-closed-interval sparse-imap -12288 12288)))

  (test-equal (list->dup-alist '(-25 0 25 50))
              (imapping->alist
               (imapping-open-closed-interval mixed-imap -50 50)))
  (test-equal '((6 . g) (7 . h) (8 . i) (9 . j) (10 . k))
              (imapping->alist
               (imapping-open-closed-interval letter-imap 5 10)))
  (test-equal (list->dup-alist '(-8192 -4096 0 4096 8192 12288))
              (imapping->alist
               (imapping-open-closed-interval sparse-imap -12288 12288)))

  (test-equal (list->dup-alist '(-50 -25 0 25))
              (imapping->alist
               (imapping-closed-open-interval mixed-imap -50 50)))
  (test-equal '((5 . f) (6 . g) (7 . h) (8 . i) (9 . j))
              (imapping->alist
               (imapping-closed-open-interval letter-imap 5 10)))
  (test-equal (list->dup-alist '(-12288 -8192 -4096 0 4096 8192))
              (imapping->alist
               (imapping-closed-open-interval sparse-imap -12288 12288)))
  )

(test-group "Submappings"
  (test-equal '((100 . 100)) (imapping->alist (isubmapping= mixed-imap 100)))
  (test-equal '((7 . h)) (imapping->alist (isubmapping= letter-imap 7)))
  (test-equal '((16384 . 16384))
              (imapping->alist (isubmapping= sparse-imap 16384)))
  (test-eqv #t (imapping-empty? (isubmapping= sparse-imap 1)))

  (test-equal (list->dup-alist '(-100 -75 -50 -25))
              (imapping->alist (isubmapping< mixed-imap 0)))
  (test-equal '((0 . a) (1 . b) (2 . c))
              (imapping->alist (isubmapping< letter-imap 3)))
  (test-equal (list->dup-alist '(-65536 -61440 -57344))
              (imapping->alist (isubmapping< sparse-imap -53248)))

  (test-equal (list->dup-alist '(25 50 75 100))
              (imapping->alist (isubmapping> mixed-imap 0)))
  (test-equal '((23 . x) (24 . y) (25 . z))
              (imapping->alist (isubmapping> letter-imap 22)))
  (test-equal (list->dup-alist '(57344 61440 65536))
              (imapping->alist (isubmapping> sparse-imap 53248)))

  (test-equal (list->dup-alist '(-100 -75 -50 -25 0))
              (imapping->alist (isubmapping<= mixed-imap 0)))
  (test-equal '((0 . a) (1 . b) (2 . c) (3 . d))
              (imapping->alist (isubmapping<= letter-imap 3)))
  (test-equal (list->dup-alist '(-65536 -61440 -57344 -53248))
              (imapping->alist (isubmapping<= sparse-imap -53248)))

  (test-equal (list->dup-alist '(0 25 50 75 100))
              (imapping->alist (isubmapping>= mixed-imap 0)))
  (test-equal '((22 . w) (23 . x) (24 . y) (25 . z))
              (imapping->alist (isubmapping>= letter-imap 22)))
  (test-equal (list->dup-alist '(53248 57344 61440 65536))
              (imapping->alist (isubmapping>= sparse-imap 53248)))
  )

(test-group "Relation map"
  (test-eqv #t
            (imapping=? default-comp
                        (imapping 0 #t)
                        (imapping-relation-map (lambda (_k _v) (values 0 #t))
                                               letter-imap)))
  (test-eqv #t
            (imapping=? default-comp
                        letter-imap
                        (imapping-relation-map values letter-imap)))
  (test-equal '((0 . a) (1 . b) (2 . c))
              (imapping->alist
               (imapping-relation-map (lambda (k v) (values (- k) v))
                                      (imapping 0 'a -1 'b -2 'c))))
  )

(test-group "Comparator"
  (let ((comp (imapping-comparator)))
    (test-eqv #t (comparator-ordered? comp))
    (test-eqv #t ((comparator-type-test-predicate comp) empty-imap))
    (test-eqv #f ((comparator-type-test-predicate comp) 'z))
    (test-eqv #t (=? comp mixed-imap mixed-imap))
    (test-eqv #t (=? comp (imapping 0 'a -1 'b -2 'c)
                          (imapping -1 'b 0 'a -2 'c)))
    (test-eqv #f (=? comp mixed-imap sparse-imap))  ; same value types
    (test-eqv #f (=? comp mixed-imap letter-imap))  ; different value types
    (test-eqv #t (<? comp empty-imap mixed-imap))
    (test-eqv #t (<? comp (imapping 0 'a) (imapping 0 'a -1 'b -2 'c)))
    (test-eqv #f (<? comp (imapping 0 0) (imapping 0 'a -1 'b -2 'c)))
    (test-eqv #f (<? comp mixed-imap letter-imap))  ; different value types
    (test-eqv #t (<=? comp (imapping 0 'a 1 'b) (imapping 1 'b 0 'a)))
    (test-eqv #t (<=? comp (imapping 0 'a 1 'b) (imapping 1 'a 0 'a)))
    (test-eqv #f (<=? comp (imapping 0 'z 1 'b) (imapping 1 'a 0 'a)))
    (test-eqv #t (>? comp (imapping 1 'b 0 'a) (imapping 0 'a)))
    (test-eqv #f (>? comp (imapping 1 'b 0 'a) (imapping 1 'a)))
    (test-eqv #t (>=? comp (imapping 1 'b 0 'a) (imapping 0 'a 1 'b)))
    (test-eqv #t (>=? comp (imapping 1 'b 0 'a) (imapping 1 'b)))
    (test-eqv #f (>=? comp (imapping 1 'b 0 'a) (imapping 0 'z)))
    (test-eqv #f (>=? comp (imapping 1 'b) (imapping 0 'a 1 'b)))
    )

  (let ((comp (make-imapping-comparator
               (make-comparator boolean?    ; boolean comparator
                                boolean=?
                                (lambda (x y) (and (not x) y))
                                #f))))
    (test-eqv #t (=? comp (imapping 0 #f 1 #t) (imapping 1 #t 0 #f)))
    (test-eqv #f (=? comp (imapping 0 #f 1 #t) (imapping 1 #t)))
    (test-eqv #t (<? comp (imapping 0 #f) (imapping 1 #t 0 #f)))
    (test-eqv #f (<? comp (imapping 0 #t 1 #t) (imapping 1 #t 0 #f)))
    (test-eqv #t (<=? comp (imapping 0 #f 1 #t) (imapping 1 #t 0 #f)))
    (test-eqv #t (<=? comp (imapping 0 #f 1 #t) (imapping 1 #f 0 #f)))
    (test-eqv #t (>? comp (imapping 1 #t 0 #f) (imapping 0 #f)))
    (test-eqv #f (>? comp (imapping 1 #t 0 #f) (imapping 1 #f)))
    (test-eqv #t (>=? comp (imapping 1 #t 0 #f) (imapping 1 #t 0 #f)))
    (test-eqv #f (>=? comp (imapping 1 #t 0 #f) (imapping 1 #t)))
    )
  )
