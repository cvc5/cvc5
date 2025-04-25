; COMMAND-LINE: --dt-stc-ind --conjecture-gen
; DISABLE-TESTER: unsat-core
; EXPECT: unsat
(set-logic UFDTLIA)
(declare-datatypes ((pair3 0)) (((pair22 (proj1-pair2 Int) (proj2-pair2 Int)))))
(declare-datatypes ((list6 0)) (((nil6) (cons6 (head6 Bool) (tail6 list6)))))
(declare-datatypes ((list5 0)) (((nil5) (cons5 (head5 Int) (tail5 list5)))))
(declare-datatypes ((list3 0)) (((nil2) (cons2 (head2 pair3) (tail2 list3)))))
(declare-datatypes ((B 0)) (((I) (O))))
(declare-datatypes ((list 0)) (((nil4) (cons4 (head4 B) (tail4 list)))))
(declare-datatypes ((list4 0)) (((nil3) (cons3 (head3 list) (tail3 list4)))))
(declare-datatypes ((pair 0)) (((pair2 (proj1-pair list) (proj2-pair list)))))
(declare-datatypes ((list2 0)) (((nil) (cons (head pair) (tail list2)))))
(define-fun-rec
  primEnumFromTo
  ((x Int) (y Int)) list5
  (ite (< y x) nil5 (cons5 x (primEnumFromTo (+ 1 x) y))))
(define-fun-rec
  or2
  ((x list6)) Bool
  (ite (is-cons6 x) (or (head6 x) (or2 (tail6 x))) false))
(define-fun-rec
  maximum-maximum1
  ((x Int) (y list3)) Int
  (ite
    (is-cons2 y)
    (let
      ((y3
          (ite
            (<= (proj1-pair2 (head2 y)) (proj2-pair2 (head2 y)))
            (proj2-pair2 (head2 y)) (proj1-pair2 (head2 y)))))
      (ite
        (<= x y3) (maximum-maximum1 y3 (tail2 y))
        (maximum-maximum1 x (tail2 y))))
    x))
(define-fun-rec
  length
  ((x list4)) Int (ite (is-cons3 x) (+ 1 (length (tail3 x))) 0))
(define-fun-rec
  last
  ((x list) (y list4)) list
  (ite (is-cons3 y) (last (head3 y) (tail3 y)) x))
(define-fun-rec
  dodeca6
  ((x Int) (y list5)) list3
  (ite
    (is-cons5 y)
    (cons2
      (pair22 (+ (+ (+ x x) x) (head5 y))
        (+ (+ (+ x x) x) (+ 1 (head5 y))))
      (dodeca6 x (tail5 y)))
    nil2))
(define-fun-rec
  dodeca5
  ((x Int) (y list5)) list3
  (ite
    (is-cons5 y)
    (cons2 (pair22 (+ (+ x x) (head5 y)) (+ (+ (+ x x) x) (head5 y)))
      (dodeca5 x (tail5 y)))
    nil2))
(define-fun-rec
  dodeca4
  ((x Int) (y list5)) list3
  (ite
    (is-cons5 y)
    (cons2 (pair22 (+ x (+ 1 (head5 y))) (+ (+ x x) (head5 y)))
      (dodeca4 x (tail5 y)))
    nil2))
(define-fun-rec
  dodeca3
  ((x Int) (y list5)) list3
  (ite
    (is-cons5 y)
    (cons2 (pair22 (+ x (head5 y)) (+ (+ x x) (head5 y)))
      (dodeca3 x (tail5 y)))
    nil2))
(define-fun-rec
  dodeca2
  ((x Int) (y list5)) list3
  (ite
    (is-cons5 y)
    (cons2 (pair22 (head5 y) (+ x (head5 y))) (dodeca2 x (tail5 y)))
    nil2))
(define-fun-rec
  dodeca
  ((x list5)) list3
  (ite
    (is-cons5 x)
    (cons2 (pair22 (head5 x) (+ 1 (head5 x))) (dodeca (tail5 x)))
    nil2))
(define-fun-rec
  bin
  ((x Int)) list
  (ite
    (= x 0) nil4
    (ite
      (= (mod x 2) 0) (cons4 O (bin (div x 2)))
      (cons4 I (bin (div x 2))))))
(define-fun-rec
  bgraph
  ((x list3)) list2
  (ite
    (is-cons2 x)
    (cons
      (pair2 (bin (proj1-pair2 (head2 x))) (bin (proj2-pair2 (head2 x))))
      (bgraph (tail2 x)))
    nil))
(define-fun-rec
  beq
  ((x list) (y list)) Bool
  (ite
    (is-cons4 x)
    (ite
      (is-O (head4 x))
      (ite
        (is-cons4 y) (ite (is-O (head4 y)) (beq (tail4 x) (tail4 y)) false)
        false)
      (ite
        (is-cons4 y) (ite (is-O (head4 y)) false (beq (tail4 x) (tail4 y)))
        false))
    (not (is-cons4 y))))
(define-fun-rec
  bpath
  ((x list) (y list) (z list2)) list6
  (ite
    (is-cons z)
    (cons6
      (or
        (and (beq (proj1-pair (head z)) x) (beq (proj2-pair (head z)) y))
        (and (beq (proj1-pair (head z)) y) (beq (proj2-pair (head z)) x)))
      (bpath x y (tail z)))
    nil6))
(define-fun-rec
  bpath2
  ((x list4) (y list2)) Bool
  (ite
    (is-cons3 x)
    (ite
      (is-cons3 (tail3 x))
      (and (or2 (bpath (head3 x) (head3 (tail3 x)) y))
        (bpath2 (cons3 (head3 (tail3 x)) (tail3 (tail3 x))) y))
      true)
    true))
(define-fun-rec
  belem
  ((x list) (y list4)) list6
  (ite
    (is-cons3 y) (cons6 (beq x (head3 y)) (belem x (tail3 y))) nil6))
(define-fun
  belem2
  ((x list) (y list4)) Bool (or2 (belem x y)))
(define-fun-rec
  bunique
  ((x list4)) Bool
  (ite
    (is-cons3 x)
    (and (not (belem2 (head3 x) (tail3 x))) (bunique (tail3 x))) true))
(define-fun
  btour
  ((x list4) (y list3)) Bool
  (ite
    (is-cons3 x)
    (ite
      (is-cons2 y)
      (and (beq (head3 x) (last (head3 x) (tail3 x)))
        (and
          (bpath2 (cons3 (head3 x) (tail3 x))
            (bgraph
              (cons2 (pair22 (proj1-pair2 (head2 y)) (proj2-pair2 (head2 y)))
                (tail2 y))))
          (and (bunique (tail3 x))
            (= (length (cons3 (head3 x) (tail3 x)))
              (ite
                (<= (proj1-pair2 (head2 y)) (proj2-pair2 (head2 y)))
                (+ 1 (+ 1 (maximum-maximum1 (proj2-pair2 (head2 y)) (tail2 y))))
                (+ 1
                  (+ 1 (maximum-maximum1 (proj1-pair2 (head2 y)) (tail2 y)))))))))
      false)
    (not (is-cons2 y))))
(define-fun-rec
  ++
  ((x list3) (y list3)) list3
  (ite (is-cons2 x) (cons2 (head2 x) (++ (tail2 x) y)) y))
(define-fun
  dodeca7
  ((x Int)) list3
  (ite
    (= x 0) nil2
    (++ (cons2 (pair22 (- x 1) 0) (dodeca (primEnumFromTo 0 (- x 1))))
      (++ (dodeca2 x (primEnumFromTo 0 x))
        (++ (dodeca3 x (primEnumFromTo 0 x))
          (++
            (cons2 (pair22 x (+ (+ x x) (- x 1)))
              (dodeca4 x (primEnumFromTo 0 (- x 1))))
            (++ (dodeca5 x (primEnumFromTo 0 x))
              (cons2 (pair22 (+ (+ (+ x x) x) (- x 1)) (+ (+ x x) x))
                (dodeca6 x (primEnumFromTo 0 (- x 1)))))))))))
(declare-const k Int)
(assert
  (not
    (forall ((p list4))
      (not
        (btour p
          (++ (cons2 (pair22 (- k 1) 0) (dodeca (primEnumFromTo 0 (- k 1))))
            (++ (dodeca2 k (primEnumFromTo 0 k))
              (++ (dodeca3 k (primEnumFromTo 0 k))
                (++
                  (cons2 (pair22 k (+ (+ k k) (- k 1)))
                    (dodeca4 k (primEnumFromTo 0 (- k 1))))
                  (++ (dodeca5 k (primEnumFromTo 0 k))
                    (cons2 (pair22 (+ (+ (+ k k) k) (- k 1)) (+ (+ k k) k))
                      (dodeca6 k (primEnumFromTo 0 (- k 1))))))))))))))
(check-sat)
