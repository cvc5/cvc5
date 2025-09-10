; COMMAND-LINE: --dt-stc-ind --conjecture-gen
; DISABLE-TESTER: unsat-core
; EXPECT: unsat
(set-logic UFDTLIA)
(declare-datatypes ((pair3 0))
  (((pair22 (proj1-pair2 Int) (proj2-pair2 Int)))))
(declare-datatypes ((list7 0))
  (((nil7) (cons7 (head7 Bool) (tail7 list7)))))
(declare-datatypes ((list6 0))
  (((nil6) (cons6 (head6 Int) (tail6 list6)))))
(declare-datatypes ((list3 0))
  (((nil2) (cons2 (head2 pair3) (tail2 list3)))))
(declare-datatypes ((list4 0))
  (((nil3) (cons3 (head3 list3) (tail3 list4)))))
(declare-datatypes ((B 0)) (((I) (O))))
(declare-datatypes ((list 0))
  (((nil5) (cons5 (head5 B) (tail5 list)))))
(declare-datatypes ((list5 0))
  (((nil4) (cons4 (head4 list) (tail4 list5)))))
(declare-datatypes ((pair 0))
  (((pair2 (proj1-pair list) (proj2-pair list)))))
(declare-datatypes ((list2 0))
  (((nil) (cons (head pair) (tail list2)))))
(define-fun-rec
  primEnumFromTo
  ((x Int) (y Int)) list6
  (ite (< y x) nil6 (cons6 x (primEnumFromTo (+ 1 x) y))))
(define-fun-rec
  petersen3
  ((x Int) (y list6)) list3
  (ite
    (is-cons6 y)
    (cons2 (pair22 (head6 y) (+ x (head6 y))) (petersen3 x (tail6 y)))
    nil2))
(define-fun-rec
  petersen2
  ((x list6)) list3
  (ite
    (is-cons6 x)
    (cons2 (pair22 (head6 x) (+ 1 (head6 x))) (petersen2 (tail6 x)))
    nil2))
(define-fun-rec
  petersen
  ((x Int) (y list3)) list4
  (ite
    (is-cons2 y)
    (cons3
      (cons2 (pair22 (proj1-pair2 (head2 y)) (proj2-pair2 (head2 y)))
        (cons2
          (pair22 (+ x (proj1-pair2 (head2 y)))
            (+ x (proj2-pair2 (head2 y))))
          nil2))
      (petersen x (tail2 y)))
    nil3))
(define-fun-rec
  or2
  ((x list7)) Bool
  (ite (is-cons7 x) (or (head7 x) (or2 (tail7 x))) false))
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
  ((x list5)) Int (ite (is-cons4 x) (+ 1 (length (tail4 x))) 0))
(define-fun-rec
  last
  ((x list) (y list5)) list
  (ite (is-cons4 y) (last (head4 y) (tail4 y)) x))
(define-fun-rec
  bin
  ((x Int)) list
  (ite
    (= x 0) nil5
    (ite
      (= (mod x 2) 0) (cons5 O (bin (div x 2)))
      (cons5 I (bin (div x 2))))))
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
    (is-cons5 x)
    (ite
      (is-O (head5 x))
      (ite
        (is-cons5 y) (ite (is-O (head5 y)) (beq (tail5 x) (tail5 y)) false)
        false)
      (ite
        (is-cons5 y) (ite (is-O (head5 y)) false (beq (tail5 x) (tail5 y)))
        false))
    (not (is-cons5 y))))
(define-fun-rec
  bpath
  ((x list) (y list) (z list2)) list7
  (ite
    (is-cons z)
    (cons7
      (or
        (and (beq (proj1-pair (head z)) x) (beq (proj2-pair (head z)) y))
        (and (beq (proj1-pair (head z)) y) (beq (proj2-pair (head z)) x)))
      (bpath x y (tail z)))
    nil7))
(define-fun-rec
  bpath2
  ((x list5) (y list2)) Bool
  (ite
    (is-cons4 x)
    (ite
      (is-cons4 (tail4 x))
      (and (or2 (bpath (head4 x) (head4 (tail4 x)) y))
        (bpath2 (cons4 (head4 (tail4 x)) (tail4 (tail4 x))) y))
      true)
    true))
(define-fun-rec
  belem
  ((x list) (y list5)) list7
  (ite
    (is-cons4 y) (cons7 (beq x (head4 y)) (belem x (tail4 y))) nil7))
(define-fun
  belem2
  ((x list) (y list5)) Bool (or2 (belem x y)))
(define-fun-rec
  bunique
  ((x list5)) Bool
  (ite
    (is-cons4 x)
    (and (not (belem2 (head4 x) (tail4 x))) (bunique (tail4 x))) true))
(define-fun
  btour
  ((x list5) (y list3)) Bool
  (ite
    (is-cons4 x)
    (ite
      (is-cons2 y)
      (and (beq (head4 x) (last (head4 x) (tail4 x)))
        (and
          (bpath2 (cons4 (head4 x) (tail4 x))
            (bgraph
              (cons2 (pair22 (proj1-pair2 (head2 y)) (proj2-pair2 (head2 y)))
                (tail2 y))))
          (and (bunique (tail4 x))
            (= (length (cons4 (head4 x) (tail4 x)))
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
(define-fun-rec
  concat2
  ((x list4)) list3
  (ite (is-cons3 x) (++ (head3 x) (concat2 (tail3 x))) nil2))
(define-fun
  petersen4
  ((x Int)) list3
  (ite
    (= x 0) nil2
    (++
      (concat2
        (petersen x
          (cons2 (pair22 (- x 1) 0) (petersen2 (primEnumFromTo 0 (- x 1))))))
      (petersen3 x (primEnumFromTo 0 x)))))
(assert
  (not
    (forall ((p list5))
      (not
        (btour p
          (++
            (concat2
              (petersen 5
                (cons2 (pair22 (- 5 1) 0) (petersen2 (primEnumFromTo 0 (- 5 1))))))
            (petersen3 5 (primEnumFromTo 0 5))))))))
(check-sat)
