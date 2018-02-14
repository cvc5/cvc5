;; This is a nasty parsing test for define-fun-rec

(set-logic UFLIRA)
(set-info :smt-lib-version 2.5)
(define-fun-rec (
   (f ((x Int)) Int 5) ;; ok, f : Int -> Int
   (g ((x Int)) Int (h 4)) ;;  um, ok, so g : Int -> Int and h : Int -> Int?
   (h ((x Real)) Int 4)   ;; oops no we were wrong, **CRASH**
))

(reset)

(set-logic UFLIRA)
(set-info :smt-lib-version 2.5)
(define-fun-rec (
   (f ((x Int)) Int (g (h 4) 5)) ;; ok, f : Int -> Int and g : Int -> X -> Int and h : Int -> X ??!  What the F?! (pun intended)
   (g ((x Int)) Int 5) ;; wait, now g has wrong arity?!!  **BURN**
   (h ((x Int)) Int 2)
))

(reset)

(set-logic UFLIRA)
(set-info :smt-lib-version 2.5)
(declare-const g Int 2)
(define-fun-rec (
  (f () Int g)  ;; wait, which g does this refer to?!  **LOCUSTS**
  (g () Int 5)
))
