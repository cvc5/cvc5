; REQUIRES: normaliz
; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --no-arith-liastar-lazy
;
; The predicate under the star is infeasible, so the star set is exactly the
; zero vector (the empty sum). The vector is forced to zero by non-constant
; bounds, so the answer is sat. The lazy strategy finds no cell at all: its
; first round completes the enumeration with the star {0}.
(set-logic HO_ALL)
(set-info :status sat)
(declare-const a Int)
(declare-const b Int)
(assert (>= a 0))
(assert (<= a 0))
(assert (>= b 0))
(assert (<= b 0))
(assert (int.star-contains
  (lambda ((x Int) (y Int))
    (and (>= (+ x y) 1) (>= (* (- 1) (+ x y)) 0)))
  a b))
(check-sat)
