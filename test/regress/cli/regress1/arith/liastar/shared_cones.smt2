; REQUIRES: normaliz
; REQUIRES: unrestricted-mode
; COMMAND-LINE:
; COMMAND-LINE: --no-arith-liastar-lazy
;
; The lazy strategy shares the cones it discovers between all atoms over the
; same lambda, within a check and across user contexts. Every lemma for an
; atom must then account for all of them: here S = {2, 3}, and 4 = 2 + 2 is
; in S* but not in S for both atoms, and again for the atom of the second
; check-sat, whose lambda was fully enumerated by the first.
(set-logic HO_ALL)
(set-option :incremental true)
(declare-const a Int)
(declare-const b Int)
(define-fun L ((v Int)) Bool
  (int.star-contains (lambda ((x Int)) (or (= x 2) (= x 3))) v))

(set-info :status sat)
(push 1)
(assert (L a))
(assert (L b))
(assert (= a 4))
(assert (= b 4))
(check-sat)
(pop 1)

; 9 = 2 + 7, with the cells of the first check-sat popped
(set-info :status sat)
(push 1)
(assert (L a))
(assert (= a 9))
(check-sat)
(pop 1)

; 1 is not in S*
(set-info :status unsat)
(push 1)
(assert (L a))
(assert (= a 1))
(check-sat)
(pop 1)

; a + b = 1 has no solution in S* x S*
(set-info :status unsat)
(push 1)
(assert (L a))
(assert (L b))
(assert (= (+ a b) 1))
(check-sat)
(pop 1)
