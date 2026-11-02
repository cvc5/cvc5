; REQUIRES: normaliz
; REQUIRES: unrestricted-mode
; COMMAND-LINE: --nl-rlv=always
; DISABLE-TESTER: proof
;
; Relevance filtering in the nonlinear extension (--nl-rlv, only available
; in quantifier-free logics) keeps the assertions needed to justify the
; input and the lemmas marked NEEDS_JUSTIFY. The reduction of a positive
; int.star-contains literal, with or without skolems, is the only constraint
; that keeps the vector in S*, and the split on p(y) certifies the
; model-value shortcut, so both carry that property; otherwise their
; literals could be dropped from the nonlinear model check.
(set-logic HO_QF_UFNIA)
(set-option :incremental true)
(set-option :quiet true)
(declare-const a Int)

; a = 4 is in S*
(set-info :status sat)
(push 1)
(assert (int.star-contains (lambda ((x Int)) (= x 2)) a))
(assert (= (* a a) 16))
(check-sat)
(pop 1)

; a = 3 or a = -3, neither is in S*
(set-info :status unsat)
(push 1)
(assert (int.star-contains (lambda ((x Int)) (= x 2)) a))
(assert (= (* a a) 9))
(check-sat)
(pop 1)

; S = {5}: the coordinate (* a a) is in S* only for a = 0 or a multiple of 5.
; The linear model may give (* a a) the abstract value 5, which passes the
; model-value shortcut; the split literal (= (* a a) 5) then has to stay in
; the nonlinear model check.
(set-info :status unsat)
(push 1)
(assert (>= a 2))
(assert (<= a 4))
(assert (int.star-contains (lambda ((x Int)) (= x 5)) (* a a)))
(check-sat)
(pop 1)

; S = {4}: a = 4 with (* a a) = 16 is the smallest solution
(set-info :status sat)
(push 1)
(assert (>= a 3))
(assert (int.star-contains (lambda ((x Int)) (= x 4)) (* a a)))
(check-sat)
(pop 1)

; S = {}: its star is {0}, and the reduction (= L (= (* a a) 0)) has no
; skolems. Its literal (= (* a a) 0) still has to stay in the nonlinear model
; check, or the model repair gives (* a a) its real value.
(set-info :status unsat)
(push 1)
(assert (>= a 1))
(assert (int.star-contains (lambda ((x Int)) false) (* a a)))
(check-sat)
(pop 1)

; a = 0 is the only solution
(set-info :status sat)
(push 1)
(assert (>= a -1))
(assert (<= a 1))
(assert (int.star-contains (lambda ((x Int)) false) (* a a)))
(check-sat)
(pop 1)
