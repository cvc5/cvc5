; REQUIRES: normaliz
; COMMAND-LINE: --nl-rlv=always
; DISABLE-TESTER: proof
;
; Relevance filtering in the nonlinear extension (--nl-rlv, only available
; in quantifier-free logics) keeps the assertions needed to justify the
; input and the lemmas marked NEEDS_JUSTIFY. The reduction of a positive
; int.star-contains literal introduces skolems, so it carries that property;
; otherwise its constraints could be dropped from the nonlinear model check.
; Here S = {2}, so S* is the set of even nonnegative integers.
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
