; COMMAND-LINE: --parse-skolem-definitions --print-skolem-definitions
; EXPECT: unsat
(set-option :parse-skolem-definitions true)
(set-logic QF_AUFNIA)
(set-info :status unsat)
(declare-fun b () (Array Int Int))
(declare-fun a () (Array Int Int))
(assert (not (= a b)))
(assert (= (select a (@array_deq_diff a b)) (select b (@array_deq_diff a b))))
(check-sat)