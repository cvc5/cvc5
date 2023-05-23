; COMMAND-LINE: --sets-ext
; SCRUBBER: grep -o "which doesn't include THEORY_QUANTIFIERS"
; EXPECT: which doesn't include THEORY_QUANTIFIERS
; EXIT: 1
(set-logic QF_UFLIAFS)
(set-info :status unsat)

(declare-sort U 0)
(declare-fun a () U)
(declare-fun x () (Set U))


(assert (set.subset x (set.comprehension ((z U)) (not (= z a)) z)))

(check-sat)
