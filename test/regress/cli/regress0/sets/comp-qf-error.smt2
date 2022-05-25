; COMMAND-LINE: --sets-ext
; EXPECT: (error "Set comprehensions require quantifiers in the background logic.")
; EXIT: 1
(set-logic QF_UFLIAFS)
(set-info :status unsat)

(declare-sort U 0)
(declare-fun a () U)
(declare-fun x () (Set U))


(assert (set.subset x (set.comprehension ((z U)) (not (= z a)) z)))

(check-sat)
