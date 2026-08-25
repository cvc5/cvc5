; REQUIRES: glpk
; COMMAND-LINE: --use-approx
; EXPECT: (error "Error in option parsing: approx-branch-depth = 2809892243652038984 is not a legal setting, value should be at most 2147483647.")
; EXPECT: sat
;; An out-of-range approx-branch-depth must be rejected at option-parse time.
;; Without the bound it is a valid int64 that truncates to a negative int in
;; ApproxGLPK::setBranchingDepth (Assert(bd >= 0) in assertions builds).
(set-logic QF_LIA)
(set-option :approx-branch-depth 2809892243652038984)
(declare-fun x () Int)
(declare-fun x6 () Int)
(declare-fun x4 () Int)
(assert (and (= 0 (+ x6 1 (* 2 x4))) (= 0 (+ (* x 51725) (* x6 241)))))
(check-sat)
