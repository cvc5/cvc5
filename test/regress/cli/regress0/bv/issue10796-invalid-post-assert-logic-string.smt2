; SCRUBBER: grep set-logic
; EXPECT: (set-logic QF_UFBVNIA)
; EXIT: 0
; Regression test to detect invalid post-assert logic string (QF_UFBVNA)
(set-logic QF_BV)
(set-option :solve-bv-as-int sum)
(set-option :output post-asserts)
(declare-const a (_ BitVec 1))
(assert (not (= a #b0)))
(check-sat)
