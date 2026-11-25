; COMMAND-LINE: --strings-alpha-card=3
; EXPECT: sat
; EXPECT: (((and (< (str.to_code x) 3) (< (str.to_code y) 3) (< (str.to_code z) 3)) true))
(set-logic QF_SLIA)
(set-option :produce-models true)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (distinct x y z))
(assert (= (str.len x) 1))
(assert (= (str.len y) 1))
(assert (= (str.len z) 1))
(check-sat)
(get-value ((and (< (str.to_code x) 3) (< (str.to_code y) 3) (< (str.to_code z) 3))))
