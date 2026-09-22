; COMMAND-LINE: -i --sat-solver=cadical
; DISABLE-TESTER: proof
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-fun s () String)
;
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (or (not a) b))
(assert (or (not b) a))
(assert (or a b))
; This part above is to force `a` to be a fixed assignment at user level 1,
; so that the literal for `(= (str.len s) 0)` will be renotified and produce
; the error
(assert (or (not a) (= (str.len s) 0)))
(push)
(check-sat)
(pop)
(check-sat)
