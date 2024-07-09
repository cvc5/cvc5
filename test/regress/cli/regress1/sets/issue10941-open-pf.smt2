; COMMAND-LINE: --produce-proofs -q
; EXPECT: sat
(set-logic ALL)
(assert (= 1.0 (* 1.0 (set.choose (set.insert (arcsin 0.0) (set.singleton 1.0))))))
(check-sat)
