; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun r () String)
(declare-fun tr () String)
(declare-fun t () String)
(assert (not (= tr r)))
(assert (= (str.prefixof "b" (str.++ r (str.++ (str.from_int (str.len (str.++
  tr t))) "b"))) (= tr (str.++ (str.from_int (str.len (str.++ tr t))) (str.++
  t "b")))))
(check-sat)
