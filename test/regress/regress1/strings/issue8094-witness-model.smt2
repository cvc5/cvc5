; COMMAND-LINE: --strings-exp -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun v () String)
(declare-fun r () Bool)
(declare-fun w () String)
(assert (forall ((V String)) (or r (exists ((V String)) (str.in_re (str.++ "z" v) (re.* (str.to_re (str.from_code (str.len v)))))))))
(assert (= w (str.++ v "A")))
(check-sat)
