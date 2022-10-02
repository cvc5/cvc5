; COMMAND-LINE: -i
; EXPECT: sat
(set-logic ALL)
(set-option :strings-lazy-pp false)
(declare-fun ufbi4 (Bool Bool Bool Bool) Int)
(declare-fun str0 () String)
(declare-fun str8 () String)
(declare-fun i16 () Int)
(assert (= (str.to_int str0) (ufbi4 false true false (= 0 i16))))
(push)
(assert (= str8 (str.from_int (str.to_int str0))))
(push)
(check-sat)
