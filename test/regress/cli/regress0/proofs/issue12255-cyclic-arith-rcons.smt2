; COMMAND-LINE: --produce-proofs --proof-check=eager
; EXPECT: sat
(set-logic ALL)
(declare-fun B () String)
(declare-fun E () String)
(declare-fun D () String)
(assert (= (str.++ B B E "a") (str.++ D D)))
(check-sat)
