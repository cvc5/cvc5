; COMMAND-LINE: --incremental --check-proofs --proof-check=eager
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-const S String)
(declare-const t String)
(assert (> (str.len t) 1))
(assert (! true :named IP_1))
(assert (! true :named IP_2))
(check-sat)
(assert (str.in_re (str.replace "A" S "") (str.to_re t)))
(check-sat-assuming (IP_2))
(check-sat-assuming (IP_1))
(check-sat)
