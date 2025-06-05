; COMMAND-LINE:
; COMMAND-LINE: --strings-rec-arith-approx
; EXPECT: unsat
(set-logic ALL)
(declare-fun u () String)
(assert (= 0 (ite (not (= "o" (str.substr (str.substr u 0 0) 0 (str.len (str.substr (str.substr u 1 1) 0 (str.indexof (str.substr u 0 1) "/" 0)))))) 1 0)))
(check-sat)
