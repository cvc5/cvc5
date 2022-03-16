; COMMAND-LINE: --cegqi-bv
; EXPECT: unsat
(set-logic BV)
(set-info :status unsat)
; two occurrences of x
(assert (not (exists ((?X (_ BitVec 32)) (?Y (_ BitVec 32))) (= (bvmul ?X ?Y) ?X))))
(check-sat)
(exit)
