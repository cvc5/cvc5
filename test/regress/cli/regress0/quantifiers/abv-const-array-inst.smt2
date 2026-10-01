; COMMAND-LINE: --arrays-exp --mbqi
; EXPECT: unsat
(set-logic ABV)
(assert
  (forall ((x (Array (_ BitVec 32) (_ BitVec 32))) (i (_ BitVec 32)))
    (= (select x i) (_ bv0 32))
  )
)
(check-sat)
