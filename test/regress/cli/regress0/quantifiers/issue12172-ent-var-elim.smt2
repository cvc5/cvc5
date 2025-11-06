; COMMAND-LINE: --var-ent-eq-elim-quant
; EXPECT: sat
(set-logic BV)
(assert
  (forall ((x (_ BitVec 32)))
    (exists ((e0 (_ BitVec 8))
             (e1 (_ BitVec 8))
             (e2 (_ BitVec 8))
             (e3 (_ BitVec 8)))
      (= (concat e3 (concat e2 (concat e1 e0)))
         (bvadd x (_ bv1 32))))))
(check-sat)
