; COMMAND-LINE: --fp-exp
; EXPECT: unsat
(set-logic QF_BVFP)
(declare-const x (_ BitVec 1))
(declare-const rm RoundingMode)
(assert (or
  (distinct ((_ to_fp 5 11) rm #b1) (fp #b1 #b01111 #b0000000000))
  (distinct ((_ to_fp 5 11) rm #b0) (_ +zero 5 11))
  (ite
     (= x #b1)
     (= ((_ to_fp 5 11) rm x) ((_ to_fp_unsigned 5 11) rm x))
     (distinct ((_ to_fp 5 11) rm x) ((_ to_fp_unsigned 5 11) rm x))
  )
  ))
(check-sat)
