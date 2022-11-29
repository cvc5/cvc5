; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun a () String)
(assert
 (xor
  (= (= (str.replace "B" (str.replace (str.++ (str.replace "B" a "B") a) "B" "") "B")
      (str.replace "B" (str.replace "B" a (str.++ a "B")) a))
   (not
    (= (str.replace "B" (str.replace a "B" "") "B")
     (str.replace "B" a (str.++ a "B")))))
  (= (str.replace "B" a "")
   (str.replace "B" a
    (ite (not (= (str.replace "" (str.replace a "" a) "") "")) ""
     (str.replace "" (str.replace a "B" "") "B"))))))
(set-info :status unsat)
(check-sat)
