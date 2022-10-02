; COMMAND-LINE: --mbqi
; EXPECT: sat

; This triggered a failure related to datatypes model building (when symfpu is enabled)
(set-logic ALL)
(declare-datatypes ((V 0) (A 0)) (
  ((I (i Int)) (vec (v A)))
  ((arr (l Int)))))
(declare-fun E (V V) Bool)
(declare-fun eee (A) Bool)
(declare-fun a () V)
(declare-fun aa () A)
(assert (forall ((?y1 A)) (eee ?y1)))
(assert (E a a))
(assert (not (E (I 0) (I 0))))
(assert (= (l aa) (i a)))
(check-sat)
