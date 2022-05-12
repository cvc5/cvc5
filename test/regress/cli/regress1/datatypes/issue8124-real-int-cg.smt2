(set-logic ALL)
(set-info :status sat)

(declare-datatype RR ((rr (first_rr Real) (second_rr Real))))
(declare-datatype RI ((ri (first_ri Real) (second_ri Int))))
(declare-datatype IR ((ir (first_ir Int) (second_ir Real))))

(declare-fun x () RR)
(declare-fun t () (Set RI))
(declare-fun e () (Set IR))
(declare-fun V () Real)

(assert 
(and 
(distinct x (rr 0.0 0.0))
(not (set.member (ir (to_int (first_rr x)) (second_rr x)) e))
(not (set.member (ri (first_rr x) (to_int (second_rr x))) t)))
)

(check-sat)
