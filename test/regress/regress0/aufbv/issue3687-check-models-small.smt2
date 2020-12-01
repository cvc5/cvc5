; EXPECT: sat
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (_ BitVec 2))
(assert (distinct #b01 (select (store (store a #b01 (bvor #b01 (select a
  #b00))) #b10 #b00) b)))
(check-sat)