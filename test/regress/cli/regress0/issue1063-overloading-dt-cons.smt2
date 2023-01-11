; DISABLE-TESTER: dump
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-datatypes ((Enum0 0)) (((In_Air) (On_Ground) (None))))
(declare-datatypes ((Enum1 0)) (((True) (False) (None))))
(declare-fun var_0 (Int) Enum0)
(declare-fun var_1 (Int) Enum1)
(assert (= (var_0 0) (as None Enum0)))
(assert (= (var_1 1) (as None Enum1)))
(assert (not ((_ is In_Air) (var_0 0))))
(declare-fun var_2 () Enum1)
(assert ((_ is None) var_2))
(check-sat)
