; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((TypeGeneric 0)) (((generic))))
(declare-fun f (TypeGeneric) Int)
(declare-fun a () TypeGeneric)
(check-sat-assuming ( (not (= (f a) 0)) ))
