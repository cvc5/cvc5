; EXPECT: sat
(set-logic QF_SLIA)
(declare-const x String)
(declare-const x1 Int)
(set-option :produce-proofs true)
(declare-const _x String)
(check-sat-assuming ((>= 0 (ite (= x (str.++ (str.from_code 0) (str.replace_all x (str.from_code 0) (str.++ (str.from_code 0) (str.from_code 0))) _x) (ite false x (str.++ _x _x _x)) x) x1 0))))