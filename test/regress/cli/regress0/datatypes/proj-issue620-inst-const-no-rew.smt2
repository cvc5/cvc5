; EXPECT: sat
(set-logic ALL)
(set-option :ee-mode central)
(declare-datatypes ((d 0)) (((c (s Int)))))
(declare-const _x Int)
(declare-const x (Array Int d))
(assert ((_ divisible 3) (s (select (store x _x (select x 0)) 0))))
(check-sat)
