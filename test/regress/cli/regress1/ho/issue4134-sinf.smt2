; COMMAND-LINE: --sort-inference
; EXPECT: sat
(set-logic HO_ALL)
(set-option :sort-inference true)
(set-info :status sat)
(declare-fun a () Int)
(declare-fun b (Int) Int)
(declare-fun c (Int) Int)
(declare-fun d (Int) Int)
(assert (distinct d (ite (= a 0) b c)))
(assert (= (d 0) 0))
(check-sat)
