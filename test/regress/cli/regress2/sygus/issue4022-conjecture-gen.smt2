; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-option :conjecture-gen true)
(set-option :quant-ind true)
(set-option :sygus-inference try)
(set-info :status sat)
(declare-fun a (Int) Bool)
(assert (exists ((b Int)) (a b)))
(check-sat)
