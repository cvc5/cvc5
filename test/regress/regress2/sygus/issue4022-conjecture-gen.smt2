; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-option :conjecture-filter-model true)
(set-option :conjecture-gen true)
(set-option :conjecture-no-filter true)
(set-option :quant-ind true)
(set-option :sygus-inference true)
(set-info :status sat)
(declare-fun a (Int) Bool)
(assert (exists ((b Int)) (a b)))
(check-sat)
