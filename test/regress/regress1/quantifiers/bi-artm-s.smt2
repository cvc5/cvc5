; COMMAND-LINE: --fmf-bound-lazy
; EXPECT: unsat
(set-option :incremental false)
(set-info :status unsat)
(set-logic ALL)
(declare-fun Y () String)
(set-info :notes "ufP_1 is uf type conv P")
(declare-fun ufP_1 (Int) Int)
(set-info :notes "ufM_2 is uf type conv M")
(declare-fun ufM_2 (Int) Int)
(declare-fun z1_3 () String)
(declare-fun z2_4 () String)
(declare-fun z3_5 () String)
(declare-fun V_253 () String) 
(declare-fun V_254 () String)

(assert (or (= Y "1") (= Y "0")))
(assert (>= (ufP_1 0) 32))
(assert 

(forall ((V_243 Int)) 
(or 
(not (and (>= V_243 0) (>= (+ (str.len Y) (* (- 1) V_243)) 1))) 
(and 
(or (not (= (str.len Y) (+ 1 V_243))) (= (ufP_1 V_243) (ufM_2 V_243))) 
(not (>= (ufM_2 V_243) 10)) 
(not (or (not (= (str.len Y) (+ 1 V_243 (str.len V_253)))) (not (= Y (str.++ V_253 (ite (= (ufM_2 V_243) 0) "0" "1") V_254)))) ))) ))

(check-sat)
