; COMMAND-LINE: --ext-rew-prep=agg
; EXPECT: sat
(set-logic ALL)
(declare-fun a () Real)   
(declare-fun b () Int)     
(declare-fun c () Int)            
(declare-fun d () Int)  
(declare-fun e () Int)  
(assert (let ((?v_2 (* b 1)))(let ((?v_5 (* c 1)))
(let ((?v_6 (* (ite (< ?v_2 0) ?v_2 0) (ite (< ?v_5 0) ?v_5 0))))          
(= (+ (* a d) e) (- ?v_6))))))   
(check-sat)
