; COMMAND-LINE: --no-nl-ext-rewrite
; EXPECT: sat
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (not 

(<= 
(* (- b (- (* a a))) b) 
(- (+ (mod (abs b) (+ (int.pow2 a) (abs b))) (int.pow2 (abs (int.pow2 b))))))))
(check-sat)
