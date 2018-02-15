; COMMAND-LINE: --finite-model-find --fmf-inst-engine
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(set-info :status unsat)
(declare-sort I_fb 0)
(declare-fun fb_arg_0_1 (I_fb) Int)
(declare-fun fb (Int) Int)

(assert (forall ((?j I_fb)) (= (fb (fb_arg_0_1 ?j)) (ite (not (>= (fb_arg_0_1 ?j) 2)) (fb_arg_0_1 ?j) (+ (fb (+ (- 1) (fb_arg_0_1 ?j))) (fb (+ (- 2) (fb_arg_0_1 ?j)))))) ) )

(assert (forall ((?i I_fb)) (ite (not (>= (fb_arg_0_1 ?i) 2)) true (and (not (forall ((?z I_fb)) (not (= (fb_arg_0_1 ?i) (+ 1 (fb_arg_0_1 ?z)))) )) (not (forall ((?z I_fb)) (not (= (fb_arg_0_1 ?i) (+ 2 (fb_arg_0_1 ?z)))) )))) ) )

(assert (forall ((?i I_fb)) (or (>= (fb_arg_0_1 ?i) 2) (and (not (>= (fb_arg_0_1 ?i) 2)) (not (forall ((?z I_fb)) (not (= (fb_arg_0_1 ?i) (+ 1 (fb_arg_0_1 ?z)))) )) (not (forall ((?z I_fb)) (not (= (fb_arg_0_1 ?i) (+ 2 (fb_arg_0_1 ?z)))) )))) ))


(assert (not (= (fb 5) 5)) )
(assert (not (forall ((?z I_fb)) (not (= (fb_arg_0_1 ?z) 5)) )))

(check-sat)