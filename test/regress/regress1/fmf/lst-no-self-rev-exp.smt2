; COMMAND-LINE: --finite-model-find --dt-rewrite-error-sel --lang=smt2.5
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(declare-datatypes () ((Nat (succ (pred Nat)) (zero)) (Lst (cons (hd Nat) (tl Lst)) (nil))))

(declare-fun app (Lst Lst) Lst)
(declare-fun rev (Lst) Lst)
 
(declare-sort I_app 0)
(declare-sort I_rev 0)

(declare-fun a () I_app)
(declare-fun b () I_app)
(assert (not (= a b)))

(declare-fun app_0_3 (I_app) Lst)
(declare-fun app_1_4 (I_app) Lst)
(declare-fun rev_0_5 (I_rev) Lst)

(declare-fun xs () Lst)

(assert (and
 
(forall ((?i I_app)) (= (app (app_0_3 ?i) (app_1_4 ?i)) (ite (is-cons (app_0_3 ?i)) (cons (hd (app_0_3 ?i)) (app (tl (app_0_3 ?i)) (app_1_4 ?i))) (app_1_4 ?i))) ) 
 
(forall ((?i I_rev)) (= (rev (rev_0_5 ?i)) (ite (is-cons (rev_0_5 ?i)) (app (rev (tl (rev_0_5 ?i))) (cons (hd (rev_0_5 ?i)) nil)) nil)) ) 

(forall ((?i I_rev)) (or (not (is-cons (rev_0_5 ?i))) (and (not (forall ((?z I_app)) (not (and (= (app_0_3 ?z) (rev (tl (rev_0_5 ?i)))) (= (app_1_4 ?z) (cons (hd (rev_0_5 ?i))  nil)))) )) (not (forall ((?z I_rev)) (not (= (rev_0_5 ?z) (tl (rev_0_5 ?i)) )) )))) )

(not (or (= xs (rev xs)) (forall ((?z I_rev)) (not (= (rev_0_5 ?z) xs)) )))
  
))
  
(check-sat)

