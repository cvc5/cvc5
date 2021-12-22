; COMMAND-LINE: --sets-infer-as-lemmas --simplification=none
; EXPECT: sat
(set-logic ALL)
(declare-fun b () (Bag (Tuple String Int)))
(declare-fun c () (Bag (Tuple Int String)))
(declare-fun d () (Bag (Tuple String String)))
(declare-fun f () (Bag Int))
(declare-fun e () Int) 
(assert (= b (set.insert (tuple "" 1)  (tuple "" 2) (set.singleton (tuple "" 4))))) 
(assert (= c (set.insert (tuple 1 "1") (tuple 2 "2") (set.singleton (tuple 7 ""))))) 
(assert (= d (rel.join b c)))    
(assert (= e (bag.card f)))
(check-sat)
