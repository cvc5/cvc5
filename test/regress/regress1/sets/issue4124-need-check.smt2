; COMMAND-LINE: --sets-infer-as-lemmas --simplification=none
; EXPECT: sat
(set-logic ALL)
(declare-fun b () (Set (Tuple String Int))) 
(declare-fun c () (Set (Tuple Int String))) 
(declare-fun d () (Set (Tuple String String))) 
(declare-fun f () (Set Int)) 
(declare-fun e () Int) 
(assert (= b (set.insert (tuple "" 1)  (tuple "" 2) (set.singleton (tuple "" 4))))) 
(assert (= c (set.insert (tuple 1 "1") (tuple 2 "2") (set.singleton (tuple 7 ""))))) 
(assert (= d (rel.join b c)))    
(assert (= e (set.card f))) 
(check-sat)
