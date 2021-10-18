; COMMAND-LINE: --sets-infer-as-lemmas --simplification=none
; EXPECT: sat
(set-logic ALL)
(declare-fun b () (Set (Tuple String Int))) 
(declare-fun c () (Set (Tuple Int String))) 
(declare-fun d () (Set (Tuple String String))) 
(declare-fun f () (Set Int)) 
(declare-fun e () Int) 
(assert (= b (insert (tuple "" 1)  (tuple "" 2) (singleton (tuple "" 4))))) 
(assert (= c (insert (tuple 1 "1") (tuple 2 "2") (singleton (tuple 7 ""))))) 
(assert (= d (join b c)))    
(assert (= e (card f))) 
(check-sat)
