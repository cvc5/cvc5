(set-logic ALL) 
(set-info :status unsat)
 
(declare-sort Loc 0) 
(declare-heap (Loc Loc)) 
 
(declare-const z Loc) 
(declare-const y Loc) 
(declare-const x Loc) 
 
(assert 
  (sep 
    (not (wand 
      sep.emp 
      (not (pto x z)) 
    ))  
    (distinct y z) 
    (distinct y x) 
    (distinct z x) 
  ) 
) 
 
(assert 
  (pto x y) 
) 
 
(check-sat) 

