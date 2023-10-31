(set-logic ALL)
(set-info :status sat)
(declare-codatatypes ((S 0) (T 0)) 
(
((A (a S))) 
((B (b S)))
))
(declare-fun y () T)
(check-sat)
