; COMMAND-LINE: --symmetry-breaker-exp
(set-logic ALL)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun C () (Set Int))

(assert (and (member x A) (member x B) (member x C)))

(check-sat)
