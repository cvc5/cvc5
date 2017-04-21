; COMMAND-LINE: --sets-ext
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () (Set Int))
(declare-fun P ((Set Int)) Bool)

(assert (P x))
(assert (not (P (singleton 0))))
(assert (member 1 x))
(assert (not (member 0 (as univset (Set Int)))))

(check-sat)
