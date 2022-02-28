; COMMAND-LINE: --ext-rew-prep=agg
; EXPECT: sat
(set-logic ALL)
(declare-sort Atom 0)

(declare-fun a () Atom)
(declare-fun b () Atom)
(declare-fun c () Atom)
(declare-fun S () (Set Atom))


(assert (= S (set.union (set.singleton a) (set.union (set.singleton c) (set.singleton b)))))

(check-sat)

