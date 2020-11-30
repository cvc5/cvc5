; COMMAND-LINE: --ext-rew-prep --ext-rew-prep-agg
; EXPECT: sat
(set-logic ALL)
(declare-sort Atom 0)

(declare-fun a () Atom)
(declare-fun b () Atom)
(declare-fun c () Atom)
(declare-fun S () (Set Atom))


(assert (= S (union (singleton a) (union (singleton c) (singleton b)))))

(check-sat)

