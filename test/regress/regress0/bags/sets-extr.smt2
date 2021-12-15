; COMMAND-LINE: --ext-rew-prep --ext-rew-prep-agg
; EXPECT: sat
(set-logic ALL)
(declare-sort Atom 0)

(declare-fun a () Atom)
(declare-fun b () Atom)
(declare-fun c () Atom)
(declare-fun S () (Bag Atom))


(assert (= S (bag.union_disjoint (bag a 1) (bag.union_disjoint (bag c 1) (bag b 1)))))

(check-sat)

