(set-logic HO_ALL)

(set-info :status sat)

(declare-fun data () (Table String String String))
(declare-fun part1 () (Table String String String))
(declare-fun part2 () (Table String String String))
(declare-fun partition () (Bag (Table String String String)))

(assert (distinct data part1 part2 (as bag.empty (Table String String String))))

(assert (= partition ((_ table.group 0) data)))
(assert (bag.member part1 partition))
(assert (bag.member part2 partition))

(check-sat)
