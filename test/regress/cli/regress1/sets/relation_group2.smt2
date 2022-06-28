(set-logic HO_ALL)

(set-info :status sat)

(declare-fun data () (Relation String String String))
(declare-fun part1 () (Relation String String String))
(declare-fun part2 () (Relation String String String))
(declare-fun partition () (Set (Relation String String String)))

(assert (distinct data part1 part2 (as set.empty (Relation String String String))))

(assert (= partition ((_ rel.group 0) data)))
(assert (set.member part1 partition))
(assert (set.member part2 partition))

(check-sat)
