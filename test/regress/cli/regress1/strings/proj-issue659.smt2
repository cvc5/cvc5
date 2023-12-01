; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :sets-ext true)
(set-option :strings-eager-reg false)
(declare-const x String)
(declare-const x3 String)
(check-sat-assuming ((set.member (set.choose (set.complement (set.singleton x3))) (set.singleton x3)) (or (str.< x x3) (set.member (set.choose (set.complement (set.singleton x3))) (set.singleton x3)))))
