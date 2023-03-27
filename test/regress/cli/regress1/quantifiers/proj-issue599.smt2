; COMMAND-LINE: --cegqi-all
; EXPECT: sat
(set-logic ALL)
(declare-const x1 Bool)
(set-option :sets-ext true)
(set-option :ieval use)
(declare-const x (Set Bool))
(declare-fun _x ((Set Bool) Bool (Set Bool) (Set Bool) Bool) Bool)
(check-sat-assuming ((and (= x (set.complement x)) (_x x (and (set.is_singleton x) (exists ((x9 (Set Bool))) (_x x9 (_x x9 false x9 x9 false) x9 x9 (=> x1 x1)))) x x false))))
