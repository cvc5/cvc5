; COMMAND-LINE: --sygus-inst -q
; EXPECT: sat
(set-logic NIA)
(set-option :sygus-inst true)

(set-info :status sat)
(declare-fun d () Int)
(assert (forall ((g Int)) (or (> 1 g) (> g (div 1 d)))))
(assert (not (= d 0)))
(check-sat)
