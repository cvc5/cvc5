; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(set-option :produce-models true)

(declare-fun |A| () String)
(declare-fun |B| () String)
(declare-fun |c| () String)

(assert (not (=>
(not (= (str.indexof A c 0) (- 1)))
(= (str.indexof (str.++ A B) c 0) (str.indexof A c 0)))))

(check-sat)
