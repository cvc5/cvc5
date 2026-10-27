; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () (Seq Int))
(declare-fun z () (Seq Int))

(assert (= (str.len y) (str.len z)))
(assert (= (seq.++ (seq.unit 0) (seq.unit 1) y (seq.unit x) (seq.unit 0) (seq.unit 1) y)
           (seq.++ (seq.unit 0) (seq.unit 1) z (seq.unit x) (seq.unit 1) (seq.unit 1) z))
)
; requires a distinct value inference after concat_unify
(check-sat)
