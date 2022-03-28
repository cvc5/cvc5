(set-logic QF_SLIA)
(set-option :strings-exp true)
(set-info :status sat)
(declare-fun s () (Seq Int))
(declare-fun x () Int)

(assert (= s (seq.++ (seq.unit 0) (seq.unit 1) (seq.unit 7) (seq.unit 3) (seq.unit 4) (seq.unit 5))))

(assert (not (= s (seq.update s x (seq.unit x)))))

(check-sat)
