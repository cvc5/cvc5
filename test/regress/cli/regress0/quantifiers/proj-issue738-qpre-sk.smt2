; EXPECT: sat
(set-logic ALL)
(set-option :incremental true)
(set-option :pre-skolem-quant agg)
(set-option :var-elim-quant false)
(assert (exists ((x String)) (distinct (str.< "" x) (seq.prefixof (seq.unit x) (seq.unit x)))))
(check-sat-assuming ((exists ((x String)) (distinct (str.< "" x) (seq.prefixof (seq.unit x) (seq.unit x))))))
