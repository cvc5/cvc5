; EXPECT: false
(set-logic LIA)
(set-option :ext-rewrite-quant true)
(get-qe (forall ((q92 Int) (q93 Bool) (q94 Bool)) (=> (< q92 541) (and (not (not (<= 94 660))) q93 (< 94 660) q94 q94))))
