; COMMAND-LINE: --finite-model-find
; EXPECT: unknown
(set-logic HO_ALL)
(declare-sort $$unsorted 0)
(declare-fun tptp.cK ((-> $$unsorted Bool) $$unsorted) Bool)
(assert (not (=> (forall ((X (-> $$unsorted Bool)) (Y (-> $$unsorted Bool))) (= (@ tptp.cK (lambda ((Xz $$unsorted)) (or (@ X Xz) (@ Y Xz)))) (lambda ((Xw $$unsorted)) (or (@ (@ tptp.cK X) Xw) (@ (@ tptp.cK Y) Xw))))) (forall ((X (-> $$unsorted Bool)) (Y (-> $$unsorted Bool))) (=> (forall ((Xx $$unsorted)) (=> (@ X Xx) (@ Y Xx))) (forall ((Xx $$unsorted)) (=> (@ (@ tptp.cK X) Xx) (@ (@ tptp.cK Y) Xx))))))))
(set-info :filename soundness_fmf_SYO362^5-delta)
(check-sat-assuming ( true ))
