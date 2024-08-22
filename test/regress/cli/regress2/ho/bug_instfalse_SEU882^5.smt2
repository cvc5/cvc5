; COMMAND-LINE:  --full-saturate-quant --ho-elim
(set-logic HO_ALL)
(set-info :status unsat)
(declare-sort $$unsorted 0)
(assert (not (forall ((Xy $$unsorted)) (exists ((Xf (-> $$unsorted $$unsorted)) (Xx $$unsorted)) (= (@ Xf Xx) Xy)))))
(set-info :filename bug_instfalse_SEU882^5)
(check-sat-assuming ( true ))
