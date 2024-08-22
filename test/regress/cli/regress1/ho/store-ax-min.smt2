; COMMAND-LINE: --full-saturate-quant --ho-elim-store-ax
; COMMAND-LINE: --full-saturate-quant --ho-elim

(set-logic HO_ALL)
(set-info :status unsat)
(declare-sort $$unsorted 0)
(declare-fun tptp.a () $$unsorted)
(declare-fun tptp.b () $$unsorted)
(assert (not (= tptp.a tptp.b)))
(assert (not (exists ((F (-> $$unsorted $$unsorted)) (G (-> $$unsorted $$unsorted))) (not (= F G)))))
(set-info :filename store-ax-min)
(check-sat-assuming ( true ))
