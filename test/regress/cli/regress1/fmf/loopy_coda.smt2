; COMMAND-LINE: --finite-model-find --e-matching --uf-ss-fair-monotone
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-sort a 0)
(declare-fun __nun_card_witness_0 () a)
(declare-codatatypes ((llist 0))
  (((LCons (_select_LCons_0 a) (_select_LCons_1 llist)) (LNil ))))
(declare-fun xs () llist)
(declare-fun y () a)
(declare-fun ys () llist)
(declare-sort G_lappend 0)
(declare-fun __nun_card_witness_1 () G_lappend)
(declare-fun lappend (llist llist) llist)
(declare-fun proj_G_lappend_0 (G_lappend) llist)
(declare-fun proj_G_lappend_1 (G_lappend) llist)
(assert
 (forall ((a/33 G_lappend))
    (and
     (= (lappend (proj_G_lappend_0 a/33) (proj_G_lappend_1 a/33))
      (ite ((_ is LCons) (proj_G_lappend_0 a/33))
        (LCons (_select_LCons_0 (proj_G_lappend_0 a/33))
         (lappend (_select_LCons_1 (proj_G_lappend_0 a/33))
          (proj_G_lappend_1 a/33)))
        (proj_G_lappend_1 a/33)))
     (=> ((_ is LCons) (proj_G_lappend_0 a/33))
      (exists ((a/35 G_lappend))
         (and (= (proj_G_lappend_1 a/33) (proj_G_lappend_1 a/35))
          (= (_select_LCons_1 (proj_G_lappend_0 a/33))
           (proj_G_lappend_0 a/35))))))))
(assert
 (not
  (=>
   (exists ((a/37 G_lappend))
      (and (= (LCons y ys) (proj_G_lappend_1 a/37))
       (= xs (proj_G_lappend_0 a/37))))
   (= (lappend xs (LCons y ys)) xs))))
(check-sat)
