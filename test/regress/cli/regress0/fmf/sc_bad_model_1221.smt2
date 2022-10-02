; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-sort a 0)
(declare-fun __nun_card_witness_0 () a)
(declare-datatypes ((prod 0)) (((Pair (_select_Pair_0 a) (_select_Pair_1 a)))))
(declare-sort G_snd 0)
(declare-fun __nun_card_witness_1 () G_snd)
(declare-fun snd (prod) a)
(declare-fun proj_G_snd_0 (G_snd) prod)
(assert
 (forall ((a/32 G_snd))
    (and
     (= (snd (proj_G_snd_0 a/32)) (_select_Pair_1 (proj_G_snd_0 a/32)))
     true)))
(declare-fun p () prod)
(declare-datatypes ((pd 0)) (((Pd (_select_Pd_0 prod)))))
(declare-sort G_fs 0)
(declare-fun __nun_card_witness_2 () G_fs)
(declare-fun fs (pd) a)
(declare-fun proj_G_fs_0 (G_fs) pd)
(assert
 (forall ((a/33 G_fs))
    (and
     (= (fs (proj_G_fs_0 a/33))
      (_select_Pair_0 (_select_Pd_0 (proj_G_fs_0 a/33))))
     true)))
(assert
 (and (not (= (fs (Pd p)) (snd p)))
  (exists ((a/34 G_fs)) (= (Pd p) (proj_G_fs_0 a/34)))
  (exists ((a/35 G_snd)) (= p (proj_G_snd_0 a/35)))))
(check-sat)
