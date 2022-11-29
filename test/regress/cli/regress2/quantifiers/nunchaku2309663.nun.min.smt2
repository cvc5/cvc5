; EXPECT: unsat
; COMMAND-LINE: --finite-model-find
(set-logic ALL)
(set-info :status unsat)
(declare-datatypes ((nat__ 0)) (((Suc__ (_select_Suc___0 nat__)) (zero__))))
(declare-sort a__ 0)
(declare-fun __nun_card_witness_0_ () a__)
(declare-datatypes ((tree__ 0))
   (((MKT__ (_select_MKT___0 a__) (_select_MKT___1 tree__)
        (_select_MKT___2 tree__) (_select_MKT___3 nat__))
     (ET__))))
(declare-sort G_plus__ 0)
(declare-fun __nun_card_witness_1_ () G_plus__)
(declare-fun plus__ (nat__ nat__) nat__)
(declare-fun proj_G_plus__0_ (G_plus__) nat__)
(declare-fun proj_G_plus__1_ (G_plus__) nat__)

(declare-sort G_less__eq__ 0)
(declare-fun __nun_card_witness_2_ () G_less__eq__)
(declare-fun less__eq__ (nat__ nat__) Bool)
(declare-fun proj_G_less__eq__0_ (G_less__eq__) nat__)
(declare-fun proj_G_less__eq__1_ (G_less__eq__) nat__)

(declare-sort G_max__ 0)
(declare-fun __nun_card_witness_3_ () G_max__)
(declare-fun max__ (nat__ nat__) nat__)
(declare-fun proj_G_max__0_ (G_max__) nat__)
(declare-fun proj_G_max__1_ (G_max__) nat__)

(declare-sort G_one__ 0)
(declare-fun __nun_card_witness_4_ () G_one__)
(declare-fun one__ () nat__)
(assert (forall ((a/295 G_one__)) (= one__ (Suc__ zero__))))
(declare-sort G_height__ 0)
(declare-fun __nun_card_witness_5_ () G_height__)
(declare-fun height__ (tree__) nat__)
(declare-fun proj_G_height__0_ (G_height__) tree__)

(declare-sort G_avl__ 0)
(declare-fun __nun_card_witness_6_ () G_avl__)
(declare-fun avl__ (tree__) Bool)
(declare-fun proj_G_avl__0_ (G_avl__) tree__)

(declare-fun l__ () tree__)
(declare-fun r__ () tree__)
(declare-sort G_minus__ 0)
(declare-fun __nun_card_witness_7_ () G_minus__)
(declare-fun minus__ (Bool Bool) Bool)
(declare-fun proj_G_minus__0_ (G_minus__) Bool)
(declare-fun proj_G_minus__1_ (G_minus__) Bool)

(declare-sort G_ht__ 0)
(declare-fun __nun_card_witness_8_ () G_ht__)
(declare-fun ht__ (tree__) nat__)
(declare-fun proj_G_ht__0_ (G_ht__) tree__)

(declare-sort G_mkt__ 0)
(declare-fun __nun_card_witness_9_ () G_mkt__)
(declare-fun mkt__ (a__ tree__ tree__) tree__)
(declare-fun proj_G_mkt__0_ (G_mkt__) a__)
(declare-fun proj_G_mkt__1_ (G_mkt__) tree__)
(declare-fun proj_G_mkt__2_ (G_mkt__) tree__)

(declare-fun x__ () a__)

(assert (and
(forall ((a/334 G_avl__)) (and (= (avl__ (proj_G_avl__0_ a/334)) (=> ((_ is MKT__) (proj_G_avl__0_ a/334)) (and (or (= (height__ (_select_MKT___1 (proj_G_avl__0_ a/334))) (height__ (_select_MKT___2 (proj_G_avl__0_ a/334)))) (= (height__ (_select_MKT___1 (proj_G_avl__0_ a/334))) (plus__ (height__ (_select_MKT___2 (proj_G_avl__0_ a/334))) one__)) (= (height__ (_select_MKT___2 (proj_G_avl__0_ a/334))) (plus__ (height__ (_select_MKT___1 (proj_G_avl__0_ a/334))) one__))) (= (_select_MKT___3 (proj_G_avl__0_ a/334)) (plus__ (max__ (height__ (_select_MKT___1 (proj_G_avl__0_ a/334))) (height__ (_select_MKT___2 (proj_G_avl__0_ a/334)))) one__)) (avl__ (_select_MKT___1 (proj_G_avl__0_ a/334))) (avl__ (_select_MKT___2 (proj_G_avl__0_ a/334)))))) (exists ((a/602 G_avl__)) (= (_select_MKT___2 (proj_G_avl__0_ a/334)) (proj_G_avl__0_ a/602)) ) (exists ((a/601 G_avl__)) (= (_select_MKT___1 (proj_G_avl__0_ a/334)) (proj_G_avl__0_ a/601)) ) (exists ((a/592 G_max__)) (and (= (height__ (_select_MKT___2 (proj_G_avl__0_ a/334))) (proj_G_max__1_ a/592)) (exists ((a/595 G_height__)) (= (_select_MKT___2 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/595)) ) (= (height__ (_select_MKT___1 (proj_G_avl__0_ a/334))) (proj_G_max__0_ a/592)) (exists ((a/596 G_height__)) (= (_select_MKT___1 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/596)) )) ) (exists ((a/600 G_height__)) (= (_select_MKT___2 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/600)) ) (exists ((a/599 G_height__)) (= (_select_MKT___1 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/599)) ) (exists ((a/564 G_plus__)) (and (= one__ (proj_G_plus__1_ a/564)) (= (max__ (height__ (_select_MKT___1 (proj_G_avl__0_ a/334))) (height__ (_select_MKT___2 (proj_G_avl__0_ a/334)))) (proj_G_plus__0_ a/564)) (exists ((a/581 G_height__)) (= (_select_MKT___1 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/581)) ) (exists ((a/582 G_height__)) (= (_select_MKT___2 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/582)) ) (exists ((a/574 G_max__)) (and (= (height__ (_select_MKT___2 (proj_G_avl__0_ a/334))) (proj_G_max__1_ a/574)) (exists ((a/577 G_height__)) (= (_select_MKT___2 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/577)) ) (= (height__ (_select_MKT___1 (proj_G_avl__0_ a/334))) (proj_G_max__0_ a/574)) (exists ((a/578 G_height__)) (= (_select_MKT___1 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/578)) )) )) ) (exists ((a/551 G_height__)) (= (_select_MKT___1 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/551)) ) (exists ((a/550 G_height__)) (= (_select_MKT___2 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/550)) ) (exists ((a/557 G_height__)) (= (_select_MKT___1 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/557)) ) (exists ((a/552 G_plus__)) (and (= one__ (proj_G_plus__1_ a/552)) (= (height__ (_select_MKT___2 (proj_G_avl__0_ a/334))) (proj_G_plus__0_ a/552)) (exists ((a/554 G_height__)) (= (_select_MKT___2 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/554)) )) ) (exists ((a/556 G_height__)) (= (_select_MKT___2 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/556)) ) (exists ((a/563 G_height__)) (= (_select_MKT___2 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/563)) ) (exists ((a/558 G_plus__)) (and (= one__ (proj_G_plus__1_ a/558)) (= (height__ (_select_MKT___1 (proj_G_avl__0_ a/334))) (proj_G_plus__0_ a/558)) (exists ((a/560 G_height__)) (= (_select_MKT___1 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/560)) )) ) (exists ((a/562 G_height__)) (= (_select_MKT___1 (proj_G_avl__0_ a/334)) (proj_G_height__0_ a/562)) )) )
(forall ((a/603 G_minus__)) (= (minus__ (proj_G_minus__0_ a/603) (proj_G_minus__1_ a/603)) (ite (proj_G_minus__0_ a/603) (ite (proj_G_minus__1_ a/603) (and (proj_G_minus__0_ a/603) (not (proj_G_minus__1_ a/603))) (and (proj_G_minus__0_ a/603) (not (proj_G_minus__1_ a/603)))) (ite (proj_G_minus__1_ a/603) (and (proj_G_minus__0_ a/603) (not (proj_G_minus__1_ a/603))) (and (proj_G_minus__0_ a/603) (not (proj_G_minus__1_ a/603)))))) )
(forall ((a/296 G_height__)) (and (= (height__ (proj_G_height__0_ a/296)) (ite ((_ is MKT__) (proj_G_height__0_ a/296)) (plus__ (max__ (height__ (_select_MKT___1 (proj_G_height__0_ a/296))) (height__ (_select_MKT___2 (proj_G_height__0_ a/296)))) one__) zero__)) (=> ((_ is MKT__) (proj_G_height__0_ a/296)) (and (exists ((a/297 G_plus__)) (and (= one__ (proj_G_plus__1_ a/297)) (= (max__ (height__ (_select_MKT___1 (proj_G_height__0_ a/296))) (height__ (_select_MKT___2 (proj_G_height__0_ a/296)))) (proj_G_plus__0_ a/297)) (exists ((a/314 G_height__)) (= (_select_MKT___1 (proj_G_height__0_ a/296)) (proj_G_height__0_ a/314)) ) (exists ((a/315 G_height__)) (= (_select_MKT___2 (proj_G_height__0_ a/296)) (proj_G_height__0_ a/315)) ) (exists ((a/307 G_max__)) (and (= (height__ (_select_MKT___2 (proj_G_height__0_ a/296))) (proj_G_max__1_ a/307)) (exists ((a/310 G_height__)) (= (_select_MKT___2 (proj_G_height__0_ a/296)) (proj_G_height__0_ a/310)) ) (= (height__ (_select_MKT___1 (proj_G_height__0_ a/296))) (proj_G_max__0_ a/307)) (exists ((a/311 G_height__)) (= (_select_MKT___1 (proj_G_height__0_ a/296)) (proj_G_height__0_ a/311)) )) )) ) (exists ((a/332 G_height__)) (= (_select_MKT___1 (proj_G_height__0_ a/296)) (proj_G_height__0_ a/332)) ) (exists ((a/333 G_height__)) (= (_select_MKT___2 (proj_G_height__0_ a/296)) (proj_G_height__0_ a/333)) ) (exists ((a/325 G_max__)) (and (= (height__ (_select_MKT___2 (proj_G_height__0_ a/296))) (proj_G_max__1_ a/325)) (exists ((a/328 G_height__)) (= (_select_MKT___2 (proj_G_height__0_ a/296)) (proj_G_height__0_ a/328)) ) (= (height__ (_select_MKT___1 (proj_G_height__0_ a/296))) (proj_G_max__0_ a/325)) (exists ((a/329 G_height__)) (= (_select_MKT___1 (proj_G_height__0_ a/296)) (proj_G_height__0_ a/329)) )) )))) )
(forall ((a/604 G_ht__)) (= (ht__ (proj_G_ht__0_ a/604)) (ite ((_ is MKT__) (proj_G_ht__0_ a/604)) (_select_MKT___3 (proj_G_ht__0_ a/604)) zero__)) )

(not (=> (and (avl__ l__) (exists ((a/1961 G_avl__)) (= l__ (proj_G_avl__0_ a/1961)) )) (=> (and (avl__ r__) (exists ((a/2175 G_avl__)) (= r__ (proj_G_avl__0_ a/2175)) )) (=> (or (and (= (height__ l__) (height__ r__)) (exists ((a/2334 G_height__)) (= l__ (proj_G_height__0_ a/2334)) ) (exists ((a/2333 G_height__)) (= r__ (proj_G_height__0_ a/2333)) )) (and (minus__ (= (height__ l__) (plus__ (height__ r__) one__)) (= (height__ r__) (plus__ (height__ l__) one__))) (exists ((a/2382 G_height__)) (= l__ (proj_G_height__0_ a/2382)) ) (exists ((a/2378 G_plus__)) (and (= one__ (proj_G_plus__1_ a/2378)) (= (height__ l__) (proj_G_plus__0_ a/2378)) (exists ((a/2380 G_height__)) (= l__ (proj_G_height__0_ a/2380)) )) ) (exists ((a/2383 G_height__)) (= r__ (proj_G_height__0_ a/2383)) ) (exists ((a/2376 G_height__)) (= r__ (proj_G_height__0_ a/2376)) ) (exists ((a/2372 G_plus__)) (and (= one__ (proj_G_plus__1_ a/2372)) (= (height__ r__) (proj_G_plus__0_ a/2372)) (exists ((a/2374 G_height__)) (= r__ (proj_G_height__0_ a/2374)) )) ) (exists ((a/2377 G_height__)) (= l__ (proj_G_height__0_ a/2377)) ) (exists ((a/2335 G_minus__)) (and (= (= (height__ r__) (plus__ (height__ l__) one__)) (proj_G_minus__1_ a/2335)) (exists ((a/2352 G_height__)) (= l__ (proj_G_height__0_ a/2352)) ) (exists ((a/2348 G_plus__)) (and (= one__ (proj_G_plus__1_ a/2348)) (= (height__ l__) (proj_G_plus__0_ a/2348)) (exists ((a/2350 G_height__)) (= l__ (proj_G_height__0_ a/2350)) )) ) (exists ((a/2353 G_height__)) (= r__ (proj_G_height__0_ a/2353)) ) (= (= (height__ l__) (plus__ (height__ r__) one__)) (proj_G_minus__0_ a/2335)) (exists ((a/2358 G_height__)) (= r__ (proj_G_height__0_ a/2358)) ) (exists ((a/2354 G_plus__)) (and (= one__ (proj_G_plus__1_ a/2354)) (= (height__ r__) (proj_G_plus__0_ a/2354)) (exists ((a/2356 G_height__)) (= r__ (proj_G_height__0_ a/2356)) )) ) (exists ((a/2359 G_height__)) (= l__ (proj_G_height__0_ a/2359)) )) ))) (=> (exists ((a/2384 G_avl__)) (and (= (mkt__ x__ l__ r__) (proj_G_avl__0_ a/2384)) (exists ((a/2385 G_mkt__)) (and (= r__ (proj_G_mkt__2_ a/2385)) (= l__ (proj_G_mkt__1_ a/2385)) (= x__ (proj_G_mkt__0_ a/2385))) )) ) (=> (exists ((a/2387 G_mkt__)) (and (= r__ (proj_G_mkt__2_ a/2387)) (= l__ (proj_G_mkt__1_ a/2387)) (= x__ (proj_G_mkt__0_ a/2387))) ) (avl__ (mkt__ x__ l__ r__))))))))
(forall ((a/605 G_mkt__)) (and (= (mkt__ (proj_G_mkt__0_ a/605) (proj_G_mkt__1_ a/605) (proj_G_mkt__2_ a/605)) (MKT__ (proj_G_mkt__0_ a/605) (proj_G_mkt__1_ a/605) (proj_G_mkt__2_ a/605) (plus__ (max__ (ht__ (proj_G_mkt__1_ a/605)) (ht__ (proj_G_mkt__2_ a/605))) one__))) (exists ((a/671 G_max__)) (and (= (ht__ (proj_G_mkt__2_ a/605)) (proj_G_max__1_ a/671)) (exists ((a/674 G_ht__)) (= (proj_G_mkt__2_ a/605) (proj_G_ht__0_ a/674)) ) (= (ht__ (proj_G_mkt__1_ a/605)) (proj_G_max__0_ a/671)) (exists ((a/675 G_ht__)) (= (proj_G_mkt__1_ a/605) (proj_G_ht__0_ a/675)) )) ) (exists ((a/679 G_ht__)) (= (proj_G_mkt__2_ a/605) (proj_G_ht__0_ a/679)) ) (exists ((a/678 G_ht__)) (= (proj_G_mkt__1_ a/605) (proj_G_ht__0_ a/678)) ) (exists ((a/643 G_plus__)) (and (= one__ (proj_G_plus__1_ a/643)) (= (max__ (ht__ (proj_G_mkt__1_ a/605)) (ht__ (proj_G_mkt__2_ a/605))) (proj_G_plus__0_ a/643)) (exists ((a/660 G_ht__)) (= (proj_G_mkt__1_ a/605) (proj_G_ht__0_ a/660)) ) (exists ((a/661 G_ht__)) (= (proj_G_mkt__2_ a/605) (proj_G_ht__0_ a/661)) ) (exists ((a/653 G_max__)) (and (= (ht__ (proj_G_mkt__2_ a/605)) (proj_G_max__1_ a/653)) (exists ((a/656 G_ht__)) (= (proj_G_mkt__2_ a/605) (proj_G_ht__0_ a/656)) ) (= (ht__ (proj_G_mkt__1_ a/605)) (proj_G_max__0_ a/653)) (exists ((a/657 G_ht__)) (= (proj_G_mkt__1_ a/605) (proj_G_ht__0_ a/657)) )) )) )) )
(forall ((a/295 G_one__)) (= one__ (Suc__ zero__)) )

))

(check-sat)
