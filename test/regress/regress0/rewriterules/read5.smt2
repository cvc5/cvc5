(set-logic AUF)
(set-info :source |
Translated from old SVC processor verification benchmarks.  Contact Clark
Barrett at barrett@cs.nyu.edu for more information.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Index 0)
(declare-sort Element 0)(declare-sort Arr 0)(declare-fun aselect (Arr Index) Element)(declare-fun astore (Arr Index Element) Arr)(declare-fun k (Arr Arr) Index)
(declare-fun a () Index)
(declare-fun aaa () Index)
(declare-fun aa () Index)
(declare-fun S () Arr)
(declare-fun vvv () Element)
(declare-fun v () Element)
(declare-fun vv () Element)
(declare-fun bbb () Index)
(declare-fun www () Element)
(declare-fun bb () Index)
(declare-fun ww () Element)
(declare-fun b () Index)
(declare-fun w () Element)
(declare-fun SS () Arr)
(assert (let ((?v_3 (ite (= a aa) false true)) (?v_4 (ite (= aa aaa) false true)) (?v_1 (astore (astore (astore S a v) aa vv) aaa vvv)) (?v_0 (astore S aaa vvv)) (?v_2 (astore S aa vv))) (not (ite (ite (ite (ite (= a aaa) false true) (ite ?v_3 ?v_4 false) false) (ite (= (astore (astore ?v_0 a v) aa vv) ?v_1) (ite (= (astore (astore ?v_0 aa vv) a v) ?v_1) (ite (= (astore (astore ?v_2 a v) aaa vvv) ?v_1) (= (astore (astore ?v_2 aaa vvv) a v) ?v_1) false) false) false) true) (ite (ite (= ?v_1 (astore (astore (astore S bbb www) bb ww) b w)) (ite (ite ?v_3 (ite ?v_4 (ite (ite (= aa b) false true) (ite (ite (= aa bb) false true) (ite (= aa bbb) false true) false) false) false) false) (= (aselect S aa) vv) true) true) (ite (= S (astore SS a v)) (= S (astore SS a (aselect S a))) true) false) false))))
; rewrite rule definition of arrays theory
(assert (forall ((?x Arr) (?i Index) (?j Index) (?e Element)) (! (=> (not (= ?i ?j)) (= (aselect (astore ?x ?i ?e) ?j) (aselect ?x ?j))) :rewrite-rule)))
(assert (forall ((?x Arr) (?i Index) (?e Element)) (! (=> true (= (aselect (astore ?x ?i ?e) ?i) ?e)) :rewrite-rule)))
(assert (forall ((?x Arr) (?y Arr)) (! (=> (not (= ?x ?y)) (not (= (aselect ?x (k ?x ?y)) (aselect ?y (k ?x ?y))))) :rewrite-rule)))
(assert (forall ((?x Arr) (?y Arr)) (! (! (=> true (or (= ?x ?y) (not (= ?x ?y)))) :pattern (?x)) :rewrite-rule)))
(assert (forall ((?x Arr) (?i Index) (?j Index) (?e Element)) (! (! (=> true (or (= ?i ?j) (not (= ?i ?j)))) :pattern ((aselect (astore ?x ?i ?e) ?j))) :rewrite-rule)))(check-sat)
(exit)
