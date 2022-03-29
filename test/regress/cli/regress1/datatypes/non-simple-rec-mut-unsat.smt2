; COMMAND-LINE: --dt-nested-rec
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-datatypes ((E 0)(T 0)) (
((Yes) (No))
((FMap (m (Array E E))) (Map (mm (Array E T))) (None) )
))
(declare-fun a () T)
(declare-fun b () T)
(declare-fun c () T)
(assert (distinct a b c))
(assert ((_ is FMap) a))
(assert ((_ is FMap) b))
(assert ((_ is FMap) c))
(assert (= (select (m a) Yes) (select (m b) Yes)))
(assert (= (select (m b) Yes) (select (m c) Yes)))
(check-sat)
