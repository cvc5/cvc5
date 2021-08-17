(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :strings-exp true)
(set-option :strings-seq-update false)
(set-option :full-saturate-quant true)
(set-logic ALL)
; done setting options


(declare-fun ControlFlow (Int Int) Int)
(declare-fun A () (Seq Int))
(declare-fun B@2 () (Seq Int))
(declare-fun back_index@1 () Int)
(declare-fun front_index@0 () Int)
(declare-fun B@0 () (Seq Int))
(declare-fun len@0 () Int)
(declare-fun B@1 () (Seq Int))
(declare-fun front_index@1 () Int)
(declare-fun back_index@2 () Int)
(declare-fun back_index@0 () Int)
(push 1)
(set-info :boogie-vc-id reverse)
(assert (not
 (=> (= (ControlFlow 0 0) 1167) (let ((GeneratedUnifiedExit_correct  (and (=> (= (ControlFlow 0 1160) (- 0 1778)) (= (seq.len A) (seq.len B@2))) (=> (= (seq.len A) (seq.len B@2)) (=> (= (ControlFlow 0 1160) (- 0 1787)) (forall ((x Int) ) (!  (=> (and (<= 0 x) (< x (seq.len A))) (= (seq.nth A x) (seq.nth B@2 (- (- (seq.len A) 1) x))))
 :qid |testbpl.45:17|
 :skolemid |0|
)))))))
(let ((anon5_LoopDone_correct  (=> (<= back_index@1 front_index@0) (=> (and (= B@2 B@0) (= (ControlFlow 0 480) 1160)) GeneratedUnifiedExit_correct))))
(let ((anon4_Then_correct  (=> (= len@0 0) (=> (and (= B@2 A) (= (ControlFlow 0 465) 1160)) GeneratedUnifiedExit_correct))))
(let ((anon5_LoopBody_correct  (=> (and (and (< front_index@0 back_index@1) (= B@1 (seq.update (seq.update B@0 back_index@1 (seq.extract B@0 front_index@0 1)) front_index@0 (seq.extract B@0 back_index@1 1)))) (and (= front_index@1 (+ front_index@0 1)) (= back_index@2 (- back_index@1 1)))) (and (=> (= (ControlFlow 0 478) (- 0 1616)) (and (<= 0 front_index@1) (< front_index@1 (seq.len A)))) (=> (and (<= 0 front_index@1) (< front_index@1 (seq.len A))) (and (=> (= (ControlFlow 0 478) (- 0 1630)) (= (+ front_index@1 back_index@2) (- len@0 1))) (=> (= (+ front_index@1 back_index@2) (- len@0 1)) (and (=> (= (ControlFlow 0 478) (- 0 1641)) (= (seq.len A) (seq.len B@1))) (=> (= (seq.len A) (seq.len B@1)) (and (=> (= (ControlFlow 0 478) (- 0 1650)) (forall ((x@@0 Int) ) (!  (=> (and (<= 0 x@@0) (< x@@0 front_index@1)) (= (seq.nth A x@@0) (seq.nth B@1 (- (- (seq.len A) 1) x@@0))))
 :qid |testbpl.63:23|
 :skolemid |1|
))) (=> (forall ((x@@1 Int) ) (!  (=> (and (<= 0 x@@1) (< x@@1 front_index@1)) (= (seq.nth A x@@1) (seq.nth B@1 (- (- (seq.len A) 1) x@@1))))
 :qid |testbpl.63:23|
 :skolemid |1|
)) (and (=> (= (ControlFlow 0 478) (- 0 1691)) (forall ((x@@2 Int) ) (!  (=> (and (< back_index@2 x@@2) (< x@@2 (seq.len A))) (= (seq.nth A x@@2) (seq.nth B@1 (- (- (seq.len A) 1) x@@2))))
 :qid |testbpl.64:23|
 :skolemid |2|
))) (=> (forall ((x@@3 Int) ) (!  (=> (and (< back_index@2 x@@3) (< x@@3 (seq.len A))) (= (seq.nth A x@@3) (seq.nth B@1 (- (- (seq.len A) 1) x@@3))))
 :qid |testbpl.64:23|
 :skolemid |2|
)) (=> (= (ControlFlow 0 478) (- 0 1734)) (forall ((x@@4 Int) ) (!  (=> (and (<= front_index@1 x@@4) (<= x@@4 back_index@2)) (= (seq.nth A x@@4) (seq.nth B@1 x@@4)))
 :qid |testbpl.65:23|
 :skolemid |3|
))))))))))))))))
(let ((anon5_LoopHead_correct  (=> (and (and (and (<= 0 front_index@0) (< front_index@0 (seq.len A))) (= (+ front_index@0 back_index@1) (- len@0 1))) (and (and (= (seq.len A) (seq.len B@0)) (forall ((x@@5 Int) ) (!  (=> (and (<= 0 x@@5) (< x@@5 front_index@0)) (= (seq.nth A x@@5) (seq.nth B@0 (- (- (seq.len A) 1) x@@5))))
 :qid |testbpl.63:23|
 :skolemid |1|
))) (and (forall ((x@@6 Int) ) (!  (=> (and (< back_index@1 x@@6) (< x@@6 (seq.len A))) (= (seq.nth A x@@6) (seq.nth B@0 (- (- (seq.len A) 1) x@@6))))
 :qid |testbpl.64:23|
 :skolemid |2|
)) (forall ((x@@7 Int) ) (!  (=> (and (<= front_index@0 x@@7) (<= x@@7 back_index@1)) (= (seq.nth A x@@7) (seq.nth B@0 x@@7)))
 :qid |testbpl.65:23|
 :skolemid |3|
))))) (and (=> (= (ControlFlow 0 476) 480) anon5_LoopDone_correct) (=> (= (ControlFlow 0 476) 478) anon5_LoopBody_correct)))))
(let ((anon4_Else_correct  (=> (and (not (= len@0 0)) (= back_index@0 (- len@0 1))) (and (=> (= (ControlFlow 0 467) (- 0 1270)) (and (<= 0 0) (< 0 (seq.len A)))) (=> (and (<= 0 0) (< 0 (seq.len A))) (and (=> (= (ControlFlow 0 467) (- 0 1284)) (= (+ 0 back_index@0) (- len@0 1))) (=> (= (+ 0 back_index@0) (- len@0 1)) (and (=> (= (ControlFlow 0 467) (- 0 1295)) (= (seq.len A) (seq.len A))) (=> (= (seq.len A) (seq.len A)) (and (=> (= (ControlFlow 0 467) (- 0 1304)) (forall ((x@@8 Int) ) (!  (=> (and (<= 0 x@@8) (< x@@8 0)) (= (seq.nth A x@@8) (seq.nth A (- (- (seq.len A) 1) x@@8))))
 :qid |testbpl.63:23|
 :skolemid |1|
))) (=> (forall ((x@@9 Int) ) (!  (=> (and (<= 0 x@@9) (< x@@9 0)) (= (seq.nth A x@@9) (seq.nth A (- (- (seq.len A) 1) x@@9))))
 :qid |testbpl.63:23|
 :skolemid |1|
)) (and (=> (= (ControlFlow 0 467) (- 0 1345)) (forall ((x@@10 Int) ) (!  (=> (and (< back_index@0 x@@10) (< x@@10 (seq.len A))) (= (seq.nth A x@@10) (seq.nth A (- (- (seq.len A) 1) x@@10))))
 :qid |testbpl.64:23|
 :skolemid |2|
))) (=> (forall ((x@@11 Int) ) (!  (=> (and (< back_index@0 x@@11) (< x@@11 (seq.len A))) (= (seq.nth A x@@11) (seq.nth A (- (- (seq.len A) 1) x@@11))))
 :qid |testbpl.64:23|
 :skolemid |2|
)) (and (=> (= (ControlFlow 0 467) (- 0 1388)) (forall ((x@@12 Int) ) (!  (=> (and (<= 0 x@@12) (<= x@@12 back_index@0)) (= (seq.nth A x@@12) (seq.nth A x@@12)))
 :qid |testbpl.65:23|
 :skolemid |3|
))) (=> (forall ((x@@13 Int) ) (!  (=> (and (<= 0 x@@13) (<= x@@13 back_index@0)) (= (seq.nth A x@@13) (seq.nth A x@@13)))
 :qid |testbpl.65:23|
 :skolemid |3|
)) (=> (= (ControlFlow 0 467) 476) anon5_LoopHead_correct))))))))))))))))
(let ((anon0_correct  (=> (= len@0 (seq.len A)) (and (=> (= (ControlFlow 0 464) 465) anon4_Then_correct) (=> (= (ControlFlow 0 464) 467) anon4_Else_correct)))))
(let ((PreconditionGeneratedEntry_correct  (=> (= (ControlFlow 0 1167) 464) anon0_correct)))
PreconditionGeneratedEntry_correct)))))))))
))
(check-sat)
