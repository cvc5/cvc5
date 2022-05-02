; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-fun start!1 () Bool)

(assert start!1)

(declare-fun b!15 () Bool)

(declare-fun e!22 () Bool)

(declare-fun error_value!0 () Bool)

(assert (=> b!15 (= e!22 error_value!0)))

(declare-fun b!16 () Bool)

(declare-fun e!20 () Bool)

(assert (=> b!16 (= e!20 e!22)))

(declare-fun b!20 () Bool)

(declare-datatypes ((Option!3 0) (tuple2!0 0) (Unit!0 0)) (((None!1) (Some!1 (v!71 tuple2!0))) ((tuple2!1 (_1!0 Unit!0) (_2!0 Bool))) ((Unit!1))))

(declare-fun lt!7 () Option!3)

(declare-fun Unit!2 () Unit!0)

(assert (=> b!16 (= b!20 (ite ((_ is Some!1) lt!7) (= (_1!0 (v!71 lt!7)) Unit!2) false))))

(assert (=> b!16 (or (not b!20) (not b!15))))

(assert (=> b!16 (or b!20 b!15)))

(declare-datatypes ((tuple3!0 0)) (((tuple3!1 (_1!1 (_ BitVec 32)) (_2!1 Bool) (_3!0 Unit!0)))))

(declare-fun unapply!2 (tuple3!0) Option!3)

(declare-fun Unit!3 () Unit!0)

(assert (=> b!16 (= lt!7 (unapply!2 (tuple3!1 #x0000002A false Unit!3)))))

(declare-fun b!17 () Bool)

(declare-fun e!21 () Bool)

(assert (=> b!17 e!21))

(declare-fun b!18 () Bool)

(declare-fun Unit!4 () Unit!0)

(assert (=> b!18 (= e!20 (_2!0 (v!71 (unapply!2 (tuple3!1 #x0000002A false Unit!4)))))))

(declare-fun lt!6 () Bool)

(assert (=> start!1 (not lt!6)))

(assert (=> start!1 (= lt!6 e!20)))

(assert (=> start!1 (= b!18 e!21)))

(assert (=> start!1 (or (not b!18) (not b!16))))

(assert (=> start!1 (or b!18 b!16)))

(declare-fun b!19 () Bool)

(assert (=> (and start!1 (not b!19)) (not e!21)))

(declare-fun lt!8 () Option!3)

(assert (=> start!1 (= b!19 (ite ((_ is Some!1) lt!8) true false))))

(declare-fun Unit!5 () Unit!0)

(assert (=> start!1 (= lt!8 (unapply!2 (tuple3!1 #x0000002A false Unit!5)))))

(assert (=> (and b!19 (not b!17)) (not e!21)))

(declare-fun Unit!6 () Unit!0)

(assert (=> b!19 (= b!17 (_2!0 (v!71 (unapply!2 (tuple3!1 #x0000002A false Unit!6)))))))

(declare-fun Unit!7 () Unit!0)

(assert (=> b!20 (= e!22 (_2!0 (v!71 (unapply!2 (tuple3!1 #x0000002A false Unit!7)))))))

(push 1)

(assert (and (and (and (and (not b!19) (not start!1)) (not b!20)) (not b!18)) (not b!16)))

(check-sat)

(pop 1)

(push 1)

(assert true)

(check-sat)

(pop 1)

(declare-fun d!1 () Bool)

(declare-fun e!25 () Bool)

(assert (=> d!1 e!25))

(declare-fun b!23 () Bool)

(assert (=> (and d!1 (not b!23)) (not e!25)))

(declare-fun Unit!8 () Unit!0)

(declare-fun Unit!9 () Unit!0)

(declare-fun Unit!10 () Unit!0)

(declare-fun Unit!11 () Unit!0)

(assert (=> d!1 (= b!23 (= (unapply!2 (tuple3!1 #x0000002A false Unit!8)) (ite (= (_1!1 (tuple3!1 #x0000002A false Unit!9)) #x00000000) None!1 (Some!1 (tuple2!1 (_3!0 (tuple3!1 #x0000002A false Unit!10)) (_2!1 (tuple3!1 #x0000002A false Unit!11)))))))))

(assert (=> b!23 (= e!25 true)))

(assert (=> b!18 d!1))

(assert (=> start!1 d!1))

(assert (=> b!16 d!1))

(assert (=> b!20 d!1))

(assert (=> b!19 d!1))

(push 1)

(assert true)

(check-sat)

(pop 1)

