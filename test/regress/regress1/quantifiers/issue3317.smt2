; COMMAND-LINE: --fmf-fun-rlv --no-check-models
; EXPECT: sat
(set-info :smt-lib-version 2.5)
(set-option :produce-models true)
(set-logic ALL)
(declare-datatypes () ((a0(c0$0(c0$0$0 a4)(c0$0$1 Bool)(c0$0$2 a4)(c0$0$3 Int)(c0$0$4 a5)(c0$0$5 a7)(c0$0$6 a7)))(a1(c1$0(c1$0$0 Bool)(c1$0$1 Bool)(c1$0$2 Int))(c1$1)(c1$2(c1$2$0 a3)(c1$2$1 a5)(c1$2$2 a1)(c1$2$3 a7))(c1$3)(c1$4)(c1$5)(c1$6)(c1$7)(c1$8)(c1$9(c1$9$0 a4))(c1$a))(a2(c2$0(c2$0$0 String)(c2$0$1 a4)(c2$0$2 a0)(c2$0$3 Bool)(c2$0$4 a5)(c2$0$5 a4))(c2$1)(c2$2)(c2$3)(c2$4)(c2$5))(a3(c3$0)(c3$1)(c3$2)(c3$3)(c3$4(c3$4$0 a6))(c3$5)(c3$6)(c3$7))(a4(c4$0)(c4$1(c4$1$0 a3))(c4$2(c4$2$0 a5))(c4$3)(c4$4)(c4$5(c4$5$0 String)(c4$5$1 a4))(c4$6)(c4$7)(c4$8)(c4$9(c4$9$0 String))(c4$a)(c4$b))(a5(c5$0)(c5$1(c5$1$0 a7)(c5$1$1 a0)(c5$1$2 Bool)(c5$1$3 a1)(c5$1$4 a3)(c5$1$5 a7)(c5$1$6 Int)(c5$1$7 Bool))(c5$2)(c5$3)(c5$4)(c5$5)(c5$6)(c5$7))(a6(c6$0(c6$0$0 Bool))(c6$1)(c6$2(c6$2$0 Bool)(c6$2$1 a3)(c6$2$2 Int)(c6$2$3 a3)(c6$2$4 a6)(c6$2$5 a7)(c6$2$6 a0)(c6$2$7 a6)))(a7(c7$0)(c7$1)(c7$2(c7$2$0 a6))(c7$3)(c7$4)(c7$5(c7$5$0 a2)(c7$5$1 a2)(c7$5$2 Int)(c7$5$3 a6))(c7$6)(c7$7))))
(define-funs-rec ( (f9((v38 Int)(v39 a2)(v3a a5)(v3b a0)(v3c a7)(v3d a3))Bool)
                   (f8((v33 String)(v34 Int)(v35 a1)(v36 a7)(v37 a4))a6)
                   (f7((v29 a1)(v2a Bool)(v2b a3)(v2c String)(v2d Bool)(v2e String)(v2f a7)(v30 a5)(v31 a2)(v32 a2))Int)
                   (f6((v20 a2)(v21 a3)(v22 Int)(v23 a3)(v24 a3)(v25 a1)(v26 a0)(v27 a4)(v28 a2))String)
                   (f5((v1b a0)(v1c String)(v1d a5)(v1e a7)(v1f a2))Int)
                   (f4((v13 a0)(v14 a5)(v15 a7)(v16 a6)(v17 Bool)(v18 a1)(v19 a2)(v1a a7))a5)
                   (f3((vb a6)(vc a2)(vd String)(ve a4)(vf Bool)(v10 a7)(v11 String)(v12 a6))a5)
                   (f2((v9 a5)(va a2))a7)
                   (f1((v0 a6)(v1 a2)(v2 a3)(v3 a6)(v4 Int)(v5 a1)(v6 a1)(v7 a0)(v8 Int))a0)
                   (f0()Int)
                 )
                 ( false 
                   (c6$0 false) 
                   (+ 3 (- (str.len v2c))) 
                   "\xca\x85C\xe1\xc8(\x092\x84" 
                   0 
                   c5$2 
                   c5$5 
                   c7$3 
                   (c0$0 c4$b false c4$8 0 c5$3 c7$1 c7$3) 
                   1)
                 )
(check-sat)
