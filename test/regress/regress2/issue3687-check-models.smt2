; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic QF_ABV)
(declare-fun c () (_ BitVec 32))
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun b () (_ BitVec 32))
(assert (let ((a!1 (bvxnor (concat #x000000 (select a (bvadd c #x00000001))) #x00000008))
      (a!3 (bvsdiv (concat #x000000 (select a (bvadd c #x00000002))) #x00000010))
      (a!4 (bvudiv (concat #x000000 (select a (bvashr c #x00000003)))
                   #x00000018))
      (a!5 (select a
                   (bvxor (bvsub (bvnand c #x00000004) #x00000004) #x00000000)))
      (a!6 (select a
                   (bvsdiv (bvsub (bvnand c #x00000004) #x00000004) #x00000001)))
      (a!7 (select a
                   (bvadd (bvsub (bvnand c #x00000004) #x00000004) #x00000002)))
      (a!9 (store a
                  (bvashr (bvurem (bvnand c #x00000004) #x00000004) #x00000001)
                  ((_ extract 7 0) (bvxnor b #x00000008))))
      (a!11 (bvnand (bvurem (bvsub (bvnand c #x00000004) #x00000004) #x00000004)
                    #x00000008)))
(let ((a!2 (bvnor (concat #x000000 (select a (bvsmod c #x00000000))) a!1))
      (a!8 (bvlshr (bvor (concat #x000000 a!5)
                         (bvmul (concat #x000000 a!6) #x00000008))
                   (bvand (concat #x000000 a!7) #x00000010)))
      (a!10 (store a!9
                   (bvshl (bvurem (bvnand c #x00000004) #x00000004) #x00000000)
                   ((_ extract 7 0) b)))
      (a!12 (bvsub (concat #x000000 (select a (bvashr a!11 #x00000001)))
                   #x00000008))
      (a!14 (bvxnor (concat #x000000 (select a (bvxnor a!11 #x00000002)))
                    #x00000010))
      (a!15 (bvxor (concat #x000000 (select a (bvsub a!11 #x00000003)))
                   #x00000018)))
(let ((a!13 (bvor (concat #x000000 (select a (bvmul a!11 #x00000000))) a!12)))
(let ((a!16 ((_ extract 7 0)
              (bvmul (bvurem (bvurem a!13 a!14) a!15) #x00000018)))
      (a!17 ((_ extract 7 0) (bvor (bvurem (bvurem a!13 a!14) a!15) #x00000010)))
      (a!18 ((_ extract 7 0)
              (bvnor (bvurem (bvurem a!13 a!14) a!15) #x00000008))))
(let ((a!19 (store (store (store (store a!10 #x08053e77 a!16) #x08053e76 a!17)
                          #x08053e75
                          a!18)
                   #x08053e74
                   ((_ extract 7 0) (bvurem (bvurem a!13 a!14) a!15)))))
(let ((a!20 (select a!19
                    (bvadd (bvsub (bvnand c #x00000004) #x00000004) #x00000003))))
(let ((a!21 (distinct (bvsdiv (bvsmod a!2 a!3) a!4)
                      (bvshl a!8 (bvshl (concat #x000000 a!20) #x00000018)))))
  (= #b1 (bvashr (ite (or a!21) #b1 #b0) #b1))))))))))
(check-sat)
