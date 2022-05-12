; COMMAND-LINE: --ext-rew-prep=use
; EXPECT: sat
(set-logic QF_BV)
(declare-fun a () (_ BitVec 4))
(assert (let ((a!1 ((_ sign_extend 3)
             (ite (bvult ((_ sign_extend 15) #b0) #x2b7e) #b1 #b0)))
      (a!2 ((_ zero_extend 15)
             (ite (distinct #x2b7e ((_ sign_extend 12) a)) #b1 #b0)))
      (a!4 (bvsgt (bvlshr (bvadd #x2b7e ((_ sign_extend 12) a))
                          ((_ sign_extend 12) a))
                  ((_ zero_extend 12) a)))
      (a!5 (bvugt (ite (bvult ((_ sign_extend 15) #b0) #x2b7e) #b1 #b0) #b0))
      (a!6 (bvugt (bvlshr (bvadd #x2b7e ((_ sign_extend 12) a))
                          ((_ sign_extend 12) a))
                  #x2b7e)))
(let ((a!3 (bvslt a!2
                  (bvlshr (bvadd #x2b7e ((_ sign_extend 12) a))
                          ((_ sign_extend 12) a))))
      (a!7 (xor (ite a!4 a!5 a!4)
                a!6
                (= (bvxnor #x2b7e ((_ zero_extend 12) a))
                   (bvadd #x2b7e ((_ sign_extend 12) a))))))
  (ite (bvule a!1 a) a!3 a!7))))
(check-sat)
