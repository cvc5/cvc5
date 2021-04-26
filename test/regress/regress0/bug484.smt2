; COMMAND-LINE:
; EXPECT: sat

; Preamble  --------------
(set-logic ALL)
(set-info :status sat)
(declare-datatypes ((UNIT 0)) (((Unit))))
(declare-datatypes ((BOOL 0)) (((Truth) (Falsity))))

; Decls     --------------
(declare-sort A 0)
(declare-sort B 0)
(declare-sort C 0)
(declare-sort D 0)
(declare-datatypes ((E 0)) (((one) (two) (three))))
(declare-datatypes ((F 0)) (((four) (five) (six))))
(declare-datatypes ((G 0)) (((c_G (seven BOOL)))))

(declare-datatypes ((H 0))
  ((
    (c_H
      (foo1 BOOL)
      (foo2 A)
      (foo3 B)
      (foo4 B)
      (foo5 Int)
    )
  ))
)

(declare-datatypes ((I 0))
  ((
    (c_I
      (bar1 E)
      (bar2 Int)
      (bar3 Int)
      (bar4 A)
    )
  ))
)

(declare-datatypes ((J 0))
  ((
    (c_J
      (f1 BOOL)
      (f2 Int)
      (f3 Int)
      (f4 Int)
      (f5 I)
      (f6 B)
      (f7 C)
    )
  ))
)

(declare-datatypes ((K 0))
  ((
    (c_K
      (g1 BOOL)
      (g2 F)
      (g3 A)
      (g4 BOOL)
    )
  ))
)

; Var Decls --------------
(declare-fun s1 () (Array A J))
(declare-fun s2 () (Array A J))
(declare-fun e1 () (Array A K))
(declare-fun e2 () (Array A K))
(declare-fun x  () A)
(declare-fun y  () A)
(declare-fun foo (A) A)
(declare-fun bar (A) C)


; Asserts   --------------
(assert
  (not
    (=
      (ite
        (=>
          (= y (g3 (select e1 x)))
          (=>
            (= s2
               (store
                 s1
                 y
                 (let ((z (select s1 y)))
                   (c_J
                     (f1 z)
                     (f2 z)
                     (- (f3 (select s1 y)) 1)
                     (f4 z)
                     (f5 z)
                     (f6 z)
                     (f7 z)
                   )
                 )
               )
            )
            (forall ((s A)) (= (g3 (select e2 s)) s))
          )
        )
       Truth
       Falsity
      )
      Truth
    )
  )
)

(check-sat)
