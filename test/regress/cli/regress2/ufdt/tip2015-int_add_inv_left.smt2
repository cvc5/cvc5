; COMMAND-LINE: --dt-stc-ind --conjecture-gen
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: cpc
; DISABLE-TESTER: lfsc
; EXPECT: unsat
(set-logic UFDT)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype Integer ((P (proj1-P Nat)) (N (proj1-N Nat))))
(define-fun zero2 () Integer 
  (P zero))
(define-fun-rec plus ((x Nat) (y Nat)) Nat
  (match x
    (((zero) y)
     ((succ px) (succ (plus px y))))))
(define-fun-rec neg ((x Integer)) Integer
  (match x
    (((N absx) (P (plus (succ zero) absx)))
     ((P absx) (match absx
                 (((zero) (P zero))
                  ((succ pabsx) (N pabsx))))))))
(define-fun-rec minus2 ((x Nat) (y Nat)) Integer
  (let ((fail (match y
                (((succ py) (match x
                              (((succ px) (minus2 px py))
                               ((zero) (N py)))))
                 ((zero) (P x))))))
    (match x
      (((succ px) fail)
       ((zero) (match y
                 (((succ py) fail)
                  ((zero) (P zero)))))))))
(define-fun plus2 ((x Integer) (y Integer)) Integer
  (match x
    (((N absx) (match y
                 (((N absy) (N (plus (plus (succ zero) absx) absy)))
                  ((P absy) (minus2 absy (plus (succ zero) absx))))))
     ((P absx) (match y
                 (((N absy) (minus2 absx (plus (succ zero) absy)))
                  ((P absy) (P (plus absx absy)))))))))
(assert
 (not
  (forall ((x Integer))
    (= (plus2 (neg x) x) zero2))))
(check-sat)
