; COMMAND-LINE: --dt-stc-ind
; EXPECT: unsat
(set-logic UFDT)
; natural numbers
(declare-datatype Nat ((succ (pred Nat)) (zero)))

(declare-fun less (Nat Nat) Bool)
(assert (not (less zero zero)))
(assert (forall ((x Nat)) (less zero (succ x))))
(assert (forall ((x Nat) (y Nat)) (= (less (succ x) (succ y)) (less x y))))

(define-fun leq ((x Nat) (y Nat)) Bool (or (= x y) (less x y)))

(declare-fun plus (Nat Nat) Nat)
(assert (forall ((n Nat)) (= (plus zero n) n)))
(assert (forall ((n Nat) (m Nat)) (= (plus (succ n) m) (succ (plus n m)))))

; lists      
(declare-datatype Lst ((cons (head Nat) (tail Lst)) (nil)))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun len (Lst) Nat)
(assert (= (len nil) zero))
(assert (forall ((x Nat) (y Lst)) (= (len (cons x y)) (succ (len y)))))

(declare-fun butlast (Lst) Lst)
(assert (= (butlast nil) nil))
(assert (forall ((x Nat) (y Lst)) (= (butlast (cons x y)) (ite (= y nil) nil (cons x (butlast y))))))

(declare-fun qreva (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (qreva nil x) x)))
(assert (forall ((x Lst) (y Lst) (z Nat)) (= (qreva (cons z x) y) (qreva x (cons z y)))))

(declare-fun qrev (Lst) Lst)
(assert (forall ((x Lst)) (= (qrev x) (qreva x nil))))

; queues
(declare-datatype Queue ((queue (front Lst) (back Lst))))

(declare-fun queue-to-lst (Queue) Lst)
(assert (forall ((x Lst) (y Lst)) (= (queue-to-lst (queue x y)) (append x (qrev y)))))

(declare-fun qlen (Queue) Nat)
(assert (forall ((x Lst) (y Lst)) (= (qlen (queue x y)) (plus (len x) (len y)))))

(declare-fun isAmortized (Queue) Bool)
(assert (forall ((x Lst) (y Lst)) (= (isAmortized (queue x y)) (leq (len y) (len x)))))

(declare-fun isEmpty (Queue) Bool)
(assert (forall ((x Lst) (y Lst)) (= (isEmpty (queue x y)) (and (= x nil) (= y nil)))))

(declare-fun amortizeQueue (Lst Lst) Queue)
(assert (forall ((x Lst) (y Lst)) (= (amortizeQueue x y) (ite (leq (len y) (len x)) (queue x y) (queue (append x (qrev y)) nil)))))

(declare-fun enqueue (Queue Nat) Queue)
(assert (forall ((x Lst) (y Lst) (n Nat)) (= (enqueue (queue x y) n) (amortizeQueue x (cons n y)))))

(declare-fun qpop (Queue) Queue)
(assert (forall ((x Lst) (y Lst) (n Nat)) (= (qpop (queue x (cons n y))) (queue x y))))
(assert (forall ((x Lst)) (= (qpop (queue x nil)) (queue (butlast x) nil))))

; proven
(assert 
(forall ((x Lst) (y Lst)) (= (len (append x y)) (plus (len x) (len y))))  ; G-amortize-queue-1 
)
(assert 
(forall ((x Lst) (y Lst)) (= (len (qreva x y)) (plus (len x) (len y)))) ; G-amortize-queue-2 
)

; conjecture
(assert (not 
(forall ((x Lst)) (= (len (qrev x)) (len x))) ; G-amortize-queue-3 
))
(check-sat)
