(set-logic QF_UFDTLIA)

; declaring a List datatype and defining List terms
(declare-datatype List ((cons (head Int) (tail List)) (nil)))

(define-fun t () List (cons 0 nil))
(define-fun t2 () Int (head t))

; declaring a parameterized datatype. We need the general
; declare-datatypes command since the singular version is a macro for
; the (declare-datatypes ((<type> 0)) <declaration>)
(declare-datatypes ((ParList 1))
  ((par (T) ((cons (parHead T) (parTail (ParList T))) (nil)))))

(define-sort ParListInt () (ParList Int))
(declare-const a ParListInt)
(define-fun aHead () Int (parHead a))

(assert (< aHead 50))
(check-sat)
