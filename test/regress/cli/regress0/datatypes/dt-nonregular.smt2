; SCRUBBER: grep -o "Cannot handle datatype [A-Z] that is not simply regular"
; EXPECT: Cannot handle datatype N that is not simply regular
; EXIT: 1
(set-logic ALL)
(declare-datatype Option (par (X) ((none) (some (val X)))))
(declare-datatype N (par (X) ((nil) (cons (hd X) (tl (N (Option X)))))))
(declare-const x (N Int))
(assert ((_ is cons) x))
(assert (= (tl x) (as nil (N (Option Int)))))
(assert (not (= x (cons (hd x) (as nil (N (Option Int)))))))
(check-sat)
