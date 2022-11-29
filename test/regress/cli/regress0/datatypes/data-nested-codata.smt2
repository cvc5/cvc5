; EXPECT: sat
(set-logic QF_DTLIA)
(set-info :status sat)

(declare-datatype List ((cons (head Int) (tail List)) (nil)))

(declare-codatatype Stream ((mkStream (shead List) (stail Stream))))


(declare-fun x () Stream)
(assert (not ((_ is nil) (shead x))))
(assert (not ((_ is nil) (tail (shead x)))))
(declare-fun y () Stream)
(assert (not ((_ is nil) (shead y))))
(assert (not ((_ is nil) (tail (shead y)))))
(declare-fun z () Stream)
(assert (not ((_ is nil) (shead z))))
(assert (not ((_ is nil) (tail (shead z)))))
(assert (distinct x y z))

(check-sat)
