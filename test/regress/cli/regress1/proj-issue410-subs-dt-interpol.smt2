; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(set-option :produce-interpolants true)
(declare-sort _u0 0)
(declare-datatype _dt1
  ((_cons16 (_sel11 _u0))))
(declare-datatype _dt17
  ((_cons23 (_sel22 _dt1))))
(declare-const _x41 _dt1)
(declare-const _x68 _dt17)
(assert (= ((_ update _sel22) _x68 _x41) _x68))
(get-interpolant A (= ((_ update _sel22) _x68 _x41) _x68))
