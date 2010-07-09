(benchmark PEQ012_size3_segsat.smt
:source {

CADE ATP System competition. See http://www.cs.miami.edu/~tptp/CASC
 for more information. 

This benchmark was obtained by trying to find a finite model of a first-order 
formula (Albert Oliveras).

Original source is QF_UF/PEQ/PEQ012_size3.smt
Mucked up by Tim
}
:status sat
:category { crafted }
:difficulty { 0 }
:logic QF_UF

:extrafuns ((f1 U U U))
:extrafuns ((c6 U))
:extrafuns ((c3 U))
:extrafuns ((c7 U))
:extrafuns ((c5 U))
:extrafuns ((c2 U))
:extrafuns ((c4 U))
:extrafuns ((c8 U))
:extrafuns ((c9 U))
:extrafuns ((c_0 U))
:extrafuns ((c_1 U))
:extrafuns ((c_2 U))
:formula 
( and 
  (not (= c_0 c_1))
  (not (= c_0 c_2))
  (not (= c_1 c_2))
  (or (not (= (f1 c_0 c_1) (f1 c_0 c_1))) (= c_1 c_1) )
  (or (not (= (f1 c_0 c_2) (f1 c_0 c_0))) (= c_2 c_0) )
  (or (not (= (f1 c_0 c_2) (f1 c_0 c_2))) (= c_2 c_2) )
  (or (not (= (f1 c_1 c_0) (f1 c_1 c_0))) (= c_0 c_0) )
  (or (not (= (f1 c_1 c_0) (f1 c_1 c_2))) (= c_0 c_2) )
  (or (not (= (f1 c_1 c_1) (f1 c_1 c_0))) (= c_1 c_0) )
  (= (f1 (f1 c_0 c_0) c_0) (f1 c_0 (f1 c_0 c_0)))
  (= (f1 (f1 c_0 c_0) c_2) (f1 c_0 (f1 c_0 c_2)))
  (= (f1 (f1 c_0 c_1) c_1) (f1 c_0 (f1 c_1 c_1)))
  (= (f1 (f1 c_0 c_1) c_2) (f1 c_0 (f1 c_1 c_2)))
  (= (f1 (f1 c_2 c_1) c_2) (f1 c_2 (f1 c_1 c_2)))
  (= (f1 (f1 c_2 c_2) c_0) (f1 c_2 (f1 c_2 c_0)))
  (= (f1 (f1 c_2 c_2) c_1) (f1 c_2 (f1 c_2 c_1)))
  (= (f1 c_0 (f1 c_2 (f1 c_2 (f1 c_2 c_0)))) (f1 c_2 (f1 c_0 (f1 c_2 (f1 c_0 c_2)))))
  (= (f1 c2 c8) (f1 c4 c9))
  (not (= (f1 c6 c8) (f1 c7 c9)))
  (or (= (f1 c_0 c_0) c_0)(= (f1 c_0 c_0) c_1)(= (f1 c_0 c_0) c_2))
  (or (= (f1 c_0 c_1) c_0)(= (f1 c_0 c_1) c_1)(= (f1 c_0 c_1) c_2))
  (or (= (f1 c_1 c_0) c_0)(= (f1 c_1 c_0) c_1)(= (f1 c_1 c_0) c_2))
  (or (= (f1 c_1 c_1) c_0)(= (f1 c_1 c_1) c_1)(= (f1 c_1 c_1) c_2))
  (or (= (f1 c_1 c_2) c_0)(= (f1 c_1 c_2) c_1)(= (f1 c_1 c_2) c_2))
  (or (= (f1 c_2 c_0) c_0)(= (f1 c_2 c_0) c_1)(= (f1 c_2 c_0) c_2))
  (or (= (f1 c_2 c_1) c_0)(= (f1 c_2 c_1) c_1)(= (f1 c_2 c_1) c_2))
  (or (= (f1 c_2 c_2) c_0)(= (f1 c_2 c_2) c_1)(= (f1 c_2 c_2) c_2))
  (or (= c6 c_0)(= c6 c_1)(= c6 c_2))
  (or (= c3 c_0)(= c3 c_1)(= c3 c_2))
  (or (= c7 c_0)(= c7 c_1)(= c7 c_2))
  (or (= c5 c_0)(= c5 c_1)(= c5 c_2))
  (or (= c2 c_0)(= c2 c_1)(= c2 c_2))
  (or (= c4 c_0)(= c4 c_1)(= c4 c_2))
  (or (= c8 c_0)(= c8 c_1)(= c8 c_2))
  (or (= c9 c_0)(= c9 c_1)(= c9 c_2))
))
