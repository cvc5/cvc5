(benchmark SEQ032_size2.smt
:source {
CADE ATP System competition. See http://www.cs.miami.edu/~tptp/CASC
 for more information. 

This benchmark was obtained by trying to find a finite model of a first-order 
formula (Albert Oliveras).
}
:status unsat
:category { crafted }
:difficulty { 0 }
:logic QF_UF
:extrafuns ((c3 U))
:extrafuns ((f1 U U U))
:extrafuns ((c2 U))
:extrafuns ((f4 U U))
:extrafuns ((c_0 U))
:extrafuns ((c_1 U))
:formula 
( and 
( distinct c_0 c_1 )(= (f1 (f1 (f1 c3 c_0) c_0) c_0) (f1 c_0 (f1 c_0 c_0))) (= (f1 (f1 (f1 c3 c_0) c_0) c_1) (f1 c_0 (f1 c_0 c_1))) (= (f1 (f1 (f1 c3 c_0) c_1) c_0) (f1 c_1 (f1 c_0 c_0))) (= (f1 (f1 (f1 c3 c_0) c_1) c_1) (f1 c_1 (f1 c_0 c_1))) (= (f1 (f1 (f1 c3 c_1) c_0) c_0) (f1 c_0 (f1 c_1 c_0))) (= (f1 (f1 (f1 c3 c_1) c_0) c_1) (f1 c_0 (f1 c_1 c_1))) (= (f1 (f1 (f1 c3 c_1) c_1) c_0) (f1 c_1 (f1 c_1 c_0))) (= (f1 (f1 (f1 c3 c_1) c_1) c_1) (f1 c_1 (f1 c_1 c_1))) (= (f1 (f1 c2 c_0) c_0) (f1 c_0 (f1 c_0 c_0))) (= (f1 (f1 c2 c_0) c_1) (f1 c_0 (f1 c_1 c_1))) (= (f1 (f1 c2 c_1) c_0) (f1 c_1 (f1 c_0 c_0))) (= (f1 (f1 c2 c_1) c_1) (f1 c_1 (f1 c_1 c_1))) (not (= (f1 c_0 (f4 c_0)) (f1 (f4 c_0) (f1 c_0 (f4 c_0))))) (not (= (f1 c_1 (f4 c_1)) (f1 (f4 c_1) (f1 c_1 (f4 c_1))))) (or (= (f1 c_0 c_0) c_0)(= (f1 c_0 c_0) c_1))(or (= (f1 c_0 c_1) c_0)(= (f1 c_0 c_1) c_1))(or (= (f1 c_1 c_0) c_0)(= (f1 c_1 c_0) c_1))(or (= (f1 c_1 c_1) c_0)(= (f1 c_1 c_1) c_1))(or (= (f4 c_0) c_0)(= (f4 c_0) c_1))(or (= (f4 c_1) c_0)(= (f4 c_1) c_1))(or (= c3 c_0)(= c3 c_1))(or (= c2 c_0)(= c2 c_1))))
