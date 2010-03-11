
(benchmark euf_simp4.smt
:status unsat
:logic QF_UF
:category { crafted }

:extrafuns ((x U))
:extrafuns ((y U))
:extrafuns ((z U))
:extrafuns ((f U U))
:extrafuns ((g U U))
:extrafuns ((H U U U))
:extrafuns ((J U U U))



:formula
(and
 (= (H x y) (H y x))
 (or (= x (J z y)) (= y (J z y)))
 (= (J z y) (f x))
 (or (= x (f x)) (not (= y (f x))) )
 (or (not (= x (f x))) (not (= (H x (f x)) (H (f x) x) )) )
 )
)