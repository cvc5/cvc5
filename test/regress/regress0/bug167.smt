(benchmark tta_startup
:logic QF_LRA
:extrafuns ((x_62 Real))
:extrafuns ((x_63 Real))
:extrafuns ((x_65 Real))
:extrafuns ((x_22 Real))
:extrafuns ((x_21 Real))
:extrafuns ((x_53 Real))
:extrafuns ((x_54 Real))
:status sat
:formula
(and
 (= x_54 (ite (= 2 x_53) x_22 x_21))
 (or (= 4 x_65) (= 3 x_65) (= 2 x_65) (= 1 x_65))
 (or (= 4 x_63) (= 1 x_63))
 (<= x_62 4)
 (or (= 1 x_62) (= 4 x_62))
)
)
