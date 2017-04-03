% SCRUBBER: sed -e 's/The fact in question: .*$/The fact in question: TERM/'
% EXPECT: (error "A non-linear fact was asserted to arithmetic in a linear logic.
% EXPECT: The fact in question: TERM
% EXPECT: ")
% EXIT: 1
(benchmark reject_nonlinear
:logic QF_LRA
:extrafuns ((n Real))
:status unknown
:formula
(= (/ n n) 1)
)
