; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(check-sat-assuming ( (not (= #b0000111101010000 #b0000111101010000)) ))
(check-sat-assuming ( (not (= (concat #b01 #b0) #b010)) ))
(check-sat-assuming ( (not (= ((_ extract 3 1) #b0011) #b001)) ))
(check-sat-assuming ( (not (= (concat #b0011 #b000) #b0011000)) ))
(check-sat-assuming ( (not (= (concat #b000 ((_ extract 3 3) #b1000)) #b0001)) ))
(check-sat-assuming ( (not (= ((_ sign_extend 2) #b100) #b11100)) ))
(check-sat-assuming ( (not (= ((_ zero_extend 3) #b1) #b0001)) ))
(check-sat-assuming ( (not (= ((_ repeat 3) #b10) #b101010)) ))
(check-sat-assuming ( (not (= ((_ rotate_left 1) #b101) #b011)) ))
(check-sat-assuming ( (not (= ((_ rotate_right 1) #b101) #b110)) ))
