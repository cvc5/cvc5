; initialize_defs
; PROPERTY DEFGEN
(set-logic QF_UFNIA)
(set-info :status unsat)
(declare-fun _base () Int)
(declare-fun _n () Int)
(assert (>= _n 0))

; maxdepth = 1
(declare-fun ___z2z___ (Int) Bool)
			; KP_START ;  INPUT,STATE(1,)/102
(declare-fun ___z3z___ (Int) Bool)
			; KP_CLEAR ;  INPUT,STATE(1,)/103
(declare-fun ___z4z___ (Int) Bool)
			; KP_0 ;  INPUT,STATE(1,)/104
(declare-fun ___z5z___ (Int) Bool)
			; KP_1 ;  INPUT,STATE(1,)/105
(declare-fun ___z6z___ (Int) Bool)
			; KP_2 ;  INPUT,STATE(1,)/106
(declare-fun ___z7z___ (Int) Bool)
			; KP_3 ;  INPUT,STATE(1,)/107
(declare-fun ___z8z___ (Int) Bool)
			; KP_4 ;  INPUT,STATE(1,)/108
(declare-fun ___z9z___ (Int) Bool)
			; KP_5 ;  INPUT,STATE(1,)/109
(declare-fun ___z10z___ (Int) Bool)
			; KP_6 ;  INPUT,STATE(1,)/110
(declare-fun ___z11z___ (Int) Bool)
			; KP_7 ;  INPUT,STATE(1,)/111
(declare-fun ___z12z___ (Int) Bool)
			; KP_8 ;  INPUT,STATE(1,)/112
(declare-fun ___z13z___ (Int) Bool)
			; KP_9 ;  INPUT,STATE(1,)/113
(declare-fun ___z14z___ (Int) Bool)
			; DOOR_CLOSED ;  INPUT/114
(declare-fun ___z15z___ (Int) Bool)
			; OK ;  OUTPUT/115
(declare-fun ___z19z___ (Int) Bool)
			; V20_START_PRESSED ;  LOCAL/119
(declare-fun ___z20z___ (Int) Bool)
			; V21_CLEAR_PRESSED ;  LOCAL/120
(declare-fun ___z21z___ (Int) Int)
			; V25_STEPS_TO_COOK ;  LOCAL,STATE(1,)/121
(declare-fun ___z22z___ (Int) Bool)
			; V26_rlt_condact_resetmicrowave_microwave_KEYPAD_PROCESSING_rlt_clock ;  LOCAL,STATE(1,)/122
(declare-fun ___z23z___ (Int) Bool)
			; V37_rlt_condact_resetmicrowave_microwave_KEYPAD_PROCESSING_rlt_init_step ;  LOCAL,STATE(1,)/123
(declare-fun ___z24z___ (Int) Int)
			; V38_microwave_microwave_KEYPAD_PROCESSING_DISPLAY_LEFT_DIGIT_DIGIT_TO_DISPLAY ;  LOCAL,STATE(1,)/124
(declare-fun ___z25z___ (Int) Int)
			; V39_microwave_microwave_KEYPAD_PROCESSING_DISPLAY_MIDDLE_DIGIT_DIGIT_TO_DISPLAY ;  LOCAL,STATE(1,)/125
(declare-fun ___z26z___ (Int) Int)
			; V40_microwave_microwave_KEYPAD_PROCESSING_DISPLAY_RIGHT_DIGIT_DIGIT_TO_DISPLAY ;  LOCAL,STATE(1,)/126
(declare-fun ___z33z___ (Int) Int)
			; V47_chart_microwave_mode_logic_start ;  LOCAL/133
(declare-fun ___z34z___ (Int) Int)
			; V48_chart_microwave_mode_logic_clear_off ;  LOCAL/134
(declare-fun ___z35z___ (Int) Int)
			; V49_chart_microwave_mode_logic_door_closed ;  LOCAL/135
(declare-fun ___z36z___ (Int) Bool)
			; V51_rlt_eval_microwave_mode_logic_ON_rlt_fired_1 ;  LOCAL/136
(declare-fun ___z37z___ (Int) Int)
			; V52_rlt_eval_microwave_mode_logic_ON_rlt_state_1_states___root ;  LOCAL/137
(declare-fun ___z38z___ (Int) Int)
			; V53_rlt_eval_microwave_mode_logic_ON_rlt_state_2_states___root ;  LOCAL/138
(declare-fun ___z39z___ (Int) Bool)
			; V54_rlt_eval_microwave_mode_logic_ON_rlt_fired_2 ;  LOCAL/139
(declare-fun ___z40z___ (Int) Bool)
			; V55_rlt_eval_microwave_mode_logic_ON_rlt_complete_1 ;  LOCAL/140
(declare-fun ___z41z___ (Int) Int)
			; V56_rlt_eval_microwave_mode_logic_ON_rlt_state_3_states___root ;  LOCAL/141
(declare-fun ___z42z___ (Int) Int)
			; V57_rlt_eval_microwave_mode_logic_ON_rlt_state_3_outports_mode ;  LOCAL/142
(declare-fun ___z43z___ (Int) Int)
			; V58_rlt_eval_microwave_mode_logic_ON_rlt_state_4_states___root ;  LOCAL/143
(declare-fun ___z44z___ (Int) Int)
			; V59_rlt_eval_microwave_mode_logic_ON_rlt_state_4_outports_mode ;  LOCAL/144
(declare-fun ___z45z___ (Int) Bool)
			; V60_rlt_eval_microwave_mode_logic_ON_rlt_fired_4 ;  LOCAL/145
(declare-fun ___z46z___ (Int) Bool)
			; V61_rlt_eval_microwave_mode_logic_ON_rlt_complete_2 ;  LOCAL/146
(declare-fun ___z47z___ (Int) Int)
			; V62_rlt_eval_microwave_mode_logic_ON_rlt_state_6_states___root ;  LOCAL/147
(declare-fun ___z48z___ (Int) Int)
			; V63_rlt_eval_microwave_mode_logic_ON_rlt_state_6_outports_steps_remaining ;  LOCAL/148
(declare-fun ___z49z___ (Int) Int)
			; V64_rlt_eval_microwave_mode_logic_ON_rlt_state_7_states___root ;  LOCAL/149
(declare-fun ___z50z___ (Int) Bool)
			; V65_rlt_eval_microwave_mode_logic_ON_rlt_fired_5 ;  LOCAL/150
(declare-fun ___z51z___ (Int) Int)
			; V66_rlt_eval_microwave_mode_logic_ON_rlt_state_8_outports_mode ;  LOCAL/151
(declare-fun ___z52z___ (Int) Int)
			; V67_rlt_eval_microwave_mode_logic_ON_rlt_state_9_states___root ;  LOCAL/152
(declare-fun ___z53z___ (Int) Int)
			; V68_rlt_eval_microwave_mode_logic_ON_rlt_state_10_states___root ;  LOCAL/153
(declare-fun ___z54z___ (Int) Bool)
			; V69_rlt_eval_microwave_mode_logic_ON_rlt_fired_6 ;  LOCAL/154
(declare-fun ___z55z___ (Int) Int)
			; V70_rlt_eval_microwave_mode_logic_ON_rlt_state_11_states___root ;  LOCAL/155
(declare-fun ___z56z___ (Int) Int)
			; V71_rlt_eval_microwave_mode_logic_ON_rlt_state_11_outports_mode ;  LOCAL/156
(declare-fun ___z57z___ (Int) Int)
			; V72_rlt_enter_microwave_mode_logic_ON_rlt_state_1_states___root ;  LOCAL/157
(declare-fun ___z58z___ (Int) Bool)
			; V73_rlt_enter_microwave_mode_logic_ON_rlt_fired_0 ;  LOCAL/158
(declare-fun ___z59z___ (Int) Bool)
			; V74_rlt_enter_microwave_mode_logic_ON_rlt_fired_1 ;  LOCAL/159
(declare-fun ___z60z___ (Int) Int)
			; V75_rlt_enter_microwave_mode_logic_ON_rlt_state_2_states___root ;  LOCAL/160
(declare-fun ___z61z___ (Int) Int)
			; V76_rlt_enter_microwave_mode_logic_ON_rlt_state_2_outports_mode ;  LOCAL/161
(declare-fun ___z62z___ (Int) Bool)
			; V77_rlt_enter_microwave_mode_logic_ON_rlt_fired_2 ;  LOCAL/162
(declare-fun ___z63z___ (Int) Int)
			; V78_rlt_enter_microwave_mode_logic_ON_rlt_state_4_states___root ;  LOCAL/163
(declare-fun ___z64z___ (Int) Bool)
			; V79_rlt_eval_microwave_mode_logic_rlt_fired_0 ;  LOCAL/164
(declare-fun ___z65z___ (Int) Int)
			; V80_rlt_eval_microwave_mode_logic_rlt_state_1_outports_steps_remaining ;  LOCAL/165
(declare-fun ___z66z___ (Int) Bool)
			; V81_rlt_eval_microwave_mode_logic_rlt_fired_1 ;  LOCAL/166
(declare-fun ___z67z___ (Int) Int)
			; V82_rlt_eval_microwave_mode_logic_rlt_state_2_states___root ;  LOCAL/167
(declare-fun ___z68z___ (Int) Int)
			; V83_rlt_eval_microwave_mode_logic_rlt_state_3_states___root ;  LOCAL/168
(declare-fun ___z69z___ (Int) Int)
			; V84_rlt_eval_microwave_mode_logic_rlt_state_3_outports_mode ;  LOCAL/169
(declare-fun ___z70z___ (Int) Int)
			; V85_rlt_enter_microwave_mode_logic_rlt_state_2_states___root ;  LOCAL/170
(declare-fun ___z71z___ (Int) Bool)
			; V86_chart_microwave_mode_logic_rlt_evtInitStep ;  LOCAL,STATE(1,)/171
(declare-fun ___z72z___ (Int) Int)
			; V87_chart_microwave_mode_logic_begin_state_states___root ;  LOCAL/172
(declare-fun ___z73z___ (Int) Int)
			; V88_chart_microwave_mode_logic_begin_state_outports_mode ;  LOCAL/173
(declare-fun ___z74z___ (Int) Int)
			; V89_chart_microwave_mode_logic_begin_state_outports_steps_remaining ;  LOCAL/174
(declare-fun ___z75z___ (Int) Int)
			; V90_chart_microwave_mode_logic_final_state_states___root ;  LOCAL,STATE(1,)/175
(declare-fun ___z76z___ (Int) Int)
			; V92_chart_microwave_mode_logic_steps_remaining ;  LOCAL,STATE(1,)/176
(declare-fun ___z77z___ (Int) Int)
			; V93_microwave_microwave_TIME_ON_DISPLAY_SECONDS_TO_MINUTES__QUOTIENT ;  LOCAL/177
(declare-fun ___z80z___ (Int) Int)
			; V96_microwave_microwave_mode_logic_mode ;  LOCAL,STATE(1,)/180


; Generic definitions:
(define-fun DEF__172 ((_M Int)) Bool(= (___z72z___ _M) (ite (= _M _base) 0 (___z75z___ (- _M 1)))))
(define-fun DEF__173 ((_M Int)) Bool(= (___z73z___ _M) (ite (= _M _base) 0 (___z80z___ (- _M 1)))))
(define-fun DEF__174 ((_M Int)) Bool(= (___z74z___ _M) (ite (= _M _base) 0 (___z76z___ (- _M 1)))))
(define-fun DEF__175 ((_M Int)) Bool(= (___z75z___ _M) (ite (= (___z71z___ _M) true) (___z70z___ _M) (ite (= (and (not (___z66z___ _M)) (and (>= (___z68z___ _M) 1) (<= (___z68z___ _M) 3))) true) (ite (= (___z54z___ _M) true) (ite (= (not (= (___z55z___ _M) 3)) true) 3 (___z55z___ _M)) (___z55z___ _M)) (___z68z___ _M)))))
(define-fun DEF__133 ((_M Int)) Bool(= (___z33z___ _M) (ite (= (= (___z19z___ _M) false) true) 0 1)))
(define-fun DEF__176 ((_M Int)) Bool(= (___z76z___ _M) (ite (= (___z71z___ _M) true) (___z74z___ _M) (ite (= (and (not (___z66z___ _M)) (and (>= (___z68z___ _M) 1) (<= (___z68z___ _M) 3))) true) (ite (= (___z50z___ _M) true) (- (___z48z___ _M) 1) (___z48z___ _M)) (___z65z___ _M)))))
(define-fun DEF__134 ((_M Int)) Bool(= (___z34z___ _M) (ite (= (= (___z20z___ _M) false) true) 0 1)))
(define-fun DEF__177 ((_M Int)) Bool(= (___z77z___ _M) (div (div (___z76z___ _M) 1) 60)))
(define-fun DEF__135 ((_M Int)) Bool(= (___z35z___ _M) (ite (= (= (___z14z___ _M) false) true) 0 1)))
(define-fun DEF__136 ((_M Int)) Bool(= (___z36z___ _M) (and (and (= (___z68z___ _M) 2) (<= (___z65z___ _M) 0)) (= (___z68z___ _M) 2))))
(define-fun DEF__180 ((_M Int)) Bool(= (___z80z___ _M) (ite (= (___z71z___ _M) true) (ite (= (not (= (___z72z___ _M) 4)) true) 1 (___z73z___ _M)) (ite (= (and (not (___z66z___ _M)) (and (>= (___z68z___ _M) 1) (<= (___z68z___ _M) 3))) true) (ite (= (___z54z___ _M) true) (ite (= (not (= (___z55z___ _M) 3)) true) 3 (___z56z___ _M)) (___z56z___ _M)) (___z69z___ _M)))))
(define-fun DEF__137 ((_M Int)) Bool(= (___z37z___ _M) (ite (= (___z36z___ _M) true) (ite (= (and (>= (___z68z___ _M) 1) (<= (___z68z___ _M) 3)) true) 0 (___z68z___ _M)) (___z68z___ _M))))
(define-fun DEF__138 ((_M Int)) Bool(= (___z38z___ _M) (ite (= (___z36z___ _M) true) (ite (= (not (= (___z37z___ _M) 4)) true) 4 (___z37z___ _M)) (___z37z___ _M))))
(define-fun DEF__139 ((_M Int)) Bool(= (___z39z___ _M) (and (= (___z38z___ _M) 3) (and (and (ite (= (not (= (___z33z___ _M) 0)) true) true false) (ite (= (not (= (___z35z___ _M) 0)) true) true false)) (not (___z36z___ _M))))))
(define-fun DEF__140 ((_M Int)) Bool(= (___z40z___ _M) (or (___z39z___ _M) (___z36z___ _M))))
(define-fun DEF__141 ((_M Int)) Bool(= (___z41z___ _M) (ite (= (___z39z___ _M) true) (ite (= (___z38z___ _M) 3) 1 (___z38z___ _M)) (___z38z___ _M))))
(define-fun DEF__142 ((_M Int)) Bool(= (___z42z___ _M) (ite (= (___z36z___ _M) true) (ite (= (not (= (___z37z___ _M) 4)) true) 1 (___z69z___ _M)) (___z69z___ _M))))
(define-fun DEF__143 ((_M Int)) Bool(= (___z43z___ _M) (ite (= (___z39z___ _M) true) (ite (= (not (= (___z41z___ _M) 2)) true) 2 (___z41z___ _M)) (___z41z___ _M))))
(define-fun DEF__144 ((_M Int)) Bool(= (___z44z___ _M) (ite (= (___z39z___ _M) true) (ite (= (not (= (___z41z___ _M) 2)) true) 2 (___z42z___ _M)) (___z42z___ _M))))
(define-fun DEF__145 ((_M Int)) Bool(= (___z45z___ _M) (and (and (= (___z43z___ _M) 3) (and (ite (= (not (= (___z34z___ _M) 0)) true) true false) (not (___z40z___ _M)))) (and (= (___z43z___ _M) 3) (not (___z40z___ _M))))))
(define-fun DEF__146 ((_M Int)) Bool(= (___z46z___ _M) (or (___z45z___ _M) (___z40z___ _M))))
(define-fun DEF__147 ((_M Int)) Bool(= (___z47z___ _M) (ite (= (___z45z___ _M) true) (ite (= (and (>= (___z43z___ _M) 1) (<= (___z43z___ _M) 3)) true) 0 (___z43z___ _M)) (___z43z___ _M))))
(define-fun DEF__148 ((_M Int)) Bool(= (___z48z___ _M) (ite (= (___z45z___ _M) true) 0 (___z65z___ _M))))
(define-fun DEF__149 ((_M Int)) Bool(= (___z49z___ _M) (ite (= (___z45z___ _M) true) (ite (= (not (= (___z47z___ _M) 4)) true) 4 (___z47z___ _M)) (___z47z___ _M))))
(define-fun DEF__150 ((_M Int)) Bool(= (___z50z___ _M) (and (= (___z49z___ _M) 2) (and (> (___z48z___ _M) 0) (not (___z46z___ _M))))))
(define-fun DEF__151 ((_M Int)) Bool(= (___z51z___ _M) (ite (= (___z45z___ _M) true) (ite (= (not (= (___z47z___ _M) 4)) true) 1 (___z44z___ _M)) (___z44z___ _M))))
(define-fun DEF__152 ((_M Int)) Bool(= (___z52z___ _M) (ite (= (___z50z___ _M) true) (ite (= (___z49z___ _M) 2) 1 (___z49z___ _M)) (___z49z___ _M))))
(define-fun DEF__153 ((_M Int)) Bool(= (___z53z___ _M) (ite (= (___z50z___ _M) true) (ite (= (not (= (___z52z___ _M) 2)) true) 2 (___z52z___ _M)) (___z52z___ _M))))
(define-fun DEF__154 ((_M Int)) Bool(= (___z54z___ _M) (and (= (___z53z___ _M) 2) (and (or (ite (= (not (= (___z34z___ _M) 0)) true) true false) (not (ite (= (not (= (___z35z___ _M) 0)) true) true false))) (not (or (___z50z___ _M) (___z46z___ _M)))))))
(define-fun DEF__155 ((_M Int)) Bool(= (___z55z___ _M) (ite (= (___z54z___ _M) true) (ite (= (___z53z___ _M) 2) 1 (___z53z___ _M)) (___z53z___ _M))))
(define-fun DEF__156 ((_M Int)) Bool(= (___z56z___ _M) (ite (= (___z50z___ _M) true) (ite (= (not (= (___z52z___ _M) 2)) true) 2 (___z51z___ _M)) (___z51z___ _M))))
(define-fun DEF__157 ((_M Int)) Bool(= (___z57z___ _M) (ite (= (not (and (>= (___z67z___ _M) 1) (<= (___z67z___ _M) 3))) true) 1 (___z67z___ _M))))
(define-fun DEF__115 ((_M Int)) Bool(= (___z15z___ _M) (ite (= _M _base) (or (not (and (___z22z___ _M) (not (___z3z___ _M)))) (or (not (or (or (or (or (or (or (or (or (or (___z5z___ _M) (___z6z___ _M)) (___z7z___ _M)) (___z8z___ _M)) (___z9z___ _M)) (___z10z___ _M)) (___z11z___ _M)) (___z12z___ _M)) (___z13z___ _M)) (___z4z___ _M))) (= (___z77z___ _M) (div (div (___z21z___ _M) 1) 60)))) (or (not (and (___z22z___ _M) (not (___z3z___ _M)))) (or (not (or (or (or (or (or (or (or (or (or (and (___z5z___ _M) (not (___z5z___ (- _M 1)))) (and (___z6z___ _M) (not (___z6z___ (- _M 1))))) (and (___z7z___ _M) (not (___z7z___ (- _M 1))))) (and (___z8z___ _M) (not (___z8z___ (- _M 1))))) (and (___z9z___ _M) (not (___z9z___ (- _M 1))))) (and (___z10z___ _M) (not (___z10z___ (- _M 1))))) (and (___z11z___ _M) (not (___z11z___ (- _M 1))))) (and (___z12z___ _M) (not (___z12z___ (- _M 1))))) (and (___z13z___ _M) (not (___z13z___ (- _M 1))))) (and (___z4z___ _M) (not (___z4z___ (- _M 1)))))) (= (___z77z___ _M) (div (div (___z21z___ _M) 1) 60)))))))
(define-fun DEF__158 ((_M Int)) Bool(= (___z58z___ _M) (and (not (and (>= (___z67z___ _M) 1) (<= (___z67z___ _M) 3))) (and (>= (___z57z___ _M) 1) (<= (___z57z___ _M) 3)))))
(define-fun DEF__159 ((_M Int)) Bool(= (___z59z___ _M) (and (___z58z___ _M) (and (and (>= (___z57z___ _M) 1) (<= (___z57z___ _M) 3)) (ite (= (not (= (___z35z___ _M) 0)) true) true false)))))
(define-fun DEF__160 ((_M Int)) Bool(= (___z60z___ _M) (ite (= (___z59z___ _M) true) (ite (= (not (= (___z57z___ _M) 2)) true) 2 (___z57z___ _M)) (___z57z___ _M))))
(define-fun DEF__161 ((_M Int)) Bool(= (___z61z___ _M) (ite (= (___z59z___ _M) true) (ite (= (not (= (___z57z___ _M) 2)) true) 2 (___z73z___ _M)) (___z73z___ _M))))
(define-fun DEF__119 ((_M Int)) Bool(= (___z19z___ _M) (ite (= _M _base) (___z2z___ _M) (and (___z2z___ _M) (not (___z2z___ (- _M 1)))))))
(define-fun DEF__162 ((_M Int)) Bool(= (___z62z___ _M) (and (___z58z___ _M) (and (and (>= (___z60z___ _M) 1) (<= (___z60z___ _M) 3)) (not (___z59z___ _M))))))
(define-fun DEF__120 ((_M Int)) Bool(= (___z20z___ _M) (ite (= _M _base) (___z3z___ _M) (and (___z3z___ _M) (not (___z3z___ (- _M 1)))))))
(define-fun DEF__163 ((_M Int)) Bool(= (___z63z___ _M) (ite (= (___z62z___ _M) true) (ite (= (not (= (___z60z___ _M) 3)) true) 3 (___z60z___ _M)) (___z60z___ _M))))
(define-fun DEF__121 ((_M Int)) Bool(= (___z21z___ _M) (ite (= _M _base) (ite (= (and (___z23z___ _M) (not (___z22z___ _M))) true) 0 (* (+ (+ (* (___z26z___ _M) 1) (* (___z25z___ _M) 10)) (* (___z24z___ _M) 60)) 1)) (ite (= (and (___z23z___ _M) (not (___z22z___ _M))) true) 0 (ite (= (___z22z___ _M) true) (* (+ (+ (* (___z26z___ _M) 1) (* (___z25z___ _M) 10)) (* (___z24z___ _M) 60)) 1) (___z21z___ (- _M 1)))))))
(define-fun DEF__164 ((_M Int)) Bool(= (___z64z___ _M) (= (___z72z___ _M) 4)))
(define-fun DEF__122 ((_M Int)) Bool(= (___z22z___ _M) (ite (= _M _base) true (ite (= 1 (___z80z___ (- _M 1))) true false))))
(define-fun DEF__165 ((_M Int)) Bool(= (___z65z___ _M) (ite (= (___z64z___ _M) true) (___z21z___ _M) (___z74z___ _M))))
(define-fun DEF__123 ((_M Int)) Bool(= (___z23z___ _M) (ite (= _M _base) true (ite (= (not (___z22z___ _M)) true) true (ite (= (___z22z___ (- _M 1)) true) false (___z23z___ (- _M 1)))))))
(define-fun DEF__166 ((_M Int)) Bool(= (___z66z___ _M) (and (___z64z___ _M) (and (= (___z72z___ _M) 4) (and (ite (= (not (= (___z33z___ _M) 0)) true) true false) (ite (= (not (= (ite (= (= (> (___z21z___ _M) 0) false) true) 0 1) 0)) true) true false))))))
(define-fun DEF__124 ((_M Int)) Bool(= (___z24z___ _M) (ite (= _M _base) 0 (ite (= (___z22z___ _M) true) (ite (= (___z23z___ _M) true) 0 (ite (= (___z3z___ _M) true) 0 (ite (= (ite (<= (ite (= (and (___z4z___ _M) (not (___z4z___ (- _M 1)))) true) 0 (ite (= (and (___z5z___ _M) (not (___z5z___ (- _M 1)))) true) 1 (ite (= (and (___z6z___ _M) (not (___z6z___ (- _M 1)))) true) 2 (ite (= (and (___z7z___ _M) (not (___z7z___ (- _M 1)))) true) 3 (ite (= (and (___z8z___ _M) (not (___z8z___ (- _M 1)))) true) 4 (ite (= (and (___z9z___ _M) (not (___z9z___ (- _M 1)))) true) 5 (ite (= (and (___z10z___ _M) (not (___z10z___ (- _M 1)))) true) 6 (ite (= (and (___z11z___ _M) (not (___z11z___ (- _M 1)))) true) 7 (ite (= (and (___z12z___ _M) (not (___z12z___ (- _M 1)))) true) 8 (ite (= (and (___z13z___ _M) (not (___z13z___ (- _M 1)))) true) 9 10)))))))))) 9) true false) true) (___z25z___ (- _M 1)) (___z24z___ (- _M 1))))) (___z24z___ (- _M 1))))))
(define-fun DEF__167 ((_M Int)) Bool(= (___z67z___ _M) (ite (= (___z66z___ _M) true) (ite (= (___z72z___ _M) 4) 0 (___z72z___ _M)) (___z72z___ _M))))
(define-fun DEF__125 ((_M Int)) Bool(= (___z25z___ _M) (ite (= _M _base) 0 (ite (= (___z22z___ _M) true) (ite (= (___z23z___ _M) true) 0 (ite (= (___z3z___ _M) true) 0 (ite (= (ite (<= (ite (= (and (___z4z___ _M) (not (___z4z___ (- _M 1)))) true) 0 (ite (= (and (___z5z___ _M) (not (___z5z___ (- _M 1)))) true) 1 (ite (= (and (___z6z___ _M) (not (___z6z___ (- _M 1)))) true) 2 (ite (= (and (___z7z___ _M) (not (___z7z___ (- _M 1)))) true) 3 (ite (= (and (___z8z___ _M) (not (___z8z___ (- _M 1)))) true) 4 (ite (= (and (___z9z___ _M) (not (___z9z___ (- _M 1)))) true) 5 (ite (= (and (___z10z___ _M) (not (___z10z___ (- _M 1)))) true) 6 (ite (= (and (___z11z___ _M) (not (___z11z___ (- _M 1)))) true) 7 (ite (= (and (___z12z___ _M) (not (___z12z___ (- _M 1)))) true) 8 (ite (= (and (___z13z___ _M) (not (___z13z___ (- _M 1)))) true) 9 10)))))))))) 9) true false) true) (___z26z___ (- _M 1)) (___z25z___ (- _M 1))))) (___z25z___ (- _M 1))))))
(define-fun DEF__168 ((_M Int)) Bool(= (___z68z___ _M) (ite (= (___z66z___ _M) true) (___z63z___ _M) (___z67z___ _M))))
(define-fun DEF__126 ((_M Int)) Bool(= (___z26z___ _M) (ite (= _M _base) (ite (= (___z3z___ _M) true) 0 (ite (= (ite (<= (ite (= (___z4z___ _M) true) 0 (ite (= (___z5z___ _M) true) 1 (ite (= (___z6z___ _M) true) 2 (ite (= (___z7z___ _M) true) 3 (ite (= (___z8z___ _M) true) 4 (ite (= (___z9z___ _M) true) 5 (ite (= (___z10z___ _M) true) 6 (ite (= (___z11z___ _M) true) 7 (ite (= (___z12z___ _M) true) 8 (ite (= (___z13z___ _M) true) 9 10)))))))))) 9) true false) true) (ite (= (___z4z___ _M) true) 0 (ite (= (___z5z___ _M) true) 1 (ite (= (___z6z___ _M) true) 2 (ite (= (___z7z___ _M) true) 3 (ite (= (___z8z___ _M) true) 4 (ite (= (___z9z___ _M) true) 5 (ite (= (___z10z___ _M) true) 6 (ite (= (___z11z___ _M) true) 7 (ite (= (___z12z___ _M) true) 8 (ite (= (___z13z___ _M) true) 9 10)))))))))) 0)) (ite (= (___z22z___ _M) true) (ite (= (___z23z___ _M) true) (ite (= (___z3z___ _M) true) 0 (ite (= (ite (<= (ite (= (___z4z___ _M) true) 0 (ite (= (___z5z___ _M) true) 1 (ite (= (___z6z___ _M) true) 2 (ite (= (___z7z___ _M) true) 3 (ite (= (___z8z___ _M) true) 4 (ite (= (___z9z___ _M) true) 5 (ite (= (___z10z___ _M) true) 6 (ite (= (___z11z___ _M) true) 7 (ite (= (___z12z___ _M) true) 8 (ite (= (___z13z___ _M) true) 9 10)))))))))) 9) true false) true) (ite (= (___z4z___ _M) true) 0 (ite (= (___z5z___ _M) true) 1 (ite (= (___z6z___ _M) true) 2 (ite (= (___z7z___ _M) true) 3 (ite (= (___z8z___ _M) true) 4 (ite (= (___z9z___ _M) true) 5 (ite (= (___z10z___ _M) true) 6 (ite (= (___z11z___ _M) true) 7 (ite (= (___z12z___ _M) true) 8 (ite (= (___z13z___ _M) true) 9 10)))))))))) 0)) (ite (= (___z3z___ _M) true) 0 (ite (= (ite (<= (ite (= (and (___z4z___ _M) (not (___z4z___ (- _M 1)))) true) 0 (ite (= (and (___z5z___ _M) (not (___z5z___ (- _M 1)))) true) 1 (ite (= (and (___z6z___ _M) (not (___z6z___ (- _M 1)))) true) 2 (ite (= (and (___z7z___ _M) (not (___z7z___ (- _M 1)))) true) 3 (ite (= (and (___z8z___ _M) (not (___z8z___ (- _M 1)))) true) 4 (ite (= (and (___z9z___ _M) (not (___z9z___ (- _M 1)))) true) 5 (ite (= (and (___z10z___ _M) (not (___z10z___ (- _M 1)))) true) 6 (ite (= (and (___z11z___ _M) (not (___z11z___ (- _M 1)))) true) 7 (ite (= (and (___z12z___ _M) (not (___z12z___ (- _M 1)))) true) 8 (ite (= (and (___z13z___ _M) (not (___z13z___ (- _M 1)))) true) 9 10)))))))))) 9) true false) true) (ite (= (and (___z4z___ _M) (not (___z4z___ (- _M 1)))) true) 0 (ite (= (and (___z5z___ _M) (not (___z5z___ (- _M 1)))) true) 1 (ite (= (and (___z6z___ _M) (not (___z6z___ (- _M 1)))) true) 2 (ite (= (and (___z7z___ _M) (not (___z7z___ (- _M 1)))) true) 3 (ite (= (and (___z8z___ _M) (not (___z8z___ (- _M 1)))) true) 4 (ite (= (and (___z9z___ _M) (not (___z9z___ (- _M 1)))) true) 5 (ite (= (and (___z10z___ _M) (not (___z10z___ (- _M 1)))) true) 6 (ite (= (and (___z11z___ _M) (not (___z11z___ (- _M 1)))) true) 7 (ite (= (and (___z12z___ _M) (not (___z12z___ (- _M 1)))) true) 8 (ite (= (and (___z13z___ _M) (not (___z13z___ (- _M 1)))) true) 9 10)))))))))) (___z26z___ (- _M 1))))) (___z26z___ (- _M 1))))))
(define-fun DEF__169 ((_M Int)) Bool(= (___z69z___ _M) (ite (= (___z66z___ _M) true) (ite (= (___z62z___ _M) true) (ite (= (not (= (___z60z___ _M) 3)) true) 3 (___z61z___ _M)) (___z61z___ _M)) (___z73z___ _M))))
(define-fun DEF__170 ((_M Int)) Bool(= (___z70z___ _M) (ite (= (not (= (___z72z___ _M) 4)) true) 4 (___z72z___ _M))))
(define-fun DEF__171 ((_M Int)) Bool(= (___z71z___ _M) (ite (= _M _base) true (ite (= true true) false (___z71z___ (- _M 1))))))
; Transition:
(define-fun trans ((_M Int)) Bool (and (DEF__171 _M)  (DEF__170 _M)  (DEF__169 _M)  (DEF__126 _M)  (DEF__168 _M)  (DEF__125 _M)  (DEF__167 _M)  (DEF__124 _M)  (DEF__166 _M)  (DEF__123 _M)  (DEF__165 _M)  (DEF__122 _M)  (DEF__164 _M)  (DEF__121 _M)  (DEF__163 _M)  (DEF__120 _M)  (DEF__162 _M)  (DEF__119 _M)  (DEF__161 _M)  (DEF__160 _M)  (DEF__159 _M)  (DEF__158 _M)  (DEF__115 _M)  (DEF__157 _M)  (DEF__156 _M)  (DEF__155 _M)  (DEF__154 _M)  (DEF__153 _M)  (DEF__152 _M)  (DEF__151 _M)  (DEF__150 _M)  (DEF__149 _M)  (DEF__148 _M)  (DEF__147 _M)  (DEF__146 _M)  (DEF__145 _M)  (DEF__144 _M)  (DEF__143 _M)  (DEF__142 _M)  (DEF__141 _M)  (DEF__140 _M)  (DEF__139 _M)  (DEF__138 _M)  (DEF__137 _M)  (DEF__180 _M)  (DEF__136 _M)  (DEF__135 _M)  (DEF__177 _M)  (DEF__134 _M)  (DEF__176 _M)  (DEF__133 _M)  (DEF__175 _M)  (DEF__174 _M)  (DEF__173 _M)  (DEF__172 _M) ))

(define-fun P ((_M Int)) Bool(= (___z15z___ _M) true))



; BASE DONE

; Begin induction:
; print_initialization
; def_assert_both1
; def_assert_both
(assert (DEF__172 0))
; print_checker_assertion
(assert (DEF__173 0))
; print_checker_assertion
(assert (DEF__174 0))
; print_checker_assertion
(assert (DEF__175 0))
; print_checker_assertion
(assert (DEF__133 0))
; print_checker_assertion
(assert (DEF__176 0))
; print_checker_assertion
(assert (DEF__134 0))
; print_checker_assertion
(assert (DEF__177 0))
; print_checker_assertion
(assert (DEF__135 0))
; print_checker_assertion
(assert (DEF__136 0))
; print_checker_assertion
(assert (DEF__180 0))
; print_checker_assertion
(assert (DEF__137 0))
; print_checker_assertion
(assert (DEF__138 0))
; print_checker_assertion
(assert (DEF__139 0))
; print_checker_assertion
(assert (DEF__140 0))
; print_checker_assertion
(assert (DEF__141 0))
; print_checker_assertion
(assert (DEF__142 0))
; print_checker_assertion
(assert (DEF__143 0))
; print_checker_assertion
(assert (DEF__144 0))
; print_checker_assertion
(assert (DEF__145 0))
; print_checker_assertion
(assert (DEF__146 0))
; print_checker_assertion
(assert (DEF__147 0))
; print_checker_assertion
(assert (DEF__148 0))
; print_checker_assertion
(assert (DEF__149 0))
; print_checker_assertion
(assert (DEF__150 0))
; print_checker_assertion
(assert (DEF__151 0))
; print_checker_assertion
(assert (DEF__152 0))
; print_checker_assertion
(assert (DEF__153 0))
; print_checker_assertion
(assert (DEF__154 0))
; print_checker_assertion
(assert (DEF__155 0))
; print_checker_assertion
(assert (DEF__156 0))
; print_checker_assertion
(assert (DEF__157 0))
; print_checker_assertion
(assert (DEF__115 0))
; print_checker_assertion
(assert (DEF__158 0))
; print_checker_assertion
(assert (DEF__159 0))
; print_checker_assertion
(assert (DEF__160 0))
; print_checker_assertion
(assert (DEF__161 0))
; print_checker_assertion
(assert (DEF__119 0))
; print_checker_assertion
(assert (DEF__162 0))
; print_checker_assertion
(assert (DEF__120 0))
; print_checker_assertion
(assert (DEF__163 0))
; print_checker_assertion
(assert (DEF__121 0))
; print_checker_assertion
(assert (DEF__164 0))
; print_checker_assertion
(assert (DEF__122 0))
; print_checker_assertion
(assert (DEF__165 0))
; print_checker_assertion
(assert (DEF__123 0))
; print_checker_assertion
(assert (DEF__166 0))
; print_checker_assertion
(assert (DEF__124 0))
; print_checker_assertion
(assert (DEF__167 0))
; print_checker_assertion
(assert (DEF__125 0))
; print_checker_assertion
(assert (DEF__168 0))
; print_checker_assertion
(assert (DEF__126 0))
; print_checker_assertion
(assert (DEF__169 0))
; print_checker_assertion
(assert (DEF__170 0))
; print_checker_assertion
(assert (DEF__171 0))
; print_checker_assertion
; def_assert_both1
; def_assert_both
(assert (DEF__172 (- 0 1)))
; print_checker_assertion
(assert (DEF__173 (- 0 1)))
; print_checker_assertion
(assert (DEF__174 (- 0 1)))
; print_checker_assertion
(assert (DEF__175 (- 0 1)))
; print_checker_assertion
(assert (DEF__133 (- 0 1)))
; print_checker_assertion
(assert (DEF__176 (- 0 1)))
; print_checker_assertion
(assert (DEF__134 (- 0 1)))
; print_checker_assertion
(assert (DEF__177 (- 0 1)))
; print_checker_assertion
(assert (DEF__135 (- 0 1)))
; print_checker_assertion
(assert (DEF__136 (- 0 1)))
; print_checker_assertion
(assert (DEF__180 (- 0 1)))
; print_checker_assertion
(assert (DEF__137 (- 0 1)))
; print_checker_assertion
(assert (DEF__138 (- 0 1)))
; print_checker_assertion
(assert (DEF__139 (- 0 1)))
; print_checker_assertion
(assert (DEF__140 (- 0 1)))
; print_checker_assertion
(assert (DEF__141 (- 0 1)))
; print_checker_assertion
(assert (DEF__142 (- 0 1)))
; print_checker_assertion
(assert (DEF__143 (- 0 1)))
; print_checker_assertion
(assert (DEF__144 (- 0 1)))
; print_checker_assertion
(assert (DEF__145 (- 0 1)))
; print_checker_assertion
(assert (DEF__146 (- 0 1)))
; print_checker_assertion
(assert (DEF__147 (- 0 1)))
; print_checker_assertion
(assert (DEF__148 (- 0 1)))
; print_checker_assertion
(assert (DEF__149 (- 0 1)))
; print_checker_assertion
(assert (DEF__150 (- 0 1)))
; print_checker_assertion
(assert (DEF__151 (- 0 1)))
; print_checker_assertion
(assert (DEF__152 (- 0 1)))
; print_checker_assertion
(assert (DEF__153 (- 0 1)))
; print_checker_assertion
(assert (DEF__154 (- 0 1)))
; print_checker_assertion
(assert (DEF__155 (- 0 1)))
; print_checker_assertion
(assert (DEF__156 (- 0 1)))
; print_checker_assertion
(assert (DEF__157 (- 0 1)))
; print_checker_assertion
(assert (DEF__115 (- 0 1)))
; print_checker_assertion
(assert (DEF__158 (- 0 1)))
; print_checker_assertion
(assert (DEF__159 (- 0 1)))
; print_checker_assertion
(assert (DEF__160 (- 0 1)))
; print_checker_assertion
(assert (DEF__161 (- 0 1)))
; print_checker_assertion
(assert (DEF__119 (- 0 1)))
; print_checker_assertion
(assert (DEF__162 (- 0 1)))
; print_checker_assertion
(assert (DEF__120 (- 0 1)))
; print_checker_assertion
(assert (DEF__163 (- 0 1)))
; print_checker_assertion
(assert (DEF__121 (- 0 1)))
; print_checker_assertion
(assert (DEF__164 (- 0 1)))
; print_checker_assertion
(assert (DEF__122 (- 0 1)))
; print_checker_assertion
(assert (DEF__165 (- 0 1)))
; print_checker_assertion
(assert (DEF__123 (- 0 1)))
; print_checker_assertion
(assert (DEF__166 (- 0 1)))
; print_checker_assertion
(assert (DEF__124 (- 0 1)))
; print_checker_assertion
(assert (DEF__167 (- 0 1)))
; print_checker_assertion
(assert (DEF__125 (- 0 1)))
; print_checker_assertion
(assert (DEF__168 (- 0 1)))
; print_checker_assertion
(assert (DEF__126 (- 0 1)))
; print_checker_assertion
(assert (DEF__169 (- 0 1)))
; print_checker_assertion
(assert (DEF__170 (- 0 1)))
; print_checker_assertion
(assert (DEF__171 (- 0 1)))
; print_checker_assertion

; Checking k=2 base
; not refinement_pass
(assert (not (=> (= _base (- 0 1)) (and (P (- 0 1)) (P 0)))))
(assert true)
(check-sat)
