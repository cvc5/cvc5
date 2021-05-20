; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)
(declare-fun t@0 () Real)
(declare-fun y2@0 () Real)
(declare-fun y1@0 () Real)
(declare-fun t@5 () Real)
(declare-fun y1@5 () Real)
(declare-fun y2@5 () Real)
(declare-fun t@6 () Real)
(declare-fun y1@6 () Real)
(declare-fun y2@6 () Real)
(declare-fun t@1 () Real)
(declare-fun y1@1 () Real)
(declare-fun y2@1 () Real)
(declare-fun t@7 () Real)
(declare-fun y1@7 () Real)
(declare-fun y2@7 () Real)
(declare-fun y1@10 () Real)
(declare-fun y2@10 () Real)
(declare-fun t@2 () Real)
(declare-fun y1@2 () Real)
(declare-fun y2@2 () Real)
(declare-fun t@8 () Real)
(declare-fun y1@8 () Real)
(declare-fun y2@8 () Real)
(declare-fun t@3 () Real)
(declare-fun y1@3 () Real)
(declare-fun y2@3 () Real)
(declare-fun t@9 () Real)
(declare-fun y1@9 () Real)
(declare-fun y2@9 () Real)
(declare-fun t@4 () Real)
(declare-fun y1@4 () Real)
(declare-fun y2@4 () Real)
(declare-fun t@10 () Real)
(assert (let ((.def_0 (<= (- 3.0) y2@10))) (let ((.def_1 (<= y2@10 3.0))) (let ((.def_2 (<= y1@10 3.0))) (let ((.def_3 (<= (- 3.0) y1@10))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (and .def_4 .def_1))) (let ((.def_6 (and 
.def_5 .def_0))) (let ((.def_7 (not .def_6))) (let ((.def_8 (cos t@10))) (let ((.def_9 (* (- 2.0) .def_8))) (let ((.def_10 (sin t@10))) (let ((.def_11 (* (- 2.0) .def_10))) (let ((.def_12 (+ .def_11 .def_9))) (let ((.def_13 (+ 
y2@10 .def_12))) (let ((.def_14 (= .def_13 0.0))) (let ((.def_15 (* 2.0 .def_10))) (let ((.def_16 (+ .def_15 .def_9))) (let ((.def_17 (+ y1@10 .def_16))) (let ((.def_18 (= .def_17 0.0))) (let ((.def_19 (<= t@10 7.0))) (let 
((.def_20 (* (- 1.0) t@10))) (let ((.def_21 (+ t@9 .def_20))) (let ((.def_22 (= .def_21 (- (/ 1 2))))) (let ((.def_23 (and .def_22 .def_19))) (let ((.def_24 (and .def_23 .def_18))) (let ((.def_25 (and .def_24 .def_14))) (let 
((.def_26 (* (- 1.0) y2@9))) (let ((.def_27 (cos t@9))) (let ((.def_28 (* 2.0 .def_27))) (let ((.def_29 (+ .def_28 .def_26))) (let ((.def_30 (sin t@9))) (let ((.def_31 (* 2.0 .def_30))) (let ((.def_32 (+ .def_31 .def_29))) (let 
((.def_33 (= .def_32 0.0))) (let ((.def_34 (* (- 2.0) .def_27))) (let ((.def_35 (+ .def_34 y1@9))) (let ((.def_36 (+ .def_31 .def_35))) (let ((.def_37 (= .def_36 0.0))) (let ((.def_38 (<= t@9 7.0))) (let ((.def_39 (* (- 1.0) t@9))) 
(let ((.def_40 (+ t@8 .def_39))) (let ((.def_41 (= .def_40 (- (/ 1 2))))) (let ((.def_42 (and .def_41 .def_38))) (let ((.def_43 (and .def_42 .def_37))) (let ((.def_44 (and .def_43 .def_33))) (let ((.def_45 (* (- 1.0) y2@8))) (let 
((.def_46 (cos t@8))) (let ((.def_47 (* 2.0 .def_46))) (let ((.def_48 (+ .def_47 .def_45))) (let ((.def_49 (sin t@8))) (let ((.def_50 (* 2.0 .def_49))) (let ((.def_51 (+ .def_50 .def_48))) (let ((.def_52 (= .def_51 0.0))) (let 
((.def_53 (* (- 2.0) .def_46))) (let ((.def_54 (+ .def_53 y1@8))) (let ((.def_55 (+ .def_50 .def_54))) (let ((.def_56 (= .def_55 0.0))) (let ((.def_57 (<= t@8 7.0))) (let ((.def_58 (* (- 1.0) t@8))) (let ((.def_59 (+ t@7 .def_58))) 
(let ((.def_60 (= .def_59 (- (/ 1 2))))) (let ((.def_61 (and .def_60 .def_57))) (let ((.def_62 (and .def_61 .def_56))) (let ((.def_63 (and .def_62 .def_52))) (let ((.def_64 (* (- 1.0) y2@7))) (let ((.def_65 (cos t@7))) (let 
((.def_66 (* 2.0 .def_65))) (let ((.def_67 (+ .def_66 .def_64))) (let ((.def_68 (sin t@7))) (let ((.def_69 (* 2.0 .def_68))) (let ((.def_70 (+ .def_69 .def_67))) (let ((.def_71 (= .def_70 0.0))) (let ((.def_72 (* (- 2.0) .def_65))) 
(let ((.def_73 (+ .def_72 y1@7))) (let ((.def_74 (+ .def_69 .def_73))) (let ((.def_75 (= .def_74 0.0))) (let ((.def_76 (<= t@7 7.0))) (let ((.def_77 (* (- 1.0) t@7))) (let ((.def_78 (+ t@6 .def_77))) (let ((.def_79 (= .def_78 (- (/ 
1 2))))) (let ((.def_80 (and .def_79 .def_76))) (let ((.def_81 (and .def_80 .def_75))) (let ((.def_82 (and .def_81 .def_71))) (let ((.def_83 (* (- 1.0) y2@6))) (let ((.def_84 (cos t@6))) (let ((.def_85 (* 2.0 .def_84))) (let 
((.def_86 (+ .def_85 .def_83))) (let ((.def_87 (sin t@6))) (let ((.def_88 (* 2.0 .def_87))) (let ((.def_89 (+ .def_88 .def_86))) (let ((.def_90 (= .def_89 0.0))) (let ((.def_91 (* (- 2.0) .def_84))) (let ((.def_92 (+ .def_91 
y1@6))) (let ((.def_93 (+ .def_88 .def_92))) (let ((.def_94 (= .def_93 0.0))) (let ((.def_95 (<= t@6 7.0))) (let ((.def_96 (* (- 1.0) t@6))) (let ((.def_97 (+ t@5 .def_96))) (let ((.def_98 (= .def_97 (- (/ 1 2))))) (let ((.def_99 
(and .def_98 .def_95))) (let ((.def_100 (and .def_99 .def_94))) (let ((.def_101 (and .def_100 .def_90))) (let ((.def_102 (* (- 1.0) y2@5))) (let ((.def_103 (cos t@5))) (let ((.def_104 (* 2.0 .def_103))) (let ((.def_105 (+ .def_104 
.def_102))) (let ((.def_106 (sin t@5))) (let ((.def_107 (* 2.0 .def_106))) (let ((.def_108 (+ .def_107 .def_105))) (let ((.def_109 (= .def_108 0.0))) (let ((.def_110 (* (- 2.0) .def_103))) (let ((.def_111 (+ .def_110 y1@5))) (let 
((.def_112 (+ .def_107 .def_111))) (let ((.def_113 (= .def_112 0.0))) (let ((.def_114 (<= t@5 7.0))) (let ((.def_115 (* (- 1.0) t@5))) (let ((.def_116 (+ t@4 .def_115))) (let ((.def_117 (= .def_116 (- (/ 1 2))))) (let ((.def_118 
(and .def_117 .def_114))) (let ((.def_119 (and .def_118 .def_113))) (let ((.def_120 (and .def_119 .def_109))) (let ((.def_121 (* (- 1.0) y2@4))) (let ((.def_122 (cos t@4))) (let ((.def_123 (* 2.0 .def_122))) (let ((.def_124 (+ 
.def_123 .def_121))) (let ((.def_125 (sin t@4))) (let ((.def_126 (* 2.0 .def_125))) (let ((.def_127 (+ .def_126 .def_124))) (let ((.def_128 (= .def_127 0.0))) (let ((.def_129 (* (- 2.0) .def_122))) (let ((.def_130 (+ .def_129 
y1@4))) (let ((.def_131 (+ .def_126 .def_130))) (let ((.def_132 (= .def_131 0.0))) (let ((.def_133 (<= t@4 7.0))) (let ((.def_134 (* (- 1.0) t@4))) (let ((.def_135 (+ t@3 .def_134))) (let ((.def_136 (= .def_135 (- (/ 1 2))))) (let 
((.def_137 (and .def_136 .def_133))) (let ((.def_138 (and .def_137 .def_132))) (let ((.def_139 (and .def_138 .def_128))) (let ((.def_140 (* (- 1.0) y2@3))) (let ((.def_141 (cos t@3))) (let ((.def_142 (* 2.0 .def_141))) (let 
((.def_143 (+ .def_142 .def_140))) (let ((.def_144 (sin t@3))) (let ((.def_145 (* 2.0 .def_144))) (let ((.def_146 (+ .def_145 .def_143))) (let ((.def_147 (= .def_146 0.0))) (let ((.def_148 (* (- 2.0) .def_141))) (let ((.def_149 (+ 
.def_148 y1@3))) (let ((.def_150 (+ .def_145 .def_149))) (let ((.def_151 (= .def_150 0.0))) (let ((.def_152 (<= t@3 7.0))) (let ((.def_153 (* (- 1.0) t@3))) (let ((.def_154 (+ t@2 .def_153))) (let ((.def_155 (= .def_154 (- (/ 1 
2))))) (let ((.def_156 (and .def_155 .def_152))) (let ((.def_157 (and .def_156 .def_151))) (let ((.def_158 (and .def_157 .def_147))) (let ((.def_159 (* (- 1.0) y2@2))) (let ((.def_160 (cos t@2))) (let ((.def_161 (* 2.0 .def_160))) 
(let ((.def_162 (+ .def_161 .def_159))) (let ((.def_163 (sin t@2))) (let ((.def_164 (* 2.0 .def_163))) (let ((.def_165 (+ .def_164 .def_162))) (let ((.def_166 (= .def_165 0.0))) (let ((.def_167 (* (- 2.0) .def_160))) (let 
((.def_168 (+ .def_167 y1@2))) (let ((.def_169 (+ .def_164 .def_168))) (let ((.def_170 (= .def_169 0.0))) (let ((.def_171 (<= t@2 7.0))) (let ((.def_172 (* (- 1.0) t@2))) (let ((.def_173 (+ t@1 .def_172))) (let ((.def_174 (= 
.def_173 (- (/ 1 2))))) (let ((.def_175 (and .def_174 .def_171))) (let ((.def_176 (and .def_175 .def_170))) (let ((.def_177 (and .def_176 .def_166))) (let ((.def_178 (* (- 1.0) y2@1))) (let ((.def_179 (cos t@1))) (let ((.def_180 (* 
2.0 .def_179))) (let ((.def_181 (+ .def_180 .def_178))) (let ((.def_182 (sin t@1))) (let ((.def_183 (* 2.0 .def_182))) (let ((.def_184 (+ .def_183 .def_181))) (let ((.def_185 (= .def_184 0.0))) (let ((.def_186 (* (- 2.0) 
.def_179))) (let ((.def_187 (+ .def_186 y1@1))) (let ((.def_188 (+ .def_183 .def_187))) (let ((.def_189 (= .def_188 0.0))) (let ((.def_190 (<= t@1 7.0))) (let ((.def_191 (* (- 1.0) t@1))) (let ((.def_192 (+ t@0 .def_191))) (let 
((.def_193 (= .def_192 (- (/ 1 2))))) (let ((.def_194 (and .def_193 .def_190))) (let ((.def_195 (and .def_194 .def_189))) (let ((.def_196 (and .def_195 .def_185))) (let ((.def_197 (= t@0 0.0))) (let ((.def_198 (cos t@0))) (let 
((.def_199 (* (- 2.0) .def_198))) (let ((.def_200 (+ .def_199 y1@0))) (let ((.def_201 (sin t@0))) (let ((.def_202 (* 2.0 .def_201))) (let ((.def_203 (+ .def_202 .def_200))) (let ((.def_204 (= .def_203 0.0))) (let ((.def_205 (* (- 
1.0) y2@0))) (let ((.def_206 (* 2.0 .def_198))) (let ((.def_207 (+ .def_206 .def_205))) (let ((.def_208 (+ .def_202 .def_207))) (let ((.def_209 (= .def_208 0.0))) (let ((.def_210 (and .def_209 .def_204))) (let ((.def_211 (and 
.def_210 .def_197))) (let ((.def_212 (and .def_211 .def_196 .def_177 .def_158 .def_139 .def_120 .def_101 .def_82 .def_63 .def_44 .def_25 .def_7))) 
.def_212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
