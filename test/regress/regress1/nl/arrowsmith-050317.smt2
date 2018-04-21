; COMMAND-LINE: --nl-ext
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :status unsat)
(declare-fun time__AT0@0 () Real)
(declare-fun instance.location.0__AT0@0 () Bool)
(declare-fun instance.y__AT0@0 () Real)
(declare-fun instance.x__AT0@0 () Real)
(declare-fun instance.location.0__AT0@4 () Bool)
(declare-fun event_is_timed__AT0@1 () Bool)
(declare-fun event_is_timed__AT0@0 () Bool)
(declare-fun instance.location.0__AT0@1 () Bool)
(declare-fun instance.x__AT0@1 () Real)
(declare-fun instance.y__AT0@1 () Real)
(declare-fun instance.EVENT.0__AT0@0 () Bool)
(declare-fun instance.EVENT.1__AT0@0 () Bool)
(declare-fun time__AT0@1 () Real)
(declare-fun event_is_timed__AT0@3 () Bool)
(declare-fun instance.location.0__AT0@3 () Bool)
(declare-fun instance.x__AT0@3 () Real)
(declare-fun instance.y__AT0@3 () Real)
(declare-fun instance.EVENT.0__AT0@2 () Bool)
(declare-fun instance.EVENT.1__AT0@2 () Bool)
(declare-fun time__AT0@3 () Real)
(declare-fun event_is_timed__AT0@2 () Bool)
(declare-fun instance.location.0__AT0@2 () Bool)
(declare-fun instance.x__AT0@2 () Real)
(declare-fun instance.y__AT0@2 () Real)
(declare-fun instance.EVENT.0__AT0@1 () Bool)
(declare-fun instance.EVENT.1__AT0@1 () Bool)
(declare-fun time__AT0@2 () Real)
(declare-fun event_is_timed__AT0@4 () Bool)
(declare-fun instance.x__AT0@4 () Real)
(declare-fun instance.y__AT0@4 () Real)
(declare-fun instance.EVENT.0__AT0@3 () Bool)
(declare-fun instance.EVENT.1__AT0@3 () Bool)
(declare-fun time__AT0@4 () Real)
(assert (let ((.def_0 (not instance.EVENT.1__AT0@3))) (let ((.def_1 (not instance.EVENT.0__AT0@3))) (let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= event_is_timed__AT0@3 instance.EVENT.1__AT0@3))) (let ((.def_4 (<= time__AT0@3 
time__AT0@4))) (let ((.def_5 (or .def_0 .def_4))) (let ((.def_6 (and .def_5 .def_3))) (let ((.def_7 (= time__AT0@3 time__AT0@4))) (let ((.def_8 (or instance.EVENT.1__AT0@3 .def_7))) (let ((.def_9 (and .def_8 .def_6))) (let 
((.def_10 (<= instance.x__AT0@3 0.0))) (let ((.def_11 (not .def_10))) (let ((.def_12 (not instance.location.0__AT0@3))) (let ((.def_13 (and .def_12 .def_11))) (let ((.def_14 (and instance.location.0__AT0@4 .def_13))) (let ((.def_15 
(= instance.x__AT0@3 instance.x__AT0@4))) (let ((.def_16 (and .def_15 .def_14))) (let ((.def_17 (= instance.y__AT0@3 instance.y__AT0@4))) (let ((.def_18 (and .def_17 .def_16))) (let ((.def_19 (<= instance.y__AT0@3 0.0))) (let 
((.def_20 (and .def_12 .def_19))) (let ((.def_21 (and instance.location.0__AT0@4 .def_20))) (let ((.def_22 (and .def_15 .def_21))) (let ((.def_23 (and .def_17 .def_22))) (let ((.def_24 (or .def_23 .def_18))) (let ((.def_25 (and 
.def_7 .def_24))) (let ((.def_26 (or instance.EVENT.1__AT0@3 .def_25))) (let ((.def_27 (not .def_7))) (let ((.def_28 (and .def_15 .def_17))) (let ((.def_29 (or .def_28 .def_27))) (let ((.def_30 (and .def_28 .def_29))) (let 
((.def_31 (or .def_30 .def_12))) (let ((.def_32 (* (- 1.0) time__AT0@3))) (let ((.def_33 (+ .def_32 time__AT0@4))) (let ((.def_34 (exp .def_33))) (let ((.def_35 (* instance.x__AT0@3 .def_34))) (let ((.def_36 (= instance.x__AT0@4 
.def_35))) (let ((.def_37 (* 2.0 instance.x__AT0@4))) (let ((.def_38 (* instance.y__AT0@4 .def_37))) (let ((.def_39 (* (- 1.0) .def_38))) (let ((.def_40 (* 2.0 instance.x__AT0@3))) (let ((.def_41 (* instance.y__AT0@3 .def_40))) 
(let ((.def_42 (* (- 1.0) .def_41))) (let ((.def_43 (+ instance.y__AT0@3 .def_42))) (let ((.def_44 (* .def_43 .def_34))) (let ((.def_45 (* (- 1.0) .def_44))) (let ((.def_46 (+ .def_45 .def_39))) (let ((.def_47 (+ instance.y__AT0@4 
.def_46))) (let ((.def_48 (= .def_47 0.0))) (let ((.def_49 (and .def_48 .def_36))) (let ((.def_50 (and .def_49 .def_29))) (let ((.def_51 (or instance.location.0__AT0@3 .def_50))) (let ((.def_52 (and .def_51 .def_31))) (let 
((.def_53 (and .def_52 .def_4))) (let ((.def_54 (= instance.location.0__AT0@4 instance.location.0__AT0@3))) (let ((.def_55 (and .def_54 .def_53))) (let ((.def_56 (or .def_0 .def_55))) (let ((.def_57 (and .def_56 .def_26))) (let 
((.def_58 (and .def_1 .def_0))) (let ((.def_59 (or .def_58 .def_57))) (let ((.def_60 (and .def_59 .def_9))) (let ((.def_61 (not .def_58))) (let ((.def_62 (and .def_54 .def_15))) (let ((.def_63 (and .def_62 .def_17))) (let ((.def_64 
(or .def_63 .def_61))) (let ((.def_65 (and .def_64 .def_60))) (let ((.def_66 (not event_is_timed__AT0@3))) (let ((.def_67 (= event_is_timed__AT0@4 .def_66))) (let ((.def_68 (and .def_67 .def_65))) (let ((.def_69 (and .def_68 
.def_2))) (let ((.def_70 (not instance.EVENT.1__AT0@2))) (let ((.def_71 (not instance.EVENT.0__AT0@2))) (let ((.def_72 (or .def_71 .def_70))) (let ((.def_73 (= event_is_timed__AT0@2 instance.EVENT.1__AT0@2))) (let ((.def_74 (<= 
time__AT0@2 time__AT0@3))) (let ((.def_75 (or .def_70 .def_74))) (let ((.def_76 (and .def_75 .def_73))) (let ((.def_77 (= time__AT0@2 time__AT0@3))) (let ((.def_78 (or instance.EVENT.1__AT0@2 .def_77))) (let ((.def_79 (and .def_78 
.def_76))) (let ((.def_80 (<= instance.x__AT0@2 0.0))) (let ((.def_81 (not .def_80))) (let ((.def_82 (not instance.location.0__AT0@2))) (let ((.def_83 (and .def_82 .def_81))) (let ((.def_84 (and instance.location.0__AT0@3 
.def_83))) (let ((.def_85 (= instance.x__AT0@2 instance.x__AT0@3))) (let ((.def_86 (and .def_85 .def_84))) (let ((.def_87 (= instance.y__AT0@2 instance.y__AT0@3))) (let ((.def_88 (and .def_87 .def_86))) (let ((.def_89 (<= 
instance.y__AT0@2 0.0))) (let ((.def_90 (and .def_82 .def_89))) (let ((.def_91 (and instance.location.0__AT0@3 .def_90))) (let ((.def_92 (and .def_85 .def_91))) (let ((.def_93 (and .def_87 .def_92))) (let ((.def_94 (or .def_93 
.def_88))) (let ((.def_95 (and .def_77 .def_94))) (let ((.def_96 (or instance.EVENT.1__AT0@2 .def_95))) (let ((.def_97 (not .def_77))) (let ((.def_98 (and .def_85 .def_87))) (let ((.def_99 (or .def_98 .def_97))) (let ((.def_100 
(and .def_98 .def_99))) (let ((.def_101 (or .def_100 .def_82))) (let ((.def_102 (* (- 1.0) time__AT0@2))) (let ((.def_103 (+ .def_102 time__AT0@3))) (let ((.def_104 (exp .def_103))) (let ((.def_105 (* instance.x__AT0@2 .def_104))) 
(let ((.def_106 (= instance.x__AT0@3 .def_105))) (let ((.def_107 (* 2.0 instance.x__AT0@2))) (let ((.def_108 (* instance.y__AT0@2 .def_107))) (let ((.def_109 (* (- 1.0) .def_108))) (let ((.def_110 (+ instance.y__AT0@2 .def_109))) 
(let ((.def_111 (* .def_110 .def_104))) (let ((.def_112 (* (- 1.0) .def_111))) (let ((.def_113 (+ .def_112 .def_42))) (let ((.def_114 (+ instance.y__AT0@3 .def_113))) (let ((.def_115 (= .def_114 0.0))) (let ((.def_116 (and .def_115 
.def_106))) (let ((.def_117 (and .def_116 .def_99))) (let ((.def_118 (or instance.location.0__AT0@2 .def_117))) (let ((.def_119 (and .def_118 .def_101))) (let ((.def_120 (and .def_119 .def_74))) (let ((.def_121 (= 
instance.location.0__AT0@2 instance.location.0__AT0@3))) (let ((.def_122 (and .def_121 .def_120))) (let ((.def_123 (or .def_70 .def_122))) (let ((.def_124 (and .def_123 .def_96))) (let ((.def_125 (and .def_71 .def_70))) (let 
((.def_126 (or .def_125 .def_124))) (let ((.def_127 (and .def_126 .def_79))) (let ((.def_128 (not .def_125))) (let ((.def_129 (and .def_121 .def_85))) (let ((.def_130 (and .def_129 .def_87))) (let ((.def_131 (or .def_130 
.def_128))) (let ((.def_132 (and .def_131 .def_127))) (let ((.def_133 (not event_is_timed__AT0@2))) (let ((.def_134 (= event_is_timed__AT0@3 .def_133))) (let ((.def_135 (and .def_134 .def_132))) (let ((.def_136 (and .def_135 
.def_72))) (let ((.def_137 (not instance.EVENT.1__AT0@1))) (let ((.def_138 (not instance.EVENT.0__AT0@1))) (let ((.def_139 (or .def_138 .def_137))) (let ((.def_140 (= event_is_timed__AT0@1 instance.EVENT.1__AT0@1))) (let ((.def_141 
(<= time__AT0@1 time__AT0@2))) (let ((.def_142 (or .def_137 .def_141))) (let ((.def_143 (and .def_142 .def_140))) (let ((.def_144 (= time__AT0@1 time__AT0@2))) (let ((.def_145 (or instance.EVENT.1__AT0@1 .def_144))) (let ((.def_146 
(and .def_145 .def_143))) (let ((.def_147 (<= instance.x__AT0@1 0.0))) (let ((.def_148 (not .def_147))) (let ((.def_149 (not instance.location.0__AT0@1))) (let ((.def_150 (and .def_149 .def_148))) (let ((.def_151 (and 
instance.location.0__AT0@2 .def_150))) (let ((.def_152 (= instance.x__AT0@1 instance.x__AT0@2))) (let ((.def_153 (and .def_152 .def_151))) (let ((.def_154 (= instance.y__AT0@1 instance.y__AT0@2))) (let ((.def_155 (and .def_154 
.def_153))) (let ((.def_156 (<= instance.y__AT0@1 0.0))) (let ((.def_157 (and .def_149 .def_156))) (let ((.def_158 (and instance.location.0__AT0@2 .def_157))) (let ((.def_159 (and .def_152 .def_158))) (let ((.def_160 (and .def_154 
.def_159))) (let ((.def_161 (or .def_160 .def_155))) (let ((.def_162 (and .def_144 .def_161))) (let ((.def_163 (or instance.EVENT.1__AT0@1 .def_162))) (let ((.def_164 (not .def_144))) (let ((.def_165 (and .def_152 .def_154))) (let 
((.def_166 (or .def_165 .def_164))) (let ((.def_167 (and .def_165 .def_166))) (let ((.def_168 (or .def_167 .def_149))) (let ((.def_169 (* (- 1.0) time__AT0@1))) (let ((.def_170 (+ .def_169 time__AT0@2))) (let ((.def_171 (exp 
.def_170))) (let ((.def_172 (* instance.x__AT0@1 .def_171))) (let ((.def_173 (= instance.x__AT0@2 .def_172))) (let ((.def_174 (* 2.0 instance.x__AT0@1))) (let ((.def_175 (* instance.y__AT0@1 .def_174))) (let ((.def_176 (* (- 1.0) 
.def_175))) (let ((.def_177 (+ instance.y__AT0@1 .def_176))) (let ((.def_178 (* .def_177 .def_171))) (let ((.def_179 (* (- 1.0) .def_178))) (let ((.def_180 (+ .def_179 .def_109))) (let ((.def_181 (+ instance.y__AT0@2 .def_180))) 
(let ((.def_182 (= .def_181 0.0))) (let ((.def_183 (and .def_182 .def_173))) (let ((.def_184 (and .def_183 .def_166))) (let ((.def_185 (or instance.location.0__AT0@1 .def_184))) (let ((.def_186 (and .def_185 .def_168))) (let 
((.def_187 (and .def_186 .def_141))) (let ((.def_188 (= instance.location.0__AT0@1 instance.location.0__AT0@2))) (let ((.def_189 (and .def_188 .def_187))) (let ((.def_190 (or .def_137 .def_189))) (let ((.def_191 (and .def_190 
.def_163))) (let ((.def_192 (and .def_138 .def_137))) (let ((.def_193 (or .def_192 .def_191))) (let ((.def_194 (and .def_193 .def_146))) (let ((.def_195 (not .def_192))) (let ((.def_196 (and .def_188 .def_152))) (let ((.def_197 
(and .def_196 .def_154))) (let ((.def_198 (or .def_197 .def_195))) (let ((.def_199 (and .def_198 .def_194))) (let ((.def_200 (not event_is_timed__AT0@1))) (let ((.def_201 (= event_is_timed__AT0@2 .def_200))) (let ((.def_202 (and 
.def_201 .def_199))) (let ((.def_203 (and .def_202 .def_139))) (let ((.def_204 (not instance.EVENT.1__AT0@0))) (let ((.def_205 (not instance.EVENT.0__AT0@0))) (let ((.def_206 (or .def_205 .def_204))) (let ((.def_207 (= 
event_is_timed__AT0@0 instance.EVENT.1__AT0@0))) (let ((.def_208 (<= time__AT0@0 time__AT0@1))) (let ((.def_209 (or .def_204 .def_208))) (let ((.def_210 (and .def_209 .def_207))) (let ((.def_211 (= time__AT0@0 time__AT0@1))) (let 
((.def_212 (or instance.EVENT.1__AT0@0 .def_211))) (let ((.def_213 (and .def_212 .def_210))) (let ((.def_214 (<= instance.x__AT0@0 0.0))) (let ((.def_215 (not .def_214))) (let ((.def_216 (not instance.location.0__AT0@0))) (let 
((.def_217 (and .def_216 .def_215))) (let ((.def_218 (and instance.location.0__AT0@1 .def_217))) (let ((.def_219 (= instance.x__AT0@0 instance.x__AT0@1))) (let ((.def_220 (and .def_219 .def_218))) (let ((.def_221 (= 
instance.y__AT0@0 instance.y__AT0@1))) (let ((.def_222 (and .def_221 .def_220))) (let ((.def_223 (<= instance.y__AT0@0 0.0))) (let ((.def_224 (and .def_216 .def_223))) (let ((.def_225 (and instance.location.0__AT0@1 .def_224))) 
(let ((.def_226 (and .def_219 .def_225))) (let ((.def_227 (and .def_221 .def_226))) (let ((.def_228 (or .def_227 .def_222))) (let ((.def_229 (and .def_211 .def_228))) (let ((.def_230 (or instance.EVENT.1__AT0@0 .def_229))) (let 
((.def_231 (not .def_211))) (let ((.def_232 (and .def_219 .def_221))) (let ((.def_233 (or .def_232 .def_231))) (let ((.def_234 (and .def_232 .def_233))) (let ((.def_235 (or .def_216 .def_234))) (let ((.def_236 (* (- 1.0) 
time__AT0@0))) (let ((.def_237 (+ .def_236 time__AT0@1))) (let ((.def_238 (exp .def_237))) (let ((.def_239 (* instance.x__AT0@0 .def_238))) (let ((.def_240 (= instance.x__AT0@1 .def_239))) (let ((.def_241 (* 2.0 
instance.x__AT0@0))) (let ((.def_242 (* instance.y__AT0@0 .def_241))) (let ((.def_243 (* (- 1.0) .def_242))) (let ((.def_244 (+ instance.y__AT0@0 .def_243))) (let ((.def_245 (* .def_244 .def_238))) (let ((.def_246 (* (- 1.0) 
.def_245))) (let ((.def_247 (+ .def_246 .def_176))) (let ((.def_248 (+ instance.y__AT0@1 .def_247))) (let ((.def_249 (= .def_248 0.0))) (let ((.def_250 (and .def_249 .def_240))) (let ((.def_251 (and .def_250 .def_233))) (let 
((.def_252 (or instance.location.0__AT0@0 .def_251))) (let ((.def_253 (and .def_252 .def_235))) (let ((.def_254 (and .def_253 .def_208))) (let ((.def_255 (= instance.location.0__AT0@0 instance.location.0__AT0@1))) (let ((.def_256 
(and .def_255 .def_254))) (let ((.def_257 (or .def_204 .def_256))) (let ((.def_258 (and .def_257 .def_230))) (let ((.def_259 (and .def_205 .def_204))) (let ((.def_260 (or .def_259 .def_258))) (let ((.def_261 (and .def_260 
.def_213))) (let ((.def_262 (not .def_259))) (let ((.def_263 (and .def_255 .def_219))) (let ((.def_264 (and .def_263 .def_221))) (let ((.def_265 (or .def_264 .def_262))) (let ((.def_266 (and .def_265 .def_261))) (let ((.def_267 
(not event_is_timed__AT0@0))) (let ((.def_268 (= event_is_timed__AT0@1 .def_267))) (let ((.def_269 (and .def_268 .def_266))) (let ((.def_270 (and .def_269 .def_206))) (let ((.def_271 (= instance.x__AT0@0 (- 1.0)))) (let ((.def_272 
(= instance.y__AT0@0 1.0))) (let ((.def_273 (and .def_272 .def_271))) (let ((.def_274 (and .def_216 .def_273))) (let ((.def_275 (= time__AT0@0 0.0))) (let ((.def_276 (and .def_275 .def_274))) (let ((.def_277 (and .def_276 .def_270 
.def_203 .def_136 .def_69 instance.location.0__AT0@4))) 
.def_277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
