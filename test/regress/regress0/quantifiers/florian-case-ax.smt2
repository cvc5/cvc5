(set-logic AUFLIA)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun A (U U U
  U U U U
  U U U U
  U U U U
  U U U U
  U U U U
  U U U U
  U U U U
  U U U U
  U U U U
  U U U U
  U U U U
  U U U U
  U U U U
  U U
  U) (Array Int U))

(assert
  (forall ((v_184 U) (v_185 U)
  (v_186 U) (v_187 U)
  (v_188 U) (v_189 U)
  (v_190 U) (v_191 U)
  (v_192 U) (v_193 U)
  (v_194 U) (v_195 U)
  (v_196 U) (v_197 U)
  (v_198 U) (v_199 U)
  (v_200 U) (v_201 U)
  (v_202 U) (v_203 U)
  (v_204 U) (v_205 U)
  (v_206 U) (v_207 U)
  (v_208 U) (v_209 U)
  (v_210 U) (v_211 U)
  (v_212 U) (v_213 U)
  (v_214 U) (v_215 U)
  (v_216 U) (v_217 U)
  (v_218 U) (v_219 U)
  (v_220 U) (v_221 U)
  (v_222 U) (v_223 U)
  (v_224 U) (v_225 U)
  (v_226 U) (v_227 U)
  (v_228 U) (v_229 U)
  (v_230 U) (v_231 U)
  (v_232 U) (v_233 U)
  (v_234 U) (v_235 U)
  (v_236 U) (v_237 U)
  (v_238 U) (v_239 U)
  (v_240 U) (v_241 U) (v_242 Int))
  (let ((v_183 (A v_184 v_185 v_186 v_187
                    v_188 v_189 v_190 v_191 v_192
                    v_193 v_194 v_195 v_196 v_197
                    v_198 v_199 v_200 v_201 v_202
                    v_203 v_204 v_205 v_206 v_207
                    v_208 v_209 v_210 v_211 v_212
                    v_213 v_214 v_215 v_216 v_217
                    v_218 v_219 v_220 v_221 v_222
                    v_223 v_224 v_225 v_226 v_227
                    v_228 v_229 v_230 v_231 v_232
                    v_233 v_234 v_235 v_236 v_237
                    v_238 v_239 v_240 v_241)))
  (ite (= v_242 59) (= (select v_183 v_242) v_240)
  (ite (= v_242 58) (= (select v_183 v_242) v_239)
  (ite (= v_242 57) (= (select v_183 v_242) v_238)
  (ite (= v_242 56) (= (select v_183 v_242) v_237)
  (ite (= v_242 55) (= (select v_183 v_242) v_236)
  (ite (= v_242 54) (= (select v_183 v_242) v_235)
  (ite (= v_242 53) (= (select v_183 v_242) v_234)
  (ite (= v_242 52) (= (select v_183 v_242) v_233)
  (ite (= v_242 51) (= (select v_183 v_242) v_232)
  (ite (= v_242 50) (= (select v_183 v_242) v_231)
  (ite (= v_242 49) (= (select v_183 v_242) v_230)
  (ite (= v_242 48) (= (select v_183 v_242) v_229)
  (ite (= v_242 47) (= (select v_183 v_242) v_228)
  (ite (= v_242 46) (= (select v_183 v_242) v_227)
  (ite (= v_242 45) (= (select v_183 v_242) v_226)
  (ite (= v_242 44) (= (select v_183 v_242) v_225)
  (ite (= v_242 43) (= (select v_183 v_242) v_224)
  (ite (= v_242 41) (= (select v_183 v_242) v_223)
  (ite (= v_242 40) (= (select v_183 v_242) v_222)
  (ite (= v_242 39) (= (select v_183 v_242) v_221)
  (ite (= v_242 37) (= (select v_183 v_242) v_220)
  (ite (= v_242 36) (= (select v_183 v_242) v_219)
  (ite (= v_242 34) (= (select v_183 v_242) v_218)
  (ite (= v_242 33) (= (select v_183 v_242) v_217)
  (ite (= v_242 32) (= (select v_183 v_242) v_216)
  (ite (= v_242 31) (= (select v_183 v_242) v_215)
  (ite (= v_242 30) (= (select v_183 v_242) v_214)
  (ite (= v_242 29) (= (select v_183 v_242) v_213)
  (ite (= v_242 28) (= (select v_183 v_242) v_212)
  (ite (= v_242 27) (= (select v_183 v_242) v_211)
  (ite (= v_242 26) (= (select v_183 v_242) v_210)
  (ite (= v_242 25) (= (select v_183 v_242) v_209)
  (ite (= v_242 24) (= (select v_183 v_242) v_208)
  (ite (= v_242 23) (= (select v_183 v_242) v_207)
  (ite (= v_242 22) (= (select v_183 v_242) v_206)
  (ite (= v_242 21) (= (select v_183 v_242) v_205)
  (ite (= v_242 20) (= (select v_183 v_242) v_204)
  (ite (= v_242 19) (= (select v_183 v_242) v_203)
  (ite (= v_242 18) (= (select v_183 v_242) v_202)
  (ite (= v_242 17) (= (select v_183 v_242) v_201)
  (ite (= v_242 16) (= (select v_183 v_242) v_200)
  (ite (= v_242 15) (= (select v_183 v_242) v_199)
  (ite (= v_242 14) (= (select v_183 v_242) v_198)
  (ite (= v_242 13) (= (select v_183 v_242) v_197)
  (ite (= v_242 12) (= (select v_183 v_242) v_196)
  (ite (= v_242 11) (= (select v_183 v_242) v_195)
  (ite (= v_242 10) (= (select v_183 v_242) v_194)
  (ite (= v_242 9) (= (select v_183 v_242) v_193)
  (ite (= v_242 8) (= (select v_183 v_242) v_192)
  (ite (= v_242 7) (= (select v_183 v_242) v_191)
  (ite (= v_242 6) (= (select v_183 v_242) v_190)
  (ite (= v_242 5) (= (select v_183 v_242) v_189)
  (ite (= v_242 4) (= (select v_183 v_242) v_188)
  (ite (= v_242 3) (= (select v_183 v_242) v_187)
  (ite (= v_242 2) (= (select v_183 v_242) v_186)
  (ite (= v_242 1) (= (select v_183 v_242) v_185)
  (ite (= v_242 0) (= (select v_183 v_242) v_184)
  (= (select v_183 v_242) v_241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  
(declare-const c_184 U) (declare-const c_185 U)
(declare-const c_186 U) (declare-const c_187 U)
(declare-const c_188 U) (declare-const c_189 U)
(declare-const c_190 U) (declare-const c_191 U)
(declare-const c_192 U) (declare-const c_193 U)
(declare-const c_194 U) (declare-const c_195 U)
(declare-const c_196 U) (declare-const c_197 U)
(declare-const c_198 U) (declare-const c_199 U)
(declare-const c_200 U) (declare-const c_201 U)
(declare-const c_202 U) (declare-const c_203 U)
(declare-const c_204 U) (declare-const c_205 U)
(declare-const c_206 U) (declare-const c_207 U)
(declare-const c_208 U) (declare-const c_209 U)
(declare-const c_210 U) (declare-const c_211 U)
(declare-const c_212 U) (declare-const c_213 U)
(declare-const c_214 U) (declare-const c_215 U)
(declare-const c_216 U) (declare-const c_217 U)
(declare-const c_218 U) (declare-const c_219 U)
(declare-const c_220 U) (declare-const c_221 U)
(declare-const c_222 U) (declare-const c_223 U)
(declare-const c_224 U) (declare-const c_225 U)
(declare-const c_226 U) (declare-const c_227 U)
(declare-const c_228 U) (declare-const c_229 U)
(declare-const c_230 U) (declare-const c_231 U)
(declare-const c_232 U) (declare-const c_233 U)
(declare-const c_234 U) (declare-const c_235 U)
(declare-const c_236 U) (declare-const c_237 U)
(declare-const c_238 U) (declare-const c_239 U)
(declare-const c_240 U) (declare-const c_241 U)
  
(declare-fun b () Int)
(declare-fun c () U)
(assert (not (= (select (A c_184 c_185 c_186 c_187
                          c_188 c_189 c_190 c_191 c_192
                          c_193 c_194 c_195 c_196 c_197
                          c_198 c_199 c_200 c_201 c_202
                          c_203 c_204 c_205 c_206 c_207
                          c_208 c_209 c_210 c_211 c_212
                          c_213 c_214 c_215 c_216 c_217
                          c_218 c_219 c_220 c_221 c_222
                          c_223 c_224 c_225 c_226 c_227
                          c_228 c_229 c_230 c_231 c_232
                          c_233 c_234 c_235 c_236 c_237
                          c_238 c_239 c_240 c_241) b) c)))
(assert (and (= b 28) (= c c_212)))

(check-sat)
