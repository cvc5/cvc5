; COMMAND-LINE: -i -q
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-sort |T@[Int]Int| 0)
(declare-datatypes ((T@Vec_2846 0)) (((Vec_2846 (|v#Vec_2846| |T@[Int]Int|) (|l#Vec_2846| Int) ) ) ))
(declare-datatypes ((T@$Location 0)) ((($Global (|a#$Global| Int) ) ($Local (|i#$Local| Int) ) ($Param (|i#$Param| Int) ) ) ))
(declare-datatypes ((T@$Path 0)) ((($Path (|p#$Path| |T@[Int]Int|) (|size#$Path| Int) ) ) ))
(declare-datatypes ((T@$Mutation_3470 0)) ((($Mutation_3470 (|l#$Mutation_3470| T@$Location) (|p#$Mutation_3470| T@$Path) (|v#$Mutation_3470| Int) ) ) ))
(declare-datatypes ((T@$Mutation_8806 0)) ((($Mutation_8806 (|l#$Mutation_8806| T@$Location) (|p#$Mutation_8806| T@$Path) (|v#$Mutation_8806| T@Vec_2846) ) ) ))
(declare-datatypes ((T@$Range 0)) ((($Range (|lb#$Range| Int) (|ub#$Range| Int) ) ) ))
(declare-fun $MAX_U8 () Int)
(declare-fun $MAX_U64 () Int)
(declare-fun $MAX_U128 () Int)
(declare-fun |$IsValid'u8'| (Int) Bool)
(declare-fun |$IsValid'u64'| (Int) Bool)
(declare-fun |$IsValid'u128'| (Int) Bool)
(declare-fun |$IsValid'num'| (Int) Bool)
(declare-fun |$IsValid'address'| (Int) Bool)
(declare-fun $InRange (T@$Range Int) Bool)
(declare-fun $EmptyPath () T@$Path)
(declare-sort |T@[Int]Bool| 0)
(declare-fun $ConstMemoryDomain (Bool) |T@[Int]Bool|)
(declare-fun |lambda#0| (Bool) |T@[Int]Bool|)
(declare-fun $EXEC_FAILURE_CODE () Int)
(declare-fun $shl (Int Int) Int)
(declare-fun $shr (Int Int) Int)
(declare-fun |$IsEqual'vec'u64''| (T@Vec_2846 T@Vec_2846) Bool)
(declare-fun InRangeVec_2846 (T@Vec_2846 Int) Bool)
(declare-fun |Select__T@[Int]Int_| (|T@[Int]Int| Int) Int)
(declare-fun |$IsValid'vec'u64''| (T@Vec_2846) Bool)
(declare-fun |$IndexOfVec'u64'| (T@Vec_2846 Int) Int)
(declare-fun |$IsEqual'vec'u8''| (T@Vec_2846 T@Vec_2846) Bool)
(declare-fun |$IsValid'vec'u8''| (T@Vec_2846) Bool)
(declare-fun |$IndexOfVec'u8'| (T@Vec_2846 Int) Int)
(declare-fun $Hash_sha2 (T@Vec_2846) T@Vec_2846)
(declare-fun $Hash_sha3 (T@Vec_2846) T@Vec_2846)
(declare-fun $Signature_$ed25519_validate_pubkey (T@Vec_2846) Bool)
(declare-fun $Signature_$ed25519_verify (T@Vec_2846 T@Vec_2846 T@Vec_2846) Bool)
(declare-fun IndexOfVec_2846 (T@Vec_2846 Int) Int)
(declare-fun |Select__T@[Int]Bool_| (|T@[Int]Bool| Int) Bool)
(declare-fun |lambda#2| (Int Int Int |T@[Int]Int| |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun |lambda#3| (Int Int |T@[Int]Int| Int Int Int) |T@[Int]Int|)
(declare-fun |lambda#4| (Int Int Int |T@[Int]Int| |T@[Int]Int| Int Int) |T@[Int]Int|)
(assert (= $MAX_U8 255))
(assert (= $MAX_U64 18446744073709551615))
(assert (= $MAX_U128 340282366920938463463374607431768211455))
(assert (forall ((v Int) ) (! (= (|$IsValid'u8'| v)  (and (>= v 0) (<= v $MAX_U8)))
 :qid |outputbpl.190:23|
 :skolemid |6|
 :pattern ( (|$IsValid'u8'| v))
)))
(assert (forall ((v@@0 Int) ) (! (= (|$IsValid'u64'| v@@0)  (and (>= v@@0 0) (<= v@@0 $MAX_U64)))
 :qid |outputbpl.194:24|
 :skolemid |7|
 :pattern ( (|$IsValid'u64'| v@@0))
)))
(assert (forall ((v@@1 Int) ) (! (= (|$IsValid'u128'| v@@1)  (and (>= v@@1 0) (<= v@@1 $MAX_U128)))
 :qid |outputbpl.198:25|
 :skolemid |8|
 :pattern ( (|$IsValid'u128'| v@@1))
)))
(assert (forall ((v@@2 Int) ) (! (= (|$IsValid'num'| v@@2) true)
 :qid |outputbpl.202:24|
 :skolemid |9|
 :pattern ( (|$IsValid'num'| v@@2))
)))
(assert (forall ((v@@3 Int) ) (! (= (|$IsValid'address'| v@@3) (>= v@@3 0))
 :qid |outputbpl.206:28|
 :skolemid |10|
 :pattern ( (|$IsValid'address'| v@@3))
)))
(assert (forall ((r T@$Range) (i Int) ) (! (= ($InRange r i)  (and (<= (|lb#$Range| r) i) (< i (|ub#$Range| r))))
 :qid |outputbpl.216:19|
 :skolemid |11|
 :pattern ( ($InRange r i))
)))
(assert (= (|size#$Path| $EmptyPath) 0))
(assert (= ($ConstMemoryDomain false) (|lambda#0| false)))
(assert (= ($ConstMemoryDomain true) (|lambda#0| true)))
(assert (= $EXEC_FAILURE_CODE (- 0 1)))
(assert (forall ((src1 Int) (p Int) ) (! (= ($shl src1 p) (ite (= p 8) (* src1 256) (ite (= p 16) (* src1 65536) (ite (= p 32) (* src1 4294967296) (ite (= p 64) (* src1 18446744073709551616) (- 0 1))))))
 :qid |outputbpl.469:15|
 :skolemid |12|
 :pattern ( ($shl src1 p))
)))
(assert (forall ((src1@@0 Int) (p@@0 Int) ) (! (= ($shr src1@@0 p@@0) (ite (= p@@0 8) (div src1@@0 256) (ite (= p@@0 16) (div src1@@0 65536) (ite (= p@@0 32) (div src1@@0 4294967296) (ite (= p@@0 64) (div src1@@0 18446744073709551616) (- 0 1))))))
 :qid |outputbpl.478:15|
 :skolemid |13|
 :pattern ( ($shr src1@@0 p@@0))
)))
(assert (forall ((v1 T@Vec_2846) (v2 T@Vec_2846) ) (! (= (|$IsEqual'vec'u64''| v1 v2)  (and (= (|l#Vec_2846| v1) (|l#Vec_2846| v2)) (forall ((i@@0 Int) ) (!  (=> (InRangeVec_2846 v1 i@@0) (= (|Select__T@[Int]Int_| (|v#Vec_2846| v1) i@@0) (|Select__T@[Int]Int_| (|v#Vec_2846| v2) i@@0)))
 :qid |outputbpl.602:13|
 :skolemid |14|
))))
 :qid |outputbpl.600:29|
 :skolemid |15|
 :pattern ( (|$IsEqual'vec'u64''| v1 v2))
)))
(assert (forall ((v@@4 T@Vec_2846) ) (! (= (|$IsValid'vec'u64''| v@@4)  (and (|$IsValid'u64'| (|l#Vec_2846| v@@4)) (forall ((i@@1 Int) ) (!  (=> (InRangeVec_2846 v@@4 i@@1) (|$IsValid'u64'| (|Select__T@[Int]Int_| (|v#Vec_2846| v@@4) i@@1)))
 :qid |outputbpl.608:13|
 :skolemid |16|
))))
 :qid |outputbpl.606:29|
 :skolemid |17|
 :pattern ( (|$IsValid'vec'u64''| v@@4))
)))
(assert (forall ((v@@5 T@Vec_2846) (e Int) ) (! (let ((i@@2 (|$IndexOfVec'u64'| v@@5 e)))
(ite  (not (exists ((i@@3 Int) ) (!  (and (and (|$IsValid'u64'| i@@3) (InRangeVec_2846 v@@5 i@@3)) (= (|Select__T@[Int]Int_| (|v#Vec_2846| v@@5) i@@3) e))
 :qid |outputbpl.613:13|
 :skolemid |18|
))) (= i@@2 (- 0 1))  (and (and (and (|$IsValid'u64'| i@@2) (InRangeVec_2846 v@@5 i@@2)) (= (|Select__T@[Int]Int_| (|v#Vec_2846| v@@5) i@@2) e)) (forall ((j Int) ) (!  (=> (and (and (|$IsValid'u64'| j) (>= j 0)) (< j i@@2)) (not (= (|Select__T@[Int]Int_| (|v#Vec_2846| v@@5) j) e)))
 :qid |outputbpl.621:17|
 :skolemid |19|
)))))
 :qid |outputbpl.617:15|
 :skolemid |20|
 :pattern ( (|$IndexOfVec'u64'| v@@5 e))
)))
(assert (forall ((v1@@0 T@Vec_2846) (v2@@0 T@Vec_2846) ) (! (= (|$IsEqual'vec'u8''| v1@@0 v2@@0)  (and (= (|l#Vec_2846| v1@@0) (|l#Vec_2846| v2@@0)) (forall ((i@@4 Int) ) (!  (=> (InRangeVec_2846 v1@@0 i@@4) (= (|Select__T@[Int]Int_| (|v#Vec_2846| v1@@0) i@@4) (|Select__T@[Int]Int_| (|v#Vec_2846| v2@@0) i@@4)))
 :qid |outputbpl.789:13|
 :skolemid |21|
))))
 :qid |outputbpl.787:28|
 :skolemid |22|
 :pattern ( (|$IsEqual'vec'u8''| v1@@0 v2@@0))
)))
(assert (forall ((v@@6 T@Vec_2846) ) (! (= (|$IsValid'vec'u8''| v@@6)  (and (|$IsValid'u64'| (|l#Vec_2846| v@@6)) (forall ((i@@5 Int) ) (!  (=> (InRangeVec_2846 v@@6 i@@5) (|$IsValid'u8'| (|Select__T@[Int]Int_| (|v#Vec_2846| v@@6) i@@5)))
 :qid |outputbpl.795:13|
 :skolemid |23|
))))
 :qid |outputbpl.793:28|
 :skolemid |24|
 :pattern ( (|$IsValid'vec'u8''| v@@6))
)))
(assert (forall ((v@@7 T@Vec_2846) (e@@0 Int) ) (! (let ((i@@6 (|$IndexOfVec'u8'| v@@7 e@@0)))
(ite  (not (exists ((i@@7 Int) ) (!  (and (and (|$IsValid'u64'| i@@7) (InRangeVec_2846 v@@7 i@@7)) (= (|Select__T@[Int]Int_| (|v#Vec_2846| v@@7) i@@7) e@@0))
 :qid |outputbpl.800:13|
 :skolemid |25|
))) (= i@@6 (- 0 1))  (and (and (and (|$IsValid'u64'| i@@6) (InRangeVec_2846 v@@7 i@@6)) (= (|Select__T@[Int]Int_| (|v#Vec_2846| v@@7) i@@6) e@@0)) (forall ((j@@0 Int) ) (!  (=> (and (and (|$IsValid'u64'| j@@0) (>= j@@0 0)) (< j@@0 i@@6)) (not (= (|Select__T@[Int]Int_| (|v#Vec_2846| v@@7) j@@0) e@@0)))
 :qid |outputbpl.808:17|
 :skolemid |26|
)))))
 :qid |outputbpl.804:15|
 :skolemid |27|
 :pattern ( (|$IndexOfVec'u8'| v@@7 e@@0))
)))
(assert (forall ((v1@@1 T@Vec_2846) (v2@@1 T@Vec_2846) ) (! (= (|$IsEqual'vec'u8''| v1@@1 v2@@1) (|$IsEqual'vec'u8''| ($Hash_sha2 v1@@1) ($Hash_sha2 v2@@1)))
 :qid |outputbpl.987:15|
 :skolemid |28|
 :pattern ( ($Hash_sha2 v1@@1) ($Hash_sha2 v2@@1))
)))
(assert (forall ((v1@@2 T@Vec_2846) (v2@@2 T@Vec_2846) ) (! (= (|$IsEqual'vec'u8''| v1@@2 v2@@2) (|$IsEqual'vec'u8''| ($Hash_sha3 v1@@2) ($Hash_sha3 v2@@2)))
 :qid |outputbpl.1003:15|
 :skolemid |29|
 :pattern ( ($Hash_sha3 v1@@2) ($Hash_sha3 v2@@2))
)))
(assert (forall ((k1 T@Vec_2846) (k2 T@Vec_2846) ) (!  (=> (|$IsEqual'vec'u8''| k1 k2) (= ($Signature_$ed25519_validate_pubkey k1) ($Signature_$ed25519_validate_pubkey k2)))
 :qid |outputbpl.1050:15|
 :skolemid |30|
 :pattern ( ($Signature_$ed25519_validate_pubkey k1) ($Signature_$ed25519_validate_pubkey k2))
)))
(assert (forall ((s1 T@Vec_2846) (s2 T@Vec_2846) (k1@@0 T@Vec_2846) (k2@@0 T@Vec_2846) (m1 T@Vec_2846) (m2 T@Vec_2846) ) (!  (=> (and (and (|$IsEqual'vec'u8''| s1 s2) (|$IsEqual'vec'u8''| k1@@0 k2@@0)) (|$IsEqual'vec'u8''| m1 m2)) (= ($Signature_$ed25519_verify s1 k1@@0 m1) ($Signature_$ed25519_verify s2 k2@@0 m2)))
 :qid |outputbpl.1053:15|
 :skolemid |31|
 :pattern ( ($Signature_$ed25519_verify s1 k1@@0 m1) ($Signature_$ed25519_verify s2 k2@@0 m2))
)))
(assert (forall ((v@@8 T@Vec_2846) (i@@8 Int) ) (! (= (InRangeVec_2846 v@@8 i@@8)  (and (>= i@@8 0) (< i@@8 (|l#Vec_2846| v@@8))))
 :qid |outputbpl.122:24|
 :skolemid |3|
 :pattern ( (InRangeVec_2846 v@@8 i@@8))
)))
(assert (forall ((v@@9 T@Vec_2846) (e@@1 Int) ) (! (let ((i@@9 (IndexOfVec_2846 v@@9 e@@1)))
(ite  (not (exists ((i@@10 Int) ) (!  (and (InRangeVec_2846 v@@9 i@@10) (= (|Select__T@[Int]Int_| (|v#Vec_2846| v@@9) i@@10) e@@1))
 :qid |outputbpl.109:13|
 :skolemid |0|
))) (= i@@9 (- 0 1))  (and (and (InRangeVec_2846 v@@9 i@@9) (= (|Select__T@[Int]Int_| (|v#Vec_2846| v@@9) i@@9) e@@1)) (forall ((j@@1 Int) ) (!  (=> (and (>= j@@1 0) (< j@@1 i@@9)) (not (= (|Select__T@[Int]Int_| (|v#Vec_2846| v@@9) j@@1) e@@1)))
 :qid |outputbpl.117:17|
 :skolemid |1|
)))))
 :qid |outputbpl.113:32|
 :skolemid |2|
 :pattern ( (IndexOfVec_2846 v@@9 e@@1))
)))
(assert (forall ((|l#0| Bool) (i@@11 Int) ) (! (= (|Select__T@[Int]Bool_| (|lambda#0| |l#0|) i@@11) |l#0|)
 :qid |outputbpl.288:54|
 :skolemid |36|
 :pattern ( (|Select__T@[Int]Bool_| (|lambda#0| |l#0|) i@@11))
)))
(assert (forall ((|l#0@@0| Int) (|l#1| Int) (|l#2| Int) (|l#3| |T@[Int]Int|) (|l#4| |T@[Int]Int|) (|l#5| Int) (|l#6| Int) (i@@12 Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#2| |l#0@@0| |l#1| |l#2| |l#3| |l#4| |l#5| |l#6|) i@@12) (ite  (and (>= i@@12 |l#0@@0|) (< i@@12 |l#1|)) (ite (< i@@12 |l#2|) (|Select__T@[Int]Int_| |l#3| i@@12) (|Select__T@[Int]Int_| |l#4| (- i@@12 |l#5|))) |l#6|))
 :qid |outputbpl.73:19|
 :skolemid |37|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#2| |l#0@@0| |l#1| |l#2| |l#3| |l#4| |l#5| |l#6|) i@@12))
)))
(assert (forall ((|l#0@@1| Int) (|l#1@@0| Int) (|l#2@@0| |T@[Int]Int|) (|l#3@@0| Int) (|l#4@@0| Int) (|l#5@@0| Int) (i@@13 Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#3| |l#0@@1| |l#1@@0| |l#2@@0| |l#3@@0| |l#4@@0| |l#5@@0|) i@@13) (ite  (and (<= |l#0@@1| i@@13) (< i@@13 |l#1@@0|)) (|Select__T@[Int]Int_| |l#2@@0| (- (- |l#3@@0| i@@13) |l#4@@0|)) |l#5@@0|))
 :qid |outputbpl.82:30|
 :skolemid |38|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#3| |l#0@@1| |l#1@@0| |l#2@@0| |l#3@@0| |l#4@@0| |l#5@@0|) i@@13))
)))
(assert (forall ((|l#0@@2| Int) (|l#1@@1| Int) (|l#2@@1| Int) (|l#3@@1| |T@[Int]Int|) (|l#4@@1| |T@[Int]Int|) (|l#5@@1| Int) (|l#6@@0| Int) (j@@2 Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#4| |l#0@@2| |l#1@@1| |l#2@@1| |l#3@@1| |l#4@@1| |l#5@@1| |l#6@@0|) j@@2) (ite  (and (>= j@@2 |l#0@@2|) (< j@@2 |l#1@@1|)) (ite (< j@@2 |l#2@@1|) (|Select__T@[Int]Int_| |l#3@@1| j@@2) (|Select__T@[Int]Int_| |l#4@@1| (+ j@@2 |l#5@@1|))) |l#6@@0|))
 :qid |outputbpl.63:20|
 :skolemid |39|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#4| |l#0@@2| |l#1@@1| |l#2@@1| |l#3@@1| |l#4@@1| |l#5@@1| |l#6@@0|) j@@2))
)))
(declare-fun ControlFlow (Int Int) Int)
(declare-fun $t0@5 () T@Vec_2846)
(declare-fun |inline$$Vector_push_back'u64'$2$m'@1| () T@$Mutation_8806)
(declare-fun $t0@3 () T@Vec_2846)
(declare-fun $t0@4 () T@Vec_2846)
(declare-fun $t6@0 () T@$Mutation_8806)
(declare-fun |Store__T@[Int]Int_| (|T@[Int]Int| Int Int) |T@[Int]Int|)
(assert (forall ( ( ?x0 |T@[Int]Int|) ( ?x1 Int) ( ?x2 Int)) (! (= (|Select__T@[Int]Int_| (|Store__T@[Int]Int_| ?x0 ?x1 ?x2) ?x1)  ?x2) :weight 0)))
(assert (forall ( ( ?x0 |T@[Int]Int|) ( ?x1 Int) ( ?y1 Int) ( ?x2 Int)) (! (=>  (not (= ?x1 ?y1)) (= (|Select__T@[Int]Int_| (|Store__T@[Int]Int_| ?x0 ?x1 ?x2) ?y1) (|Select__T@[Int]Int_| ?x0 ?y1))) :weight 0)))
(declare-fun |inline$$Vector_push_back'u64'$1$m'@1| () T@$Mutation_8806)
(declare-fun $t0@1 () T@Vec_2846)
(declare-fun $t0@2 () T@Vec_2846)
(declare-fun $t4@0 () T@$Mutation_8806)
(declare-fun |inline$$Vector_push_back'u64'$0$m'@1| () T@$Mutation_8806)
(declare-fun |inline$$Vector_empty'u64'$0$v@1| () T@Vec_2846)
(declare-fun $t0@0 () T@Vec_2846)
(declare-fun $t2@0 () T@$Mutation_8806)
(declare-fun MapConstVec_3075 (Int) |T@[Int]Int|)
(declare-fun DefaultVecElem_3075 () Int)
(push 1)
(set-info :boogie-vc-id $TestQuantInvariant_vector_of_proper_positives$verify)
(assert (not
 (=> (= (ControlFlow 0 0) 14811) (let ((anon14_correct  (=> (= $t0@5 $t0@5) (and (=> (= (ControlFlow 0 14024) (- 0 15219)) (not false)) (=> (not false) (and (=> (= (ControlFlow 0 14024) (- 0 15226)) (let (($range_0 $t0@5))
(forall (($i_1 Int) ) (!  (=> (InRangeVec_2846 $range_0 $i_1) (let ((n (|Select__T@[Int]Int_| (|v#Vec_2846| $range_0) $i_1)))
(> n 0)))
 :qid |outputbpl.1223:37|
 :skolemid |32|
)))) (=> (let (($range_0 $t0@5))
(forall (($i_1@@0 Int) ) (!  (=> (InRangeVec_2846 $range_0 $i_1@@0) (let ((n (|Select__T@[Int]Int_| (|v#Vec_2846| $range_0) $i_1@@0)))
(> n 0)))
 :qid |outputbpl.1223:37|
 :skolemid |32|
))) (and (=> (= (ControlFlow 0 14024) (- 0 15257)) (let (($range_0@@0 ($Range 0 (|l#Vec_2846| $t0@5))))
(let (($range_1 ($Range 0 (|l#Vec_2846| $t0@5))))
(forall (($i_2 Int) ($i_3 Int) ) (!  (=> ($InRange $range_0@@0 $i_2) (=> ($InRange $range_1 $i_3) (let ((i@@14 $i_2))
(let ((j@@3 $i_3))
 (=> (= (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) i@@14) (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) j@@3)) (= i@@14 j@@3))))))
 :qid |outputbpl.1229:97|
 :skolemid |33|
))))) (=> (let (($range_0@@0 ($Range 0 (|l#Vec_2846| $t0@5))))
(let (($range_1 ($Range 0 (|l#Vec_2846| $t0@5))))
(forall (($i_2@@0 Int) ($i_3@@0 Int) ) (!  (=> ($InRange $range_0@@0 $i_2@@0) (=> ($InRange $range_1 $i_3@@0) (let ((i@@14 $i_2@@0))
(let ((j@@3 $i_3@@0))
 (=> (= (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) i@@14) (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) j@@3)) (= i@@14 j@@3))))))
 :qid |outputbpl.1229:97|
 :skolemid |33|
)))) (and (=> (= (ControlFlow 0 14024) (- 0 15325)) (forall ((i@@15 Int) (j@@4 Int) ) (!  (=> (|$IsValid'u64'| i@@15) (=> (|$IsValid'u64'| j@@4) (=> (and (and (and (and (= (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) i@@15) (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) j@@4)) (>= i@@15 0)) (< i@@15 (|l#Vec_2846| $t0@5))) (>= j@@4 0)) (< j@@4 (|l#Vec_2846| $t0@5))) (= i@@15 j@@4))))
 :qid |outputbpl.1236:15|
 :skolemid |34|
 :pattern ( (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) i@@15) (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) j@@4))
))) (=> (forall ((i@@16 Int) (j@@5 Int) ) (!  (=> (|$IsValid'u64'| i@@16) (=> (|$IsValid'u64'| j@@5) (=> (and (and (and (and (= (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) i@@16) (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) j@@5)) (>= i@@16 0)) (< i@@16 (|l#Vec_2846| $t0@5))) (>= j@@5 0)) (< j@@5 (|l#Vec_2846| $t0@5))) (= i@@16 j@@5))))
 :qid |outputbpl.1236:15|
 :skolemid |34|
 :pattern ( (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) i@@16) (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) j@@5))
)) (=> (= (ControlFlow 0 14024) (- 0 15408)) (let (($range_0@@1 ($Range 0 (|l#Vec_2846| $t0@5))))
(forall (($i_1@@1 Int) ) (!  (=> ($InRange $range_0@@1 $i_1@@1) (let ((i@@17 $i_1@@1))
(let ((i@@18 (|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) i@@17)))
(> i@@18 0))))
 :qid |outputbpl.1241:56|
 :skolemid |35|
 :pattern ( (let ((i@@19 $i_1@@1))
(|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) i@@19)) (let ((i@@20 $i_1@@1))
(|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) i@@20)))
 :pattern ( (let ((i@@21 $i_1@@1))
(|Select__T@[Int]Int_| (|v#Vec_2846| $t0@5) i@@21)))
)))))))))))))))
(let ((anon22_Else_correct  (=> (not (= (|l#$Mutation_8806| |inline$$Vector_push_back'u64'$2$m'@1|) ($Local 0))) (=> (and (= $t0@5 $t0@3) (= (ControlFlow 0 13738) 14024)) anon14_correct))))
(let ((anon22_Then_correct  (=> (and (and (= (|l#$Mutation_8806| |inline$$Vector_push_back'u64'$2$m'@1|) ($Local 0)) (= $t0@4 (|v#$Mutation_8806| |inline$$Vector_push_back'u64'$2$m'@1|))) (and (= $t0@5 $t0@4) (= (ControlFlow 0 14036) 14024))) anon14_correct)))
(let ((anon21_Else_correct  (=> (not false) (and (=> (= (ControlFlow 0 13728) 14036) anon22_Then_correct) (=> (= (ControlFlow 0 13728) 13738) anon22_Else_correct)))))
(let ((anon21_Then_correct true))
(let ((|inline$$Vector_push_back'u64'$2$anon0_correct|  (=> (= |inline$$Vector_push_back'u64'$2$m'@1| ($Mutation_8806 (|l#$Mutation_8806| $t6@0) (|p#$Mutation_8806| $t6@0) (let ((l (|l#Vec_2846| (|v#$Mutation_8806| $t6@0))))
(Vec_2846 (|Store__T@[Int]Int_| (|v#Vec_2846| (|v#$Mutation_8806| $t6@0)) l 3) (+ l 1))))) (and (=> (= (ControlFlow 0 13714) 14050) anon21_Then_correct) (=> (= (ControlFlow 0 13714) 13728) anon21_Else_correct)))))
(let ((anon10_correct  (=> (= $t6@0 ($Mutation_8806 ($Local 0) $EmptyPath $t0@3)) (=> (and (|$IsValid'u64'| 3) (= (ControlFlow 0 13720) 13714)) |inline$$Vector_push_back'u64'$2$anon0_correct|))))
(let ((anon20_Else_correct  (=> (not (= (|l#$Mutation_8806| |inline$$Vector_push_back'u64'$1$m'@1|) ($Local 0))) (=> (and (= $t0@3 $t0@1) (= (ControlFlow 0 13643) 13720)) anon10_correct))))
(let ((anon20_Then_correct  (=> (and (and (= (|l#$Mutation_8806| |inline$$Vector_push_back'u64'$1$m'@1|) ($Local 0)) (= $t0@2 (|v#$Mutation_8806| |inline$$Vector_push_back'u64'$1$m'@1|))) (and (= $t0@3 $t0@2) (= (ControlFlow 0 14072) 13720))) anon10_correct)))
(let ((anon19_Else_correct  (=> (not false) (and (=> (= (ControlFlow 0 13633) 14072) anon20_Then_correct) (=> (= (ControlFlow 0 13633) 13643) anon20_Else_correct)))))
(let ((anon19_Then_correct true))
(let ((|inline$$Vector_push_back'u64'$1$anon0_correct|  (=> (= |inline$$Vector_push_back'u64'$1$m'@1| ($Mutation_8806 (|l#$Mutation_8806| $t4@0) (|p#$Mutation_8806| $t4@0) (let ((l@@0 (|l#Vec_2846| (|v#$Mutation_8806| $t4@0))))
(Vec_2846 (|Store__T@[Int]Int_| (|v#Vec_2846| (|v#$Mutation_8806| $t4@0)) l@@0 2) (+ l@@0 1))))) (and (=> (= (ControlFlow 0 13619) 14086) anon19_Then_correct) (=> (= (ControlFlow 0 13619) 13633) anon19_Else_correct)))))
(let ((anon6_correct  (=> (= $t4@0 ($Mutation_8806 ($Local 0) $EmptyPath $t0@1)) (=> (and (|$IsValid'u64'| 2) (= (ControlFlow 0 13625) 13619)) |inline$$Vector_push_back'u64'$1$anon0_correct|))))
(let ((anon18_Else_correct  (=> (not (= (|l#$Mutation_8806| |inline$$Vector_push_back'u64'$0$m'@1|) ($Local 0))) (=> (and (= $t0@1 |inline$$Vector_empty'u64'$0$v@1|) (= (ControlFlow 0 13548) 13625)) anon6_correct))))
(let ((anon18_Then_correct  (=> (and (and (= (|l#$Mutation_8806| |inline$$Vector_push_back'u64'$0$m'@1|) ($Local 0)) (= $t0@0 (|v#$Mutation_8806| |inline$$Vector_push_back'u64'$0$m'@1|))) (and (= $t0@1 $t0@0) (= (ControlFlow 0 14098) 13625))) anon6_correct)))
(let ((anon17_Else_correct  (=> (not false) (and (=> (= (ControlFlow 0 13538) 14098) anon18_Then_correct) (=> (= (ControlFlow 0 13538) 13548) anon18_Else_correct)))))
(let ((anon17_Then_correct true))
(let ((|inline$$Vector_push_back'u64'$0$anon0_correct|  (=> (= |inline$$Vector_push_back'u64'$0$m'@1| ($Mutation_8806 (|l#$Mutation_8806| $t2@0) (|p#$Mutation_8806| $t2@0) (let ((l@@1 (|l#Vec_2846| (|v#$Mutation_8806| $t2@0))))
(Vec_2846 (|Store__T@[Int]Int_| (|v#Vec_2846| (|v#$Mutation_8806| $t2@0)) l@@1 1) (+ l@@1 1))))) (and (=> (= (ControlFlow 0 13524) 14112) anon17_Then_correct) (=> (= (ControlFlow 0 13524) 13538) anon17_Else_correct)))))
(let ((anon16_Else_correct  (=> (not false) (=> (and (and (= |inline$$Vector_empty'u64'$0$v@1| |inline$$Vector_empty'u64'$0$v@1|) (= $t2@0 ($Mutation_8806 ($Local 0) $EmptyPath |inline$$Vector_empty'u64'$0$v@1|))) (and (|$IsValid'u64'| 1) (= (ControlFlow 0 13530) 13524))) |inline$$Vector_push_back'u64'$0$anon0_correct|))))
(let ((anon16_Then_correct true))
(let ((|inline$$Vector_empty'u64'$0$anon0_correct|  (=> (= |inline$$Vector_empty'u64'$0$v@1| (Vec_2846 (MapConstVec_3075 DefaultVecElem_3075) 0)) (and (=> (= (ControlFlow 0 13435) 14126) anon16_Then_correct) (=> (= (ControlFlow 0 13435) 13530) anon16_Else_correct)))))
(let ((anon0$1_correct  (=> (= (ControlFlow 0 13441) 13435) |inline$$Vector_empty'u64'$0$anon0_correct|)))
(let ((anon0_correct  (=> (= (ControlFlow 0 14811) 13441) anon0$1_correct)))
anon0_correct))))))))))))))))))))))))
))
(check-sat)
