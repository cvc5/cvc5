; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic LIA)
(set-info :status sat)
(declare-fun W_S1_V5 () Bool)
(declare-fun W_S1_V4 () Bool)
(declare-fun W_S1_V6 () Bool)
(declare-fun W_S1_V1 () Bool)
(declare-fun W_S1_V3 () Bool)
(declare-fun W_S1_V2 () Bool)
(declare-fun R_S1_V5 () Bool)
(declare-fun R_S1_V4 () Bool)
(declare-fun R_S1_V6 () Bool)
(declare-fun R_S1_V1 () Bool)
(declare-fun R_S1_V3 () Bool)
(declare-fun R_S1_V2 () Bool)
(declare-fun R_E2_V1 () Bool)
(declare-fun R_E1_V1 () Bool)
(declare-fun R_E1_V3 () Bool)
(declare-fun R_E2_V3 () Bool)
(assert
 (let
 (($x62242
   (forall
    ((V2_0 Int) (V6_0 Int) 
     (V4_0 Int) (V5_0 Int) 
     (S1_V3_!5556 Int) (S1_V3_!5562 Int) 
     (S1_V3_!5571 Int) (S1_V3_!5577 Int) 
     (E1_!5552 Int) (E1_!5567 Int) 
     (E1_!5569 Int) (S1_V2_!5555 Int) 
     (S1_V2_!5561 Int) (S1_V2_!5570 Int) 
     (S1_V2_!5576 Int) (S1_V5_!5560 Int) 
     (S1_V5_!5566 Int) (S1_V5_!5575 Int) 
     (S1_V5_!5581 Int) (S1_V4_!5559 Int) 
     (S1_V4_!5565 Int) (S1_V4_!5574 Int) 
     (S1_V4_!5580 Int) (S1_V6_!5558 Int) 
     (S1_V6_!5564 Int) (S1_V6_!5573 Int) 
     (S1_V6_!5579 Int) (E2_!5553 Int) 
     (E2_!5554 Int) (E2_!5568 Int) 
     (S1_V1_!5557 Int) (S1_V1_!5563 Int) 
     (S1_V1_!5572 Int) (S1_V1_!5578 Int))
    (let (($x59864 (= S1_V5_!5566 S1_V5_!5581)))
    (let (($x59925 (not W_S1_V5)))
    (let (($x62779 (or $x59925 $x59864)))
    (let (($x62200 (= S1_V4_!5565 S1_V4_!5580)))
    (let (($x59923 (not W_S1_V4)))
    (let (($x62447 (or $x59923 $x62200)))
    (let (($x62602 (= S1_V6_!5564 S1_V6_!5579)))
    (let (($x62610 (not W_S1_V6)))
    (let (($x62230 (or $x62610 $x62602)))
    (let (($x61214 (= S1_V1_!5563 S1_V1_!5578)))
    (let (($x60986 (= S1_V3_!5562 S1_V3_!5577)))
    (let (($x62444 (= S1_V2_!5561 S1_V2_!5576)))
    (let (($x62507 (not W_S1_V2)))
    (let (($x62441 (or $x62507 $x62444)))
    (let
    (($x62532
      (and $x62441
      (ite W_S1_V3 $x60986
      (= (ite W_S1_V3 S1_V3_!5556 E2_!5554) (+ (- 1) E2_!5568)))
      (ite W_S1_V1 $x61214
      (= E1_!5552 (+ 1 (ite W_S1_V1 S1_V1_!5572 E1_!5569)))) $x62230 $x62447
      $x62779)))
    (let ((?x62367 (ite W_S1_V1 S1_V1_!5572 E1_!5569)))
    (let ((?x60865 (+ 1 ?x62367)))
    (let ((?x62511 (ite W_S1_V1 S1_V1_!5578 ?x60865)))
    (let ((?x60218 (ite W_S1_V3 S1_V3_!5556 E2_!5554)))
    (let ((?x60222 (+ 1 ?x60218)))
    (let ((?x62533 (ite W_S1_V3 S1_V3_!5562 ?x60222)))
    (let
    (($x62746
      (and (not (<= V4_0 E2_!5553)) 
      (not (<= V2_0 E1_!5552)) 
      (not (<= V4_0 E2_!5554))
      (not (<= (ite W_S1_V4 S1_V4_!5559 V4_0) ?x60222))
      (>= ?x62533 (+ (- 1) (ite W_S1_V4 S1_V4_!5565 V4_0)))
      (>= (ite W_S1_V1 S1_V1_!5563 E1_!5552)
      (+ (- 1) (ite W_S1_V2 S1_V2_!5561 V2_0))) 
      (not (<= V2_0 E1_!5567)) 
      (not (<= V4_0 E2_!5568)) 
      (not (<= V2_0 E1_!5569))
      (not (<= (ite W_S1_V2 S1_V2_!5570 V2_0) ?x60865))
      (>= ?x62511 (+ (- 1) (ite W_S1_V2 S1_V2_!5576 V2_0)))
      (>= (ite W_S1_V3 S1_V3_!5577 E2_!5568)
      (+ (- 1) (ite W_S1_V4 S1_V4_!5580 V4_0))))))
    (let (($x62780 (= S1_V1_!5578 S1_V1_!5572)))
    (let (($x161 (not R_S1_V5)))
    (let (($x62589 (or $x161 (= (ite W_S1_V5 S1_V5_!5575 V5_0) V5_0))))
    (let (($x159 (not R_S1_V4)))
    (let (($x62548 (or $x159 (= (ite W_S1_V4 S1_V4_!5574 V4_0) V4_0))))
    (let (($x157 (not R_S1_V6)))
    (let (($x62737 (or $x157 (= (ite W_S1_V6 S1_V6_!5573 V6_0) V6_0))))
    (let (($x153 (not R_S1_V3)))
    (let
    (($x62224 (or $x153 (= (ite W_S1_V3 S1_V3_!5571 E2_!5568) E2_!5568))))
    (let (($x151 (not R_S1_V2)))
    (let (($x62641 (or $x151 (= (ite W_S1_V2 S1_V2_!5570 V2_0) V2_0))))
    (let
    (($x60228
      (and $x62641 $x62224 
      (or (not R_S1_V1) (= ?x62367 (+ (- 1) E1_!5569))) $x62737 $x62548
      $x62589)))
    (let (($x62356 (not $x60228)))
    (let (($x62680 (= S1_V1_!5578 S1_V1_!5563)))
    (let (($x62272 (or $x161 $x59925 (= S1_V5_!5575 S1_V5_!5560))))
    (let (($x61083 (= S1_V4_!5574 S1_V4_!5559)))
    (let (($x62455 (or $x159 $x59923 $x61083)))
    (let (($x60917 (= S1_V6_!5573 S1_V6_!5558)))
    (let (($x62584 (or $x157 $x62610 $x60917)))
    (let (($x59905 (= S1_V2_!5570 S1_V2_!5555)))
    (let (($x62549 (or $x151 $x62507 $x59905)))
    (let
    (($x62675
      (and $x62549 (or $x153 (= (ite W_S1_V3 S1_V3_!5571 E2_!5568) ?x60222))
      (or (not R_S1_V1)
      (= ?x62367 (+ (- 1) (ite W_S1_V1 S1_V1_!5557 E1_!5552)))) $x62584
      $x62455 $x62272)))
    (let (($x59892 (= S1_V1_!5578 S1_V1_!5557)))
    (let
    (($x60942 (or $x153 (= (ite W_S1_V3 S1_V3_!5571 E2_!5568) E2_!5554))))
    (let
    (($x62564
      (and $x62641 $x60942 
      (or (not R_S1_V1) (= ?x62367 (+ (- 1) E1_!5552))) $x62737 $x62548
      $x62589)))
    (let (($x59819 (not $x62564)))
    (let (($x60234 (= S1_V1_!5563 S1_V1_!5572)))
    (let (($x61232 (or $x161 (= (ite W_S1_V5 S1_V5_!5560 V5_0) V5_0))))
    (let (($x61254 (or $x159 (= (ite W_S1_V4 S1_V4_!5559 V4_0) V4_0))))
    (let (($x59994 (or $x157 (= (ite W_S1_V6 S1_V6_!5558 V6_0) V6_0))))
    (let (($x155 (not R_S1_V1)))
    (let
    (($x62420 (or $x155 (= (ite W_S1_V1 S1_V1_!5557 E1_!5552) E1_!5569))))
    (let (($x62368 (or $x151 (= (ite W_S1_V2 S1_V2_!5555 V2_0) V2_0))))
    (let
    (($x62830
      (not
      (and $x62368 (or $x153 (= ?x60218 (+ (- 1) E2_!5568))) $x62420 $x59994
      $x61254 $x61232))))
    (let (($x62636 (= S1_V1_!5563 S1_V1_!5557)))
    (let
    (($x59733 (or $x155 (= (ite W_S1_V1 S1_V1_!5557 E1_!5552) E1_!5552))))
    (let
    (($x62306
      (not
      (and $x62368 (or $x153 (= ?x60218 (+ (- 1) E2_!5554))) $x59733 $x59994
      $x61254 $x61232))))
    (let (($x60134 (= S1_V1_!5557 S1_V1_!5572)))
    (let
    (($x59719
      (not
      (and (or $x153 (= E2_!5554 E2_!5568)) (or $x155 (= E1_!5552 E1_!5569))))))
    (let (($x61406 (= E2_!5554 E2_!5568)))
    (let (($x59878 (not (or (not R_E2_V1) (= E1_!5552 E1_!5567)))))
    (let (($x59949 (or $x59878 $x61406)))
    (let (($x62775 (or $x59878 (= E2_!5553 E2_!5568))))
    (let (($x59743 (= E2_!5553 E2_!5554)))
    (let (($x62428 (= S1_V6_!5573 S1_V6_!5579)))
    (let (($x60152 (or $x161 (= V5_0 (ite W_S1_V5 S1_V5_!5575 V5_0)))))
    (let (($x60212 (or $x159 (= V4_0 (ite W_S1_V4 S1_V4_!5574 V4_0)))))
    (let (($x61260 (or $x157 (= V6_0 (ite W_S1_V6 S1_V6_!5573 V6_0)))))
    (let
    (($x60887 (or $x153 (= E2_!5568 (ite W_S1_V3 S1_V3_!5571 E2_!5568)))))
    (let (($x62275 (or $x151 (= V2_0 (ite W_S1_V2 S1_V2_!5570 V2_0)))))
    (let
    (($x61258
      (or
      (not
      (and $x62275 $x60887 
      (or $x155 (= E1_!5569 ?x60865)) $x61260 $x60212 $x60152)) $x62428)))
    (let
    (($x61266
      (not
      (and (or $x153 (= E2_!5568 E2_!5554)) (or $x155 (= E1_!5569 E1_!5552))))))
    (let (($x61122 (= S1_V5_!5560 S1_V5_!5575)))
    (let (($x59790 (or $x161 $x59925 $x61122)))
    (let (($x62797 (or $x159 $x59923 (= S1_V4_!5559 S1_V4_!5574))))
    (let (($x62684 (or $x157 $x62610 (= S1_V6_!5558 S1_V6_!5573))))
    (let (($x62354 (or $x151 $x62507 (= S1_V2_!5555 S1_V2_!5570))))
    (let
    (($x60910
      (and $x62354
      (or $x153 (= ?x60218 (+ (- 1) (ite W_S1_V3 S1_V3_!5571 E2_!5568))))
      (or $x155 (= (ite W_S1_V1 S1_V1_!5557 E1_!5552) ?x60865)) $x62684
      $x62797 $x59790)))
    (let (($x59844 (not $x60910)))
    (let (($x62494 (= S1_V5_!5560 S1_V5_!5581)))
    (let
    (($x62623 (or $x153 (= E2_!5554 (ite W_S1_V3 S1_V3_!5571 E2_!5568)))))
    (let
    (($x61100
      (or
      (not
      (and $x62275 $x62623 
      (or $x155 (= E1_!5552 ?x60865)) $x61260 $x60212 $x60152)) $x62494)))
    (let (($x60862 (= S1_V5_!5560 S1_V5_!5566)))
    (let (($x62353 (or $x161 (= V5_0 (ite W_S1_V5 S1_V5_!5560 V5_0)))))
    (let (($x60875 (or $x159 (= V4_0 (ite W_S1_V4 S1_V4_!5559 V4_0)))))
    (let (($x62491 (or $x157 (= V6_0 (ite W_S1_V6 S1_V6_!5558 V6_0)))))
    (let
    (($x62399 (or $x155 (= E1_!5552 (ite W_S1_V1 S1_V1_!5557 E1_!5552)))))
    (let (($x62431 (or $x151 (= V2_0 (ite W_S1_V2 S1_V2_!5555 V2_0)))))
    (let
    (($x62297
      (or
      (not
      (and $x62431 (or $x153 (= E2_!5554 ?x60222)) $x62399 $x62491 $x60875
      $x62353)) $x60862)))
    (let (($x60874 (= S1_V2_!5570 S1_V2_!5576)))
    (let
    (($x62369
      (or
      (not
      (and $x62275 $x60887 
      (or $x155 (= E1_!5569 ?x60865)) $x61260 $x60212 $x60152)) $x60874)))
    (let (($x62594 (= S1_V2_!5555 S1_V2_!5576)))
    (let
    (($x59910
      (or
      (not
      (and $x62275 $x62623 
      (or $x155 (= E1_!5552 ?x60865)) $x61260 $x60212 $x60152)) $x62594)))
    (let (($x62531 (= E1_!5569 E1_!5567)))
    (let (($x59835 (= E1_!5552 E1_!5569)))
    (let (($x62312 (= E1_!5552 E1_!5567)))
    (let
    (($x62715
      (and (or $x59719 (= S1_V3_!5556 S1_V3_!5571))
      (or $x62306 (= S1_V3_!5562 S1_V3_!5556))
      (or $x62830 (= S1_V3_!5562 S1_V3_!5571))
      (or $x59819 (= S1_V3_!5577 S1_V3_!5556))
      (or (not $x62675) (= S1_V3_!5577 S1_V3_!5562))
      (or $x62356 (= S1_V3_!5577 S1_V3_!5571)) $x62312 $x59835 $x62531
      $x59910 (or $x62306 (= S1_V2_!5561 S1_V2_!5555))
      (or $x62830 (= S1_V2_!5561 S1_V2_!5570)) 
      (or $x59844 $x62444) 
      (or $x61266 $x59905) $x62369 $x62297 
      (or $x59719 $x61122) $x61100 
      (or $x62830 (= S1_V5_!5566 S1_V5_!5575)) 
      (or $x59844 $x59864) 
      (or $x62356 (= S1_V5_!5581 S1_V5_!5575))
      (or $x62306 (= S1_V4_!5565 S1_V4_!5559))
      (or $x62830 (= S1_V4_!5565 S1_V4_!5574)) 
      (or $x59844 $x62200) 
      (or $x61266 $x61083) 
      (or $x59819 (= S1_V4_!5580 S1_V4_!5559))
      (or $x62356 (= S1_V4_!5580 S1_V4_!5574))
      (or $x62306 (= S1_V6_!5564 S1_V6_!5558))
      (or $x62830 (= S1_V6_!5564 S1_V6_!5573)) 
      (or $x59844 $x62602) 
      (or $x61266 $x60917) $x61258 
      (or $x59819 (= S1_V6_!5579 S1_V6_!5558)) $x59743 $x62775 $x59949
      (or $x59719 $x60134) 
      (or $x62306 $x62636) 
      (or $x62830 $x60234) 
      (or $x59819 $x59892) 
      (or (not $x62675) $x62680) 
      (or $x62356 $x62780)))) 
    (or (not $x62715) (not $x62746) $x62532)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (let (($x13 (or W_S1_V2 W_S1_V3 W_S1_V1 W_S1_V6 W_S1_V4 W_S1_V5)))
 (let (($x65 (not R_E1_V1)))
 (let (($x63 (not R_E1_V3)))
 (let (($x84 (not R_E2_V3))) (and $x84 $x63 $x65 $x13 $x62242)))))))
(assert (not (and (not W_S1_V4) (not W_S1_V3))))
(assert (not (and (not W_S1_V1) (not W_S1_V2))))
(assert (not (and (not R_S1_V3) (not R_S1_V1) (not W_S1_V4) (not W_S1_V2))))
(assert
 (let (($x62714 (not W_S1_V3)))
 (let (($x161 (not R_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x157 (not R_S1_V6)))
 (let (($x155 (not R_S1_V1)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x155 $x157 $x159 $x161 $x62714)))))))))
(assert
 (let (($x62610 (not W_S1_V6)))
 (let (($x62507 (not W_S1_V2)))
 (let (($x59925 (not W_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x155 (not R_S1_V1)))
 (let (($x153 (not R_S1_V3)))
 (not (and $x153 $x155 $x159 $x59925 $x62507 $x62610)))))))))
(assert
 (let (($x161 (not R_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x157 (not R_S1_V6)))
 (let (($x155 (not R_S1_V1)))
 (let (($x153 (not R_S1_V3)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x153 $x155 $x157 $x159 $x161)))))))))
(assert (not (and W_S1_V3 (not R_S1_V3) (not R_S1_V1) (not W_S1_V2))))
(assert (not (and W_S1_V3 W_S1_V1 (not R_S1_V3) (not R_S1_V1))))
(assert
 (let (($x62232 (not W_S1_V1)))
 (let (($x59925 (not W_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x157 (not R_S1_V6)))
 (let (($x153 (not R_S1_V3)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x153 $x157 $x159 $x59925 $x62232)))))))))
(assert
 (let (($x62610 (not W_S1_V6)))
 (let (($x62232 (not W_S1_V1)))
 (let (($x59925 (not W_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x153 (not R_S1_V3)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x153 $x159 $x59925 $x62232 $x62610)))))))))
(assert
 (let (($x62610 (not W_S1_V6)))
 (let (($x59923 (not W_S1_V4)))
 (let (($x161 (not R_S1_V5)))
 (let (($x155 (not R_S1_V1)))
 (let (($x153 (not R_S1_V3)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x153 $x155 $x161 $x59923 $x62610)))))))))
(assert
 (let (($x62610 (not W_S1_V6)))
 (let (($x62232 (not W_S1_V1)))
 (let (($x161 (not R_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x153 (not R_S1_V3)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x153 $x159 $x161 $x62232 $x62610)))))))))
(assert
 (let (($x62232 (not W_S1_V1)))
 (let (($x59925 (not W_S1_V5)))
 (let (($x59923 (not W_S1_V4)))
 (let (($x157 (not R_S1_V6)))
 (let (($x153 (not R_S1_V3)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x153 $x157 $x59923 $x59925 $x62232)))))))))
(assert
 (let (($x62610 (not W_S1_V6)))
 (let (($x59925 (not W_S1_V5)))
 (let (($x59923 (not W_S1_V4)))
 (let (($x155 (not R_S1_V1)))
 (let (($x153 (not R_S1_V3)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x153 $x155 $x59923 $x59925 $x62610)))))))))
(assert
 (let (($x59923 (not W_S1_V4)))
 (let (($x161 (not R_S1_V5)))
 (let (($x157 (not R_S1_V6)))
 (let (($x155 (not R_S1_V1)))
 (let (($x153 (not R_S1_V3)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x153 $x155 $x157 $x161 $x59923)))))))))
(assert
 (let (($x62232 (not W_S1_V1)))
 (let (($x59923 (not W_S1_V4)))
 (let (($x161 (not R_S1_V5)))
 (let (($x157 (not R_S1_V6)))
 (let (($x153 (not R_S1_V3)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x153 $x157 $x161 $x59923 $x62232)))))))))
(assert
 (let (($x62714 (not W_S1_V3)))
 (let (($x62507 (not W_S1_V2)))
 (let (($x161 (not R_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x157 (not R_S1_V6)))
 (let (($x155 (not R_S1_V1)))
 (not (and $x155 $x157 $x159 $x161 $x62507 $x62714)))))))))
(assert
 (let (($x62714 (not W_S1_V3)))
 (let (($x62610 (not W_S1_V6)))
 (let (($x161 (not R_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x155 (not R_S1_V1)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x155 $x159 $x161 $x62610 $x62714)))))))))
(assert
 (let (($x62714 (not W_S1_V3)))
 (let (($x62610 (not W_S1_V6)))
 (let (($x62507 (not W_S1_V2)))
 (let (($x161 (not R_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x155 (not R_S1_V1)))
 (not (and $x155 $x159 $x161 $x62507 $x62610 $x62714)))))))))
(assert
 (let (($x62714 (not W_S1_V3)))
 (let (($x59925 (not W_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x157 (not R_S1_V6)))
 (let (($x155 (not R_S1_V1)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x155 $x157 $x159 $x59925 $x62714)))))))))
(assert
 (let (($x62714 (not W_S1_V3)))
 (let (($x62507 (not W_S1_V2)))
 (let (($x59925 (not W_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x157 (not R_S1_V6)))
 (let (($x155 (not R_S1_V1)))
 (not (and $x155 $x157 $x159 $x59925 $x62507 $x62714)))))))))
(assert
 (let (($x62714 (not W_S1_V3)))
 (let (($x62610 (not W_S1_V6)))
 (let (($x59925 (not W_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x155 (not R_S1_V1)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x155 $x159 $x59925 $x62610 $x62714)))))))))
(assert
 (let (($x62714 (not W_S1_V3)))
 (let (($x62610 (not W_S1_V6)))
 (let (($x62507 (not W_S1_V2)))
 (let (($x59925 (not W_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x155 (not R_S1_V1)))
 (not (and $x155 $x159 $x59925 $x62507 $x62610 $x62714)))))))))
(assert
 (let (($x62232 (not W_S1_V1)))
 (let (($x161 (not R_S1_V5)))
 (let (($x159 (not R_S1_V4)))
 (let (($x157 (not R_S1_V6)))
 (let (($x153 (not R_S1_V3)))
 (let (($x151 (not R_S1_V2)))
 (not (and $x151 $x153 $x157 $x159 $x161 $x62232)))))))))
(check-sat)

