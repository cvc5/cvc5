% COMMAND-LINE: --uf-ho --full-saturate-quant --ho-elim
% EXPECT: % SZS status Theorem for SYO362^5

thf(cK,type,(
    cK: ( $i > $o ) > $i > $o )).

thf(cTHM631A_pme,conjecture,
    ( ! [X: $i > $o,Y: $i > $o] :
        ( ( cK
          @ ^ [Xz: $i] :
              ( ( X @ Xz )
              | ( Y @ Xz ) ) )
        = ( ^ [Xw: $i] :
              ( ( cK @ X @ Xw )
              | ( cK @ Y @ Xw ) ) ) )
   => ! [X: $i > $o,Y: $i > $o] :
        ( ! [Xx: $i] :
            ( ( X @ Xx )
           => ( Y @ Xx ) )
       => ! [Xx: $i] :
            ( ( cK @ X @ Xx )
           => ( cK @ Y @ Xx ) ) ) )).
