% COMMAND-LINE: --uf-ho --full-saturate-quant --ho-elim-store-ax
% COMMAND-LINE: --uf-ho --full-saturate-quant --ho-elim
% EXPECT: % SZS status Theorem for store-ax-min

thf(a, type, (a: $i)).
thf(b, type, (b: $i)).

%% thf(blah1, axiom, ( ! [X: $i, Y: $i] : (X = Y))).

thf(blah2, axiom, ( ~ (a = b))).

%% thf(storeax, axiom, (
%%         ! [F : $i > $i, D : $i, R : $i] :
%%         (
%%             ? [G : $i > $i] :
%%             (
%%                 ! [X : $i] :
%%                 (
%%                     (G @ X) = $ite( X = D, R, F @ X)
%%                 )
%%             )
%%         )


%% (~ (X = Y)))
%% ).

thf(blah, conjecture, ( ? [F : $i > $i, G : $i > $i] : (~ (F = G)))).
