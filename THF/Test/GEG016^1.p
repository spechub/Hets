%------------------------------------------------------------------------------
% File     : GEG016^1 : TPTP v5.1.0. Released v4.1.0.
% Domain   : Geography
% Problem  : Places in Spain and France do not overlap
% Version  : [RCC92] axioms.
% English  : 

% Refs     : [RCC92] Randell et al. (1992), A Spatial Logic Based on Region
%          : [Ben10a] Benzmueller (2010), Email to Geoff Sutcliffe
%          : [Ben10b] Benzmueller (2010), Simple Type Theory as a Framework
% Source   : [Ben10a]
% Names    : Problem 75 [Ben10b]
%          : Problem 76 [Ben10b]

% Status   : Theorem
% Rating   : 0.40 v5.1.0, 0.60 v5.0.0, 0.40 v4.1.0
% Syntax   : Number of formulae    :   98 (   6 unit;  49 type;  40 defn)
%            Number of atoms       :  550 (  45 equality; 186 variable)
%            Maximal formula depth :   11 (   6 average)
%            Number of connectives :  238 (  11   ~;   4   |;  19   &; 193   @)
%                                         (   0 <=>;  11  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  195 ( 195   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   55 (  49   :)
%            Number of variables   :  118 (   7 sgn;  35   !;   9   ?;  74   ^)
%                                         ( 118   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : THF_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Include Region Connection Calculus axioms
include('Axioms/LCL013^0.ax').
include('Axioms/LCL014^0.ax').
%------------------------------------------------------------------------------
thf(catalunya,type,(
    catalunya: reg )).

thf(france,type,(
    france: reg )).

thf(spain,type,(
    spain: reg )).

thf(paris,type,(
    paris: reg )).

thf(a,type,(
    a: $i > $i > $o )).

thf(fool,type,(
    fool: $i > $i > $o )).

thf(t_axiom_for_fool,axiom,
    ( mvalid
    @ ( mforall_prop
      @ ^ [A: $i > $o] :
          ( mimplies @ ( mbox @ fool @ A ) @ A ) ) )).

thf(k_axiom_for_fool,axiom,
    ( mvalid
    @ ( mforall_prop
      @ ^ [A: $i > $o] :
          ( mimplies @ ( mbox @ fool @ A ) @ ( mbox @ fool @ ( mbox @ fool @ A ) ) ) ) )).

thf(i_axiom_for_fool_a,axiom,
    ( mvalid
    @ ( mforall_prop
      @ ^ [Phi: $i > $o] :
          ( mimplies @ ( mbox @ fool @ Phi ) @ ( mbox @ a @ Phi ) ) ) )).

thf(ax1,axiom,
    ( mvalid
    @ ( mbox @ a
      @ ^ [X: $i] :
          ( tpp @ catalunya @ spain ) ) )).

thf(ax2,axiom,
    ( mvalid
    @ ( mbox @ fool
      @ ^ [X: $i] :
          ( ec @ spain @ france ) ) )).

thf(ax3,axiom,
    ( mvalid
    @ ( mbox @ a
      @ ^ [X: $i] :
          ( ntpp @ paris @ france ) ) )).

thf(con,conjecture,
    ( mvalid
    @ ( mbox @ fool
      @ ^ [X: $i] :
        ! [Z: reg,Y: reg] :
          ( ( ( p @ Z @ spain )
            & ( p @ Y @ france ) )
         => ~ ( o @ Z @ Y ) ) ) )).

%------------------------------------------------------------------------------
