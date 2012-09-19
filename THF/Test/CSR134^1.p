%------------------------------------------------------------------------------
% File     : CSR134^1 : TPTP v5.4.0. Released v4.1.0.
% Domain   : Commonsense Reasoning
% Problem  : In 2009, what are different feelings of people to Anna?
% Version  : Especial.
% English  : In the context of year 2009: Does there exists a relation ?R and 
%            persons ?X and ?Y so that ?R holds between ?X and Anna but not 
%            between ?Y and Anna.

% Refs     : [Ben10] Benzmueller (2010), Email to Geoff Sutcliffe
% Source   : [Ben10]
% Names    : ef_rv_6.tq_SUMO_local [Ben10]

% Status   : Theorem
% Rating   : 0.40 v5.4.0, 0.50 v5.1.0, 0.75 v5.0.0, 0.50 v4.1.0
% Syntax   : Number of formulae    :   23 (   8 unit;  12 type;   0 defn)
%            Number of atoms       :   92 (   0 equality;   4 variable)
%            Maximal formula depth :    9 (   4 average)
%            Number of connectives :   62 (   0   ~;   0   |;   1   &;  61   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :    9 (   9   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   16 (  12   :)
%            Number of variables   :    3 (   0 sgn;   0   !;   3   ?;   0   ^)
%                                         (   3   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : THF_THM_NEQ

% Comments : This is a simple test problem for reasoning in/about SUMO.
%            Initally the problem has been hand generated in KIF syntax in
%            SigmaKEE and then automatically translated by Benzmueller's
%            KIF2THF translator into THF syntax.
%          : The translation has been applied in two modes: local and SInE.
%            The local mode only translates the local assumptions and the
%            query. The SInE mode additionally translates the SInE-extract
%            of the loaded knowledge base (usually SUMO).
%          : The examples are selected to illustrate the benefits of
%            higher-order reasoning in ontology reasoning.
%------------------------------------------------------------------------------
%----The extracted signature
thf(numbers,type,(
    num: $tType )).

thf(holdsDuring_THFTYPE_IiooI,type,(
    holdsDuring_THFTYPE_IiooI: $i > $o > $o )).

thf(lAnna_THFTYPE_i,type,(
    lAnna_THFTYPE_i: $i )).

thf(lBen_THFTYPE_i,type,(
    lBen_THFTYPE_i: $i )).

thf(lBill_THFTYPE_i,type,(
    lBill_THFTYPE_i: $i )).

thf(lBob_THFTYPE_i,type,(
    lBob_THFTYPE_i: $i )).

thf(lMary_THFTYPE_i,type,(
    lMary_THFTYPE_i: $i )).

thf(lSue_THFTYPE_i,type,(
    lSue_THFTYPE_i: $i )).

thf(lYearFn_THFTYPE_IiiI,type,(
    lYearFn_THFTYPE_IiiI: $i > $i )).

thf(likes_THFTYPE_IiioI,type,(
    likes_THFTYPE_IiioI: $i > $i > $o )).

thf(n2009_THFTYPE_i,type,(
    n2009_THFTYPE_i: $i )).

thf(parent_THFTYPE_IiioI,type,(
    parent_THFTYPE_IiioI: $i > $i > $o )).

%----The translated axioms
thf(ax,axiom,
    ( holdsDuring_THFTYPE_IiooI @ ( lYearFn_THFTYPE_IiiI @ n2009_THFTYPE_i ) @ ( parent_THFTYPE_IiioI @ lMary_THFTYPE_i @ lAnna_THFTYPE_i ) )).

thf(ax_001,axiom,
    ( holdsDuring_THFTYPE_IiooI @ ( lYearFn_THFTYPE_IiiI @ n2009_THFTYPE_i ) @ ( parent_THFTYPE_IiioI @ lSue_THFTYPE_i @ lBen_THFTYPE_i ) )).

thf(ax_002,axiom,
    ( holdsDuring_THFTYPE_IiooI @ ( lYearFn_THFTYPE_IiiI @ n2009_THFTYPE_i ) @ ( ~ @ ( parent_THFTYPE_IiioI @ lBob_THFTYPE_i @ lAnna_THFTYPE_i ) ) )).

thf(ax_003,axiom,
    ( holdsDuring_THFTYPE_IiooI @ ( lYearFn_THFTYPE_IiiI @ n2009_THFTYPE_i ) @ ( likes_THFTYPE_IiioI @ lSue_THFTYPE_i @ lBill_THFTYPE_i ) )).

thf(ax_004,axiom,
    ( holdsDuring_THFTYPE_IiooI @ ( lYearFn_THFTYPE_IiiI @ n2009_THFTYPE_i ) @ ( likes_THFTYPE_IiioI @ lBob_THFTYPE_i @ lBill_THFTYPE_i ) )).

thf(ax_005,axiom,
    ( holdsDuring_THFTYPE_IiooI @ ( lYearFn_THFTYPE_IiiI @ n2009_THFTYPE_i ) @ ( ~ @ ( parent_THFTYPE_IiioI @ lBob_THFTYPE_i @ lBen_THFTYPE_i ) ) )).

thf(ax_006,axiom,
    ( holdsDuring_THFTYPE_IiooI @ ( lYearFn_THFTYPE_IiiI @ n2009_THFTYPE_i ) @ ( likes_THFTYPE_IiioI @ lMary_THFTYPE_i @ lBill_THFTYPE_i ) )).

thf(ax_007,axiom,
    ( holdsDuring_THFTYPE_IiooI @ ( lYearFn_THFTYPE_IiiI @ n2009_THFTYPE_i ) @ ( parent_THFTYPE_IiioI @ lSue_THFTYPE_i @ lAnna_THFTYPE_i ) )).

thf(ax_008,axiom,
    ( holdsDuring_THFTYPE_IiooI @ ( lYearFn_THFTYPE_IiiI @ n2009_THFTYPE_i ) @ ( parent_THFTYPE_IiioI @ lMary_THFTYPE_i @ lBen_THFTYPE_i ) )).

thf(ax_009,axiom,
    ( holdsDuring_THFTYPE_IiooI @ ( lYearFn_THFTYPE_IiiI @ n2009_THFTYPE_i ) @ ( ~ @ ( likes_THFTYPE_IiioI @ lSue_THFTYPE_i @ lMary_THFTYPE_i ) ) )).

%----The translated conjecture
thf(con,conjecture,(
    ? [R: $i > $i > $o,X: $i,Y: $i] :
      ( holdsDuring_THFTYPE_IiooI @ ( lYearFn_THFTYPE_IiiI @ n2009_THFTYPE_i )
      @ ( ( R @ X @ lAnna_THFTYPE_i )
        & ( ~ @ ( R @ Y @ lAnna_THFTYPE_i ) ) ) ) )).

%------------------------------------------------------------------------------
