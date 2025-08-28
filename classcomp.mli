
type __ = Obj.t

type empty_set = |

type unit0 =
| Tt

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

val add : nat -> nat -> nat

type 'a unconvertible = unit0

type 'a crelation = __

type ('a, 'b) arrow = 'a -> 'b

type ('a, 'b) iffT = ('a -> 'b, 'b -> 'a) prod

type ('a, 'r) reflexive = 'a -> 'r

val reflexivity : ('a1, 'a2) reflexive -> 'a1 -> 'a2

type ('a, 'r) symmetric = 'a -> 'a -> 'r -> 'r

val symmetry : ('a1, 'a2) symmetric -> 'a1 -> 'a1 -> 'a2 -> 'a2

type ('a, 'r) transitive = 'a -> 'a -> 'a -> 'r -> 'r -> 'r

val transitivity :
  ('a1, 'a2) transitive -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2

type ('a, 'r) pER = { pER_Symmetric : ('a, 'r) symmetric;
                      pER_Transitive : ('a, 'r) transitive }

type ('a, 'r) equivalence = { equivalence_Reflexive : ('a, 'r) reflexive;
                              equivalence_Symmetric : ('a, 'r) symmetric;
                              equivalence_Transitive : ('a, 'r) transitive }

val equivalence_PER : ('a1, 'a2) equivalence -> ('a1, 'a2) pER

type ('a, 'r, 'x) subrelation = 'a -> 'a -> 'r -> 'x

type ('a, 'r) proper = 'r

type ('a, 'r) properProxy = 'r

val reflexive_proper_proxy :
  ('a1, 'a2) reflexive -> 'a1 -> ('a1, 'a2) properProxy

type ('a, 'b, 'r, 'x) respectful = 'a -> 'a -> 'r -> 'x

val subrelation_respectful :
  ('a1, 'a2, 'a3) subrelation -> ('a4, 'a5, 'a6) subrelation -> ('a1 -> 'a4,
  ('a1, 'a4, 'a3, 'a5) respectful, ('a1, 'a4, 'a2, 'a6) respectful)
  subrelation

val subrelation_refl : ('a1, 'a2, 'a2) subrelation

val subrelation_proper :
  'a1 -> ('a1, 'a2) proper -> 'a1 crelation unconvertible -> ('a1, 'a2, 'a3)
  subrelation -> ('a1, 'a3) proper

val iffT_arrow_subrelation : (__, __) iffT -> (__, __) arrow

val iffT_flip_arrow_subrelation : (__, __) iffT -> (__, __) arrow

val trans_co_impl_type_morphism_obligation_1 :
  ('a1, 'a2) transitive -> 'a1 -> ('a1, __, 'a2, (__, __) arrow) respectful

val trans_co_impl_type_morphism :
  ('a1, 'a2) transitive -> 'a1 -> (__, ('a1, __, 'a2, (__, __) arrow)
  respectful) proper

val trans_sym_co_inv_impl_type_morphism_obligation_1 :
  ('a1, 'a2) pER -> 'a1 -> ('a1, __, 'a2, (__, __) arrow) respectful

val trans_sym_co_inv_impl_type_morphism :
  ('a1, 'a2) pER -> 'a1 -> (__, ('a1, __, 'a2, (__, __) arrow) respectful)
  proper

val trans_co_eq_inv_arrow_morphism_obligation_1 :
  ('a1, 'a2) transitive -> 'a1 -> 'a1 -> 'a2 -> 'a1 -> 'a1 -> (__, __) arrow

val trans_co_eq_inv_arrow_morphism :
  ('a1, 'a2) transitive -> 'a1 -> 'a1 -> 'a2 -> 'a1 -> 'a1 -> (__, __) arrow

val pER_type_morphism_obligation_1 :
  ('a1, 'a2) pER -> ('a1, __, 'a2, ('a1, __, 'a2, (__, __) iffT) respectful)
  respectful

val pER_type_morphism :
  ('a1, 'a2) pER -> (__, ('a1, __, 'a2, ('a1, __, 'a2, (__, __) iffT)
  respectful) respectful) proper

val reflexive_partial_app_morphism :
  ('a1 -> 'a2) -> ('a1 -> 'a2, ('a1, 'a2, 'a3, 'a4) respectful) proper -> 'a1
  -> ('a1, 'a3) properProxy -> ('a2, 'a4) proper

module Nat :
 sig
  val eqb : nat -> nat -> bool
 end

val remove : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val to_nat : (nat, nat) prod -> nat

type 'a in0 = __

type 'a incl = 'a -> 'a in0 -> 'a in0

type ('a, 't) included = 'a -> 'a in0 -> 't

val in_eq : 'a1 -> 'a1 list -> 'a1 in0

val in_cons : 'a1 -> 'a1 -> 'a1 list -> 'a1 in0 -> 'a1 in0

val nil_included : ('a1, 'a2) included

val nil_lem1 : 'a1 list -> 'a1 incl

val in_app_or :
  'a1 list -> 'a1 list -> 'a1 -> 'a1 in0 -> ('a1 in0, 'a1 in0) sum

val in_or_app :
  'a1 list -> 'a1 list -> 'a1 -> ('a1 in0, 'a1 in0) sum -> 'a1 in0

val included_lem1 :
  'a1 list -> 'a1 list -> ('a1, 'a2) included -> ('a1, 'a2) included -> ('a1,
  'a2) included

val incl_tran :
  'a1 list -> 'a1 list -> 'a1 list -> 'a1 incl -> 'a1 incl -> 'a1 incl

val incl_refl : 'a1 list -> 'a1 incl

val in_dec :
  ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> ('a1 in0, 'a1 in0 ->
  empty_set) sum

val incl_appl : 'a1 list -> 'a1 list -> 'a1 list -> 'a1 incl -> 'a1 incl

val incl_appr : 'a1 list -> 'a1 list -> 'a1 list -> 'a1 incl -> 'a1 incl

val in_inv : 'a1 -> 'a1 -> 'a1 list -> 'a1 in0 -> (__, 'a1 in0) sum

module type CBA =
 sig
  type coq_B

  val meet : coq_B -> coq_B -> coq_B

  val join : coq_B -> coq_B -> coq_B

  val bott : coq_B

  val top : coq_B

  val compl : coq_B -> coq_B

  type eq_B

  val eq_B_refl : (coq_B, eq_B) reflexive

  val eq_B_symm : (coq_B, eq_B) symmetric

  val eq_B_trans : (coq_B, eq_B) transitive

  val eq_B_meet_morph :
    (coq_B -> coq_B -> coq_B, (coq_B, coq_B -> coq_B, eq_B, (coq_B, coq_B,
    eq_B, eq_B) respectful) respectful) proper

  val eq_B_join_morph :
    (coq_B -> coq_B -> coq_B, (coq_B, coq_B -> coq_B, eq_B, (coq_B, coq_B,
    eq_B, eq_B) respectful) respectful) proper

  val enum : coq_B -> nat

  val meet_idem : coq_B -> eq_B

  val join_idem : coq_B -> eq_B

  val meet_comm : coq_B -> coq_B -> eq_B

  val join_comm : coq_B -> coq_B -> eq_B

  val meet_assoc : coq_B -> coq_B -> coq_B -> eq_B

  val join_assoc : coq_B -> coq_B -> coq_B -> eq_B

  val meet_absorb : coq_B -> coq_B -> eq_B

  val join_absorb : coq_B -> coq_B -> eq_B

  val meet_distrib : coq_B -> coq_B -> coq_B -> eq_B

  val join_distrib : coq_B -> coq_B -> coq_B -> eq_B

  val meet_bott : coq_B -> eq_B

  val join_bott : coq_B -> eq_B

  val meet_top : coq_B -> eq_B

  val join_top : coq_B -> eq_B

  val meet_compl : coq_B -> eq_B

  val join_compl : coq_B -> eq_B

  val id_B_dec : coq_B -> coq_B -> sumbool
 end

module Coq_filter_completion :
 functor (Coq_cba:CBA) ->
 sig
  val eq_B_relation : (Coq_cba.coq_B, Coq_cba.eq_B) equivalence

  val meet_morphism :
    (Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.coq_B, (Coq_cba.coq_B,
    Coq_cba.coq_B -> Coq_cba.coq_B, Coq_cba.eq_B, (Coq_cba.coq_B,
    Coq_cba.coq_B, Coq_cba.eq_B, Coq_cba.eq_B) respectful) respectful) proper

  val join_morphism :
    (Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.coq_B, (Coq_cba.coq_B,
    Coq_cba.coq_B -> Coq_cba.coq_B, Coq_cba.eq_B, (Coq_cba.coq_B,
    Coq_cba.coq_B, Coq_cba.eq_B, Coq_cba.eq_B) respectful) respectful) proper

  type leq = Coq_cba.eq_B

  type ('a, 'b) ciff = ('a -> 'b, 'b -> 'a) prod

  val leq' : Coq_cba.coq_B -> Coq_cba.coq_B -> (leq, Coq_cba.eq_B) ciff

  type 'f coq_Filter = { nonempty : (Coq_cba.coq_B, 'f) sigT;
                         upwards_closed : (Coq_cba.coq_B -> Coq_cba.coq_B ->
                                          'f -> leq -> 'f);
                         meet_closed : (Coq_cba.coq_B -> Coq_cba.coq_B -> 'f
                                       -> 'f -> 'f) }

  val nonempty : 'a1 coq_Filter -> (Coq_cba.coq_B, 'a1) sigT

  val upwards_closed :
    'a1 coq_Filter -> Coq_cba.coq_B -> Coq_cba.coq_B -> 'a1 -> leq -> 'a1

  val meet_closed :
    'a1 coq_Filter -> Coq_cba.coq_B -> Coq_cba.coq_B -> 'a1 -> 'a1 -> 'a1

  type 'x up =
    (nat, (Coq_cba.coq_B list, (__, (__, leq) prod) prod) sigT) sigT

  type 'f union_singl = 'f sumor

  type 'f inconsistent = 'f

  type ('f, 'g) equiconsistent =
    ('f inconsistent -> 'g inconsistent, 'g inconsistent -> 'f inconsistent)
    prod

  type 'f element_complete = ('f, 'f union_singl up) equiconsistent -> 'f

  type 'f complete = Coq_cba.coq_B -> 'f element_complete

  val leq_refl : Coq_cba.coq_B -> leq

  val leq_trans :
    Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.coq_B -> leq -> leq -> leq

  val eq_B_leq : Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.eq_B -> leq

  val leq_morphism :
    (__, (Coq_cba.coq_B, __, Coq_cba.eq_B, (Coq_cba.coq_B, __, Coq_cba.eq_B,
    (__, __) ciff) respectful) respectful) proper

  val meet_leq_compat :
    Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.coq_B -> leq
    -> leq -> leq

  val fold_left_meet_morphism :
    Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.coq_B list -> Coq_cba.eq_B ->
    Coq_cba.eq_B

  val fold_left_meet_cons :
    Coq_cba.coq_B list -> Coq_cba.coq_B -> Coq_cba.eq_B

  val fold_left_impl : Coq_cba.coq_B list -> ('a2 -> 'a3) -> __ -> __

  val fold_left_app_lem :
    Coq_cba.coq_B list -> Coq_cba.coq_B list -> Coq_cba.eq_B

  val up_filter : 'a1 up coq_Filter

  val filter_top : 'a1 coq_Filter -> 'a1

  val lemma3 : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> 'a1 incl

  val lemma2 :
    Coq_cba.coq_B list -> Coq_cba.coq_B list -> Coq_cba.coq_B incl -> leq

  val filter_memb_morph :
    'a1 coq_Filter -> Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.eq_B -> 'a1
    -> 'a1

  val lemma4 : Coq_cba.coq_B list -> 'a1 coq_Filter -> __ -> 'a1

  val lemma61 : Coq_cba.coq_B list -> __ -> (__, 'a3) prod

  val lemma62 : Coq_cba.coq_B list -> (__, 'a3) prod -> __

  val lemma5 :
    Coq_cba.coq_B list -> nat -> __ -> (__, (Coq_cba.coq_B, (Coq_cba.coq_B
    in0, (__, (__, ('a1, 'a1 union_singl up) equiconsistent) prod) prod)
    prod) sigT) sum

  type 'f coq_F_ = __

  type 'f coq_Z = (nat, 'f coq_F_) sigT

  val lem223 : Coq_cba.coq_B -> 'a2 -> 'a2 up

  type le =
  | Coq_le_n
  | Coq_le_S of nat * le

  val le_rect : nat -> 'a1 -> (nat -> le -> 'a1 -> 'a1) -> nat -> le -> 'a1

  val le_rec : nat -> 'a1 -> (nat -> le -> 'a1 -> 'a1) -> nat -> le -> 'a1

  type lt = le

  val le_lt_dec : nat -> nat -> (le, lt) sum

  val lt_le_incl : nat -> nat -> lt -> le

  val lem222 : nat -> nat -> le -> Coq_cba.coq_B -> 'a1 coq_F_ -> 'a1 coq_F_

  val thm22 :
    'a1 coq_Filter -> ('a1 coq_Z coq_Filter, (('a1, 'a1 coq_Z)
    equiconsistent, 'a1 coq_Z complete) prod) prod

  val lemma8 : Coq_cba.coq_B -> Coq_cba.coq_B list -> __ -> (__, __) sum

  val leq_bott : Coq_cba.coq_B -> leq
 end

module type Coq_classical_completeness_signature =
 sig
  type coq_function

  type predicate

  type constant0

  val function_dec : coq_function -> coq_function -> sumbool

  val predicate_dec : predicate -> predicate -> sumbool

  val constant0_dec : constant0 -> constant0 -> sumbool

  val enum_function : coq_function -> nat

  val enum_predicate : predicate -> nat

  val enum_constant0 : constant0 -> nat
 end

module Coq_classical_completeness :
 functor (Coq_ccsig:Coq_classical_completeness_signature) ->
 sig
  type formula =
  | Coq_bot
  | Coq_imp of formula * formula
  | Coq_all of formula
  | Coq_atom of Coq_ccsig.predicate * term
  and term =
  | Coq_bvar of nat
  | Coq_fvar of nat
  | Coq_cnst of constant
  | Coq_func of Coq_ccsig.coq_function * term
  and constant =
  | Coq_original of Coq_ccsig.constant0
  | Coq_added of formula

  val formula_rect :
    'a1 -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
    'a1) -> (Coq_ccsig.predicate -> term -> 'a1) -> formula -> 'a1

  val formula_rec :
    'a1 -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
    'a1) -> (Coq_ccsig.predicate -> term -> 'a1) -> formula -> 'a1

  val term_rect :
    (nat -> 'a1) -> (nat -> 'a1) -> (constant -> 'a1) ->
    (Coq_ccsig.coq_function -> term -> 'a1 -> 'a1) -> term -> 'a1

  val term_rec :
    (nat -> 'a1) -> (nat -> 'a1) -> (constant -> 'a1) ->
    (Coq_ccsig.coq_function -> term -> 'a1 -> 'a1) -> term -> 'a1

  val constant_rect :
    (Coq_ccsig.constant0 -> 'a1) -> (formula -> 'a1) -> constant -> 'a1

  val constant_rec :
    (Coq_ccsig.constant0 -> 'a1) -> (formula -> 'a1) -> constant -> 'a1

  val open_rec_term : nat -> term -> term -> term

  val open_rec : nat -> term -> formula -> formula

  val coq_open : formula -> term -> formula

  type notin = nat in0 -> empty_set

  type proof =
  | Coq_bot_elim of formula list * proof * formula
  | Coq_imp_elim of formula list * formula * formula * proof * proof
  | Coq_imp_intro of formula list * formula * formula * proof
  | Coq_dneg of formula list * formula * proof
  | Coq_hypo of formula list * formula * formula in0
  | Coq_all_elim of formula list * formula * proof * term
  | Coq_all_intro of formula list * formula * nat list
     * (nat -> notin -> proof)
  | Coq_weaken of formula list * formula * formula * proof

  val proof_rect :
    (formula list -> proof -> 'a1 -> formula -> 'a1) -> (formula list ->
    formula -> formula -> proof -> 'a1 -> proof -> 'a1 -> 'a1) -> (formula
    list -> formula -> formula -> proof -> 'a1 -> 'a1) -> (formula list ->
    formula -> proof -> 'a1 -> 'a1) -> (formula list -> formula -> formula
    in0 -> 'a1) -> (formula list -> formula -> proof -> 'a1 -> term -> 'a1)
    -> (formula list -> formula -> nat list -> __ -> (nat -> notin -> proof)
    -> (nat -> notin -> 'a1) -> 'a1) -> (formula list -> formula -> formula
    -> proof -> 'a1 -> 'a1) -> formula list -> formula -> proof -> 'a1

  val proof_rec :
    (formula list -> proof -> 'a1 -> formula -> 'a1) -> (formula list ->
    formula -> formula -> proof -> 'a1 -> proof -> 'a1 -> 'a1) -> (formula
    list -> formula -> formula -> proof -> 'a1 -> 'a1) -> (formula list ->
    formula -> proof -> 'a1 -> 'a1) -> (formula list -> formula -> formula
    in0 -> 'a1) -> (formula list -> formula -> proof -> 'a1 -> term -> 'a1)
    -> (formula list -> formula -> nat list -> __ -> (nat -> notin -> proof)
    -> (nat -> notin -> 'a1) -> 'a1) -> (formula list -> formula -> formula
    -> proof -> 'a1 -> 'a1) -> formula list -> formula -> proof -> 'a1

  type 'm model = { model_dneg : (formula -> 'm);
                    model_imp_faithful1 : (formula -> formula -> 'm -> 'm ->
                                          'm);
                    model_imp_faithful2 : (formula -> formula -> ('m -> 'm)
                                          -> 'm);
                    model_all_faithful1 : (formula -> 'm -> term -> 'm);
                    model_all_faithful2 : (formula -> __ -> __ -> (term -> __
                                          -> 'm) -> 'm) }

  val model_imp_faithful1 :
    'a1 model -> formula -> formula -> 'a1 -> 'a1 -> 'a1

  type 'm interprets = (formula -> formula in0 -> 'm) -> 'm

  type valid = __ -> __ model -> __ interprets

  val peirce : formula list -> formula -> formula -> proof

  val proof_imp_trans :
    formula list -> formula -> formula -> formula -> proof -> proof -> proof

  val proof_imp_contrapos :
    formula list -> formula -> formula -> proof -> proof

  val formula_dec : formula -> formula -> sumbool

  val constant_dec : constant -> constant -> sumbool

  module CBAproof :
   sig
    val compl : formula -> formula

    val meet : formula -> formula -> formula

    val join : formula -> formula -> formula

    val top : formula

    type eq_B = (proof, proof) prod

    val eq_B_refl : (formula, eq_B) reflexive

    val eq_B_symm : (formula, eq_B) symmetric

    val eq_B_trans : (formula, eq_B) transitive

    val eq_B_relation : (formula, eq_B) equivalence

    val join_morphism :
      (formula -> formula -> formula, (formula, formula -> formula, eq_B,
      (formula, formula, eq_B, eq_B) respectful) respectful) proper

    val meet_morphism :
      (formula -> formula -> formula, (formula, formula -> formula, eq_B,
      (formula, formula, eq_B, eq_B) respectful) respectful) proper

    val id_B_dec : formula -> formula -> sumbool

    val join_idem : formula -> eq_B

    val meet_idem : formula -> eq_B

    val join_comm : formula -> formula -> eq_B

    val meet_comm : formula -> formula -> eq_B

    val join_assoc : formula -> formula -> formula -> eq_B

    val meet_assoc : formula -> formula -> formula -> eq_B

    val meet_absorb : formula -> formula -> eq_B

    val join_absorb : formula -> formula -> eq_B

    val join_distrib : formula -> formula -> formula -> eq_B

    val meet_bott : formula -> eq_B

    val join_bott : formula -> eq_B

    val meet_top : formula -> eq_B

    val join_top : formula -> eq_B

    val meet_compl : formula -> eq_B

    val join_compl : formula -> eq_B

    val meet_distrib : formula -> formula -> formula -> eq_B

    val enump : Coq_ccsig.predicate -> nat

    val enumc0 : Coq_ccsig.constant0 -> nat

    val enumfunc : Coq_ccsig.coq_function -> nat

    val enumf : formula -> nat

    val enumt : term -> nat

    val enumc : constant -> nat

    val enum : formula -> nat

    val eq_B_join_morph :
      (formula -> formula -> formula, (formula, formula -> formula, eq_B,
      (formula, formula, eq_B, eq_B) respectful) respectful) proper

    val eq_B_meet_morph :
      (formula -> formula -> formula, (formula, formula -> formula, eq_B,
      (formula, formula, eq_B, eq_B) respectful) respectful) proper

    val bott : formula

    type coq_B = formula
   end

  val weaken_lem1 :
    formula list -> formula list -> formula -> formula incl -> proof -> proof

  val c2t_term : term -> constant -> term -> term

  val c2t : formula -> constant -> term -> formula

  val c2tl : formula list -> constant -> term -> formula list

  val thm283 : formula list -> formula -> nat -> formula -> proof -> proof

  val ex_intro : formula list -> term -> formula -> proof

  val ex_elim :
    formula list -> formula -> formula -> proof -> (term -> proof) -> proof

  val lemma_HE1 : formula list -> formula -> proof

  val disj_elim :
    formula list -> formula -> formula -> formula -> proof -> proof -> proof

  val coq_LEM : formula list -> formula -> proof

  val lemma_HE2_1 : formula -> formula list -> proof

  val lemma_HE2_2 : formula -> formula list -> proof

  val lemma_HE2 : formula list -> formula -> proof

  type coq_HA = (formula, __) sigT

  module CBAproof_completion :
   sig
    val eq_B_relation : (formula, CBAproof.eq_B) equivalence

    val meet_morphism :
      (formula -> formula -> formula, (formula, formula -> formula,
      CBAproof.eq_B, (formula, formula, CBAproof.eq_B, CBAproof.eq_B)
      respectful) respectful) proper

    val join_morphism :
      (formula -> formula -> formula, (formula, formula -> formula,
      CBAproof.eq_B, (formula, formula, CBAproof.eq_B, CBAproof.eq_B)
      respectful) respectful) proper

    type leq = CBAproof.eq_B

    type ('a, 'b) ciff = ('a -> 'b, 'b -> 'a) prod

    val leq' : formula -> formula -> (leq, CBAproof.eq_B) ciff

    type 'f coq_Filter = { nonempty : (formula, 'f) sigT;
                           upwards_closed : (formula -> formula -> 'f -> leq
                                            -> 'f);
                           meet_closed : (formula -> formula -> 'f -> 'f ->
                                         'f) }

    val nonempty : 'a1 coq_Filter -> (formula, 'a1) sigT

    val upwards_closed :
      'a1 coq_Filter -> formula -> formula -> 'a1 -> leq -> 'a1

    val meet_closed :
      'a1 coq_Filter -> formula -> formula -> 'a1 -> 'a1 -> 'a1

    type 'x up = (nat, (formula list, (__, (__, leq) prod) prod) sigT) sigT

    type 'f union_singl = 'f sumor

    type 'f inconsistent = 'f

    type ('f, 'g) equiconsistent =
      ('f inconsistent -> 'g inconsistent, 'g inconsistent -> 'f
      inconsistent) prod

    type 'f element_complete = ('f, 'f union_singl up) equiconsistent -> 'f

    type 'f complete = formula -> 'f element_complete

    val leq_refl : formula -> leq

    val leq_trans : formula -> formula -> formula -> leq -> leq -> leq

    val eq_B_leq : formula -> formula -> CBAproof.eq_B -> leq

    val leq_morphism :
      (__, (formula, __, CBAproof.eq_B, (formula, __, CBAproof.eq_B, (__, __)
      ciff) respectful) respectful) proper

    val meet_leq_compat :
      formula -> formula -> formula -> formula -> leq -> leq -> leq

    val fold_left_meet_morphism :
      formula -> formula -> formula list -> CBAproof.eq_B -> CBAproof.eq_B

    val fold_left_meet_cons : formula list -> formula -> CBAproof.eq_B

    val fold_left_impl : formula list -> ('a2 -> 'a3) -> __ -> __

    val fold_left_app_lem : formula list -> formula list -> CBAproof.eq_B

    val up_filter : 'a1 up coq_Filter

    val filter_top : 'a1 coq_Filter -> 'a1

    val lemma3 : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> 'a1 incl

    val lemma2 : formula list -> formula list -> formula incl -> leq

    val filter_memb_morph :
      'a1 coq_Filter -> formula -> formula -> CBAproof.eq_B -> 'a1 -> 'a1

    val lemma4 : formula list -> 'a1 coq_Filter -> __ -> 'a1

    val lemma61 : formula list -> __ -> (__, 'a3) prod

    val lemma62 : formula list -> (__, 'a3) prod -> __

    val lemma5 :
      formula list -> nat -> __ -> (__, (formula, (formula in0, (__, (__,
      ('a1, 'a1 union_singl up) equiconsistent) prod) prod) prod) sigT) sum

    type 'f coq_F_ = __

    type 'f coq_Z = (nat, 'f coq_F_) sigT

    val lem223 : formula -> 'a2 -> 'a2 up

    type le =
    | Coq_le_n
    | Coq_le_S of nat * le

    val le_rect : nat -> 'a1 -> (nat -> le -> 'a1 -> 'a1) -> nat -> le -> 'a1

    val le_rec : nat -> 'a1 -> (nat -> le -> 'a1 -> 'a1) -> nat -> le -> 'a1

    type lt = le

    val le_lt_dec : nat -> nat -> (le, lt) sum

    val lt_le_incl : nat -> nat -> lt -> le

    val lem222 : nat -> nat -> le -> formula -> 'a1 coq_F_ -> 'a1 coq_F_

    val thm22 :
      'a1 coq_Filter -> ('a1 coq_Z coq_Filter, (('a1, 'a1 coq_Z)
      equiconsistent, 'a1 coq_Z complete) prod) prod

    val lemma8 : formula -> formula list -> __ -> (__, __) sum

    val leq_bott : formula -> leq
   end

  type ('t1, 't2) extension = formula -> 't2 -> 't1

  type ('axioms, 't) theory =
    formula -> ('t -> (formula list, ((formula, 'axioms) included, (proof,
    unit0) sigT) prod) sigT, (formula list, ((formula, 'axioms) included,
    (proof, unit0) sigT) prod) sigT -> 't) prod

  type 't henkin_complete = formula -> __ -> __ -> 't

  type ('x, 'y) equicons = ('x -> 'y, 'y -> 'x) prod

  type ('t, 'a) coq_AxH = ('a, coq_HA) sum

  type ('t, 'a) coq_TH =
    (formula list, ((formula, ('t, 'a) coq_AxH) included, (proof, unit0)
    sigT) prod) sigT

  val henkin_equiconsistent : ('a1, 'a2) theory -> ('a2, 'a1) coq_TH -> 'a2

  val enrich :
    ('a2, 'a1) theory -> ((('a1, 'a2) coq_AxH, 'a2) extension, ((('a1, 'a2)
    coq_TH, 'a1) extension, ((('a1, 'a2) coq_AxH, ('a1, 'a2) coq_TH) theory,
    (('a1, 'a2) coq_TH henkin_complete, (('a1, 'a2) coq_TH, 'a1) equicons)
    prod) prod) prod) prod

  val theory2filter : ('a2, 'a1) theory -> 'a1 CBAproof_completion.coq_Filter

  type ('t, 'ax) coq_T1 = ('t, 'ax) coq_TH

  val coq_T1theory :
    ('a2, 'a1) theory -> (('a1, 'a2) coq_AxH, ('a1, 'a2) coq_TH) theory

  val coq_T1filter :
    ('a2, 'a1) theory -> ('a1, 'a2) coq_T1 CBAproof_completion.coq_Filter

  type ('t, 'ax) coq_Z' = ('t, 'ax) coq_T1 CBAproof_completion.coq_Z

  val lem15 :
    ('a2, 'a1) theory -> (('a1, 'a2) coq_T1 CBAproof_completion.coq_Z
    CBAproof_completion.coq_Filter, ((('a1, 'a2) coq_T1, ('a1, 'a2) coq_T1
    CBAproof_completion.coq_Z) CBAproof_completion.equiconsistent, ('a1, 'a2)
    coq_T1 CBAproof_completion.coq_Z CBAproof_completion.complete) prod) prod

  val model_existence1 :
    ('a2, 'a1) theory -> ((('a1, 'a2) coq_Z', 'a1) extension, ('a1, ('a1,
    'a2) coq_Z') equicons) prod

  type ('t, 'ax) coq_G = ('t, 'ax) coq_T1 CBAproof_completion.coq_F_

  type ('t, 'ax) coq_GAx = __

  type ('t, 'ax) coq_ZAx = (nat, ('t, 'ax) coq_GAx) sigT

  val coq_GAx_monotone :
    nat -> nat -> CBAproof_completion.le -> formula -> ('a1, 'a2) coq_GAx ->
    ('a1, 'a2) coq_GAx

  val remove_In_neq_In :
    formula list -> formula -> formula -> formula in0 -> formula in0

  val proof_fold_left :
    formula list -> formula -> proof -> CBAproof_completion.leq

  val fold_left_proof :
    formula list -> formula -> CBAproof_completion.leq -> proof

  val coq_F_n_theory :
    ('a2, 'a1) theory -> nat -> (('a1, 'a2) coq_GAx, ('a1, 'a2) coq_G) theory

  val coq_Z'theory :
    ('a2, 'a1) theory -> (('a1, 'a2) coq_ZAx, ('a1, 'a2) coq_Z') theory

  type 'x metaDN = formula -> ('x -> 'x) -> 'x

  val metaDNZ' : ('a2, 'a1) theory -> ('a1, 'a2) coq_Z' metaDN

  val model_existence2 :
    ('a2, 'a1) theory -> (formula -> formula -> ('a1, 'a2) coq_Z' -> ('a1,
    'a2) coq_Z' -> ('a1, 'a2) coq_Z', formula -> formula -> (('a1, 'a2)
    coq_Z' -> ('a1, 'a2) coq_Z') -> ('a1, 'a2) coq_Z') prod

  val model_existence3' : formula -> ('a1, 'a2) coq_Z'

  val model_existence3 :
    ('a2, 'a1) theory -> (formula -> ('a1, 'a2) coq_Z' -> term -> ('a1, 'a2)
    coq_Z', formula -> __ -> __ -> (term -> __ -> ('a1, 'a2) coq_Z') -> ('a1,
    'a2) coq_Z') prod

  val model_existence :
    ('a2, 'a1) theory -> ((('a1, 'a2) coq_Z', 'a1) extension, (('a1, 'a2)
    coq_Z' model, ('a1, ('a1, 'a2) coq_Z') equicons) prod) prod

  val completeness : formula list -> formula -> valid -> proof
 end
