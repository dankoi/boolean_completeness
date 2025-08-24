
type __ = Obj.t

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

module Nat :
 sig
  val eqb : nat -> nat -> bool
 end

val remove : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val to_nat : (nat, nat) prod -> nat

module type CBA =
 sig
  type coq_B

  val meet : coq_B -> coq_B -> coq_B

  val join : coq_B -> coq_B -> coq_B

  val bott : coq_B

  val top : coq_B

  val compl : coq_B -> coq_B

  val enum : coq_B -> nat

  val id_B_dec : coq_B -> coq_B -> sumbool
 end

module Coq_filter_completion :
 functor (Coq_cba:CBA) ->
 sig
  type 'f coq_Filter = { nonempty : (Coq_cba.coq_B, 'f) sigT;
                         upwards_closed : (Coq_cba.coq_B -> Coq_cba.coq_B ->
                                          'f -> __ -> 'f);
                         meet_closed : (Coq_cba.coq_B -> Coq_cba.coq_B -> 'f
                                       -> 'f -> 'f) }

  val nonempty : 'a1 coq_Filter -> (Coq_cba.coq_B, 'a1) sigT

  val upwards_closed :
    'a1 coq_Filter -> Coq_cba.coq_B -> Coq_cba.coq_B -> 'a1 -> 'a1

  val meet_closed :
    'a1 coq_Filter -> Coq_cba.coq_B -> Coq_cba.coq_B -> 'a1 -> 'a1 -> 'a1

  type 'x up = (nat, (Coq_cba.coq_B list, (__, (__, __) prod) prod) sigT) sigT

  type 'f union_singl = 'f sumor

  type 'f inconsistent = 'f

  type ('f, 'g) equiconsistent =
    ('f inconsistent -> 'g inconsistent, 'g inconsistent -> 'f inconsistent)
    prod

  type 'f element_complete = ('f, 'f union_singl up) equiconsistent -> 'f

  type 'f complete = Coq_cba.coq_B -> 'f element_complete

  val fold_left_impl : Coq_cba.coq_B list -> ('a2 -> 'a3) -> __ -> __

  val up_filter : 'a1 up coq_Filter

  val filter_top : 'a1 coq_Filter -> 'a1

  val filter_memb_morph :
    'a1 coq_Filter -> Coq_cba.coq_B -> Coq_cba.coq_B -> 'a1 -> 'a1

  val lemma4 : Coq_cba.coq_B list -> 'a1 coq_Filter -> __ -> 'a1

  val lemma61 : Coq_cba.coq_B list -> __ -> (__, 'a3) prod

  val lemma62 : Coq_cba.coq_B list -> (__, 'a3) prod -> __

  val lemma5 :
    Coq_cba.coq_B list -> nat -> __ -> (__, (Coq_cba.coq_B, (__, (__, (__,
    ('a1, 'a1 union_singl up) equiconsistent) prod) prod) prod) sigT) sum

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
 end

type 'a in0 = __

type ('a, 't) included = 'a -> 'a in0 -> 't

val in_eq : 'a1 -> 'a1 list -> 'a1 in0

val in_cons : 'a1 -> 'a1 -> 'a1 list -> 'a1 in0 -> 'a1 in0

val nil_included : ('a1, 'a2) included

val in_app_or :
  'a1 list -> 'a1 list -> 'a1 -> 'a1 in0 -> ('a1 in0, 'a1 in0) sum

val included_lem1 :
  'a1 list -> 'a1 list -> ('a1, 'a2) included -> ('a1, 'a2) included -> ('a1,
  'a2) included

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

  type 'm model = { model_dneg : (formula -> 'm);
                    model_imp_faithful1 : (formula -> formula -> 'm -> 'm ->
                                          'm);
                    model_imp_faithful2 : (formula -> formula -> ('m -> 'm)
                                          -> 'm);
                    model_all_faithful1 : (formula -> 'm -> term -> 'm);
                    model_all_faithful2 : (formula -> __ -> __ -> (term -> __
                                          -> 'm) -> 'm) }

  val formula_dec : formula -> formula -> sumbool

  module CBAproof :
   sig
    val compl : formula -> formula

    val meet : formula -> formula -> formula

    val join : formula -> formula -> formula

    val top : formula

    val id_B_dec : formula -> formula -> sumbool

    val enump : Coq_ccsig.predicate -> nat

    val enumc0 : Coq_ccsig.constant0 -> nat

    val enumfunc : Coq_ccsig.coq_function -> nat

    val enumf : formula -> nat

    val enumt : term -> nat

    val enumc : constant -> nat

    val enum : formula -> nat

    val bott : formula

    type coq_B = formula
   end

  module CBAproof_completion :
   sig
    type 'f coq_Filter = { nonempty : (formula, 'f) sigT;
                           upwards_closed : (formula -> formula -> 'f -> __
                                            -> 'f);
                           meet_closed : (formula -> formula -> 'f -> 'f ->
                                         'f) }

    val nonempty : 'a1 coq_Filter -> (formula, 'a1) sigT

    val upwards_closed : 'a1 coq_Filter -> formula -> formula -> 'a1 -> 'a1

    val meet_closed :
      'a1 coq_Filter -> formula -> formula -> 'a1 -> 'a1 -> 'a1

    type 'x up = (nat, (formula list, (__, (__, __) prod) prod) sigT) sigT

    type 'f union_singl = 'f sumor

    type 'f inconsistent = 'f

    type ('f, 'g) equiconsistent =
      ('f inconsistent -> 'g inconsistent, 'g inconsistent -> 'f
      inconsistent) prod

    type 'f element_complete = ('f, 'f union_singl up) equiconsistent -> 'f

    type 'f complete = formula -> 'f element_complete

    val fold_left_impl : formula list -> ('a2 -> 'a3) -> __ -> __

    val up_filter : 'a1 up coq_Filter

    val filter_top : 'a1 coq_Filter -> 'a1

    val filter_memb_morph : 'a1 coq_Filter -> formula -> formula -> 'a1 -> 'a1

    val lemma4 : formula list -> 'a1 coq_Filter -> __ -> 'a1

    val lemma61 : formula list -> __ -> (__, 'a3) prod

    val lemma62 : formula list -> (__, 'a3) prod -> __

    val lemma5 :
      formula list -> nat -> __ -> (__, (formula, (__, (__, (__, ('a1, 'a1
      union_singl up) equiconsistent) prod) prod) prod) sigT) sum

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
   end

  type ('t1, 't2) extension = formula -> 't2 -> 't1

  type ('axioms, 't) theory =
    formula -> ('t -> (formula list, ((formula, 'axioms) included, (__,
    unit0) sigT) prod) sigT, (formula list, ((formula, 'axioms) included,
    (__, unit0) sigT) prod) sigT -> 't) prod

  type 't henkin_complete = formula -> __ -> __ -> 't

  type ('x, 'y) equicons = ('x -> 'y, 'y -> 'x) prod

  type ('t, 'a) coq_AxH = ('a, __) sum

  type ('t, 'a) coq_TH =
    (formula list, ((formula, ('t, 'a) coq_AxH) included, (__, unit0) sigT)
    prod) sigT

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
 end
