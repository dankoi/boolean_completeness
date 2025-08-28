
type __ = Obj.t

type unit0 =
| Tt

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

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

val remove : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

type 'a in0 = __

type 'a incl = 'a -> 'a in0 -> 'a in0

val in_eq : 'a1 -> 'a1 list -> 'a1 in0

val in_cons : 'a1 -> 'a1 -> 'a1 list -> 'a1 in0 -> 'a1 in0

val incl_tran :
  'a1 list -> 'a1 list -> 'a1 list -> 'a1 incl -> 'a1 incl -> 'a1 incl

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
 end
