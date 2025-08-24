
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

val remove : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

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
 end
