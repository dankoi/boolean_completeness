
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

type 'a unconvertible = unit0

type 'a crelation = __

type ('a, 'b) arrow = 'a -> 'b

type ('a, 'b) iffT = ('a -> 'b, 'b -> 'a) prod

type ('a, 'r) reflexive = 'a -> 'r

(** val reflexivity : ('a1, 'a2) reflexive -> 'a1 -> 'a2 **)

let reflexivity reflexive0 =
  reflexive0

type ('a, 'r) symmetric = 'a -> 'a -> 'r -> 'r

(** val symmetry : ('a1, 'a2) symmetric -> 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let symmetry symmetric0 =
  symmetric0

type ('a, 'r) transitive = 'a -> 'a -> 'a -> 'r -> 'r -> 'r

(** val transitivity :
    ('a1, 'a2) transitive -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 **)

let transitivity transitive0 =
  transitive0

type ('a, 'r) pER = { pER_Symmetric : ('a, 'r) symmetric;
                      pER_Transitive : ('a, 'r) transitive }

type ('a, 'r) equivalence = { equivalence_Reflexive : ('a, 'r) reflexive;
                              equivalence_Symmetric : ('a, 'r) symmetric;
                              equivalence_Transitive : ('a, 'r) transitive }

(** val equivalence_PER : ('a1, 'a2) equivalence -> ('a1, 'a2) pER **)

let equivalence_PER h =
  { pER_Symmetric = h.equivalence_Symmetric; pER_Transitive =
    h.equivalence_Transitive }

type ('a, 'r, 'x) subrelation = 'a -> 'a -> 'r -> 'x

type ('a, 'r) proper = 'r

type ('a, 'r) properProxy = 'r

(** val reflexive_proper_proxy :
    ('a1, 'a2) reflexive -> 'a1 -> ('a1, 'a2) properProxy **)

let reflexive_proper_proxy h =
  h

type ('a, 'b, 'r, 'x) respectful = 'a -> 'a -> 'r -> 'x

(** val subrelation_respectful :
    ('a1, 'a2, 'a3) subrelation -> ('a4, 'a5, 'a6) subrelation -> ('a1 ->
    'a4, ('a1, 'a4, 'a3, 'a5) respectful, ('a1, 'a4, 'a2, 'a6) respectful)
    subrelation **)

let subrelation_respectful subl subr x y x0 x1 y0 x2 =
  subr (x x1) (y y0) (x0 x1 y0 (subl x1 y0 x2))

(** val subrelation_refl : ('a1, 'a2, 'a2) subrelation **)

let subrelation_refl _ _ x =
  x

(** val subrelation_proper :
    'a1 -> ('a1, 'a2) proper -> 'a1 crelation unconvertible -> ('a1, 'a2,
    'a3) subrelation -> ('a1, 'a3) proper **)

let subrelation_proper m mor _ sub =
  sub m m mor

(** val iffT_arrow_subrelation : (__, __) iffT -> (__, __) arrow **)

let iffT_arrow_subrelation x x0 =
  let Pair (a, _) = x in a x0

(** val iffT_flip_arrow_subrelation : (__, __) iffT -> (__, __) arrow **)

let iffT_flip_arrow_subrelation x x0 =
  let Pair (_, b) = x in b x0

(** val trans_co_impl_type_morphism_obligation_1 :
    ('a1, 'a2) transitive -> 'a1 -> ('a1, __, 'a2, (__, __) arrow) respectful **)

let trans_co_impl_type_morphism_obligation_1 h x x0 y x1 x2 =
  transitivity (Obj.magic h) x x0 y x2 (Obj.magic x1)

(** val trans_co_impl_type_morphism :
    ('a1, 'a2) transitive -> 'a1 -> (__, ('a1, __, 'a2, (__, __) arrow)
    respectful) proper **)

let trans_co_impl_type_morphism =
  trans_co_impl_type_morphism_obligation_1

(** val trans_sym_co_inv_impl_type_morphism_obligation_1 :
    ('a1, 'a2) pER -> 'a1 -> ('a1, __, 'a2, (__, __) arrow) respectful **)

let trans_sym_co_inv_impl_type_morphism_obligation_1 h x x0 y x1 x2 =
  transitivity (Obj.magic h).pER_Transitive x y x0 x2
    (symmetry (Obj.magic h).pER_Symmetric x0 y (Obj.magic x1))

(** val trans_sym_co_inv_impl_type_morphism :
    ('a1, 'a2) pER -> 'a1 -> (__, ('a1, __, 'a2, (__, __) arrow) respectful)
    proper **)

let trans_sym_co_inv_impl_type_morphism =
  trans_sym_co_inv_impl_type_morphism_obligation_1

(** val trans_co_eq_inv_arrow_morphism_obligation_1 :
    ('a1, 'a2) transitive -> 'a1 -> 'a1 -> 'a2 -> 'a1 -> 'a1 -> (__, __) arrow **)

let trans_co_eq_inv_arrow_morphism_obligation_1 h x y x0 y0 _ x1 =
  transitivity (Obj.magic h) x y y0 (Obj.magic x0) x1

(** val trans_co_eq_inv_arrow_morphism :
    ('a1, 'a2) transitive -> 'a1 -> 'a1 -> 'a2 -> 'a1 -> 'a1 -> (__, __) arrow **)

let trans_co_eq_inv_arrow_morphism =
  trans_co_eq_inv_arrow_morphism_obligation_1

(** val pER_type_morphism_obligation_1 :
    ('a1, 'a2) pER -> ('a1, __, 'a2, ('a1, __, 'a2, (__, __) iffT)
    respectful) respectful **)

let pER_type_morphism_obligation_1 h x y x0 x1 y0 x2 =
  Pair ((fun x3 ->
    transitivity (Obj.magic h).pER_Transitive y x1 y0
      (transitivity (Obj.magic h).pER_Transitive y x x1
        (symmetry (Obj.magic h).pER_Symmetric x y (Obj.magic x0)) x3)
      (Obj.magic x2)),
    (fun x3 ->
    transitivity (Obj.magic h).pER_Transitive x y x1 (Obj.magic x0)
      (transitivity (Obj.magic h).pER_Transitive y y0 x1 x3
        (symmetry (Obj.magic h).pER_Symmetric x1 y0 (Obj.magic x2)))))

(** val pER_type_morphism :
    ('a1, 'a2) pER -> (__, ('a1, __, 'a2, ('a1, __, 'a2, (__, __) iffT)
    respectful) respectful) proper **)

let pER_type_morphism =
  pER_type_morphism_obligation_1

(** val reflexive_partial_app_morphism :
    ('a1 -> 'a2) -> ('a1 -> 'a2, ('a1, 'a2, 'a3, 'a4) respectful) proper ->
    'a1 -> ('a1, 'a3) properProxy -> ('a2, 'a4) proper **)

let reflexive_partial_app_morphism _ h x h0 =
  h x x h0

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')
 end

(** val remove : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec remove eq_dec x = function
| Nil -> Nil
| Cons (y, tl) ->
  (match eq_dec x y with
   | Left -> remove eq_dec x tl
   | Right -> Cons (y, (remove eq_dec x tl)))

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, l0) -> fold_left f l0 (f a0 b)

(** val to_nat : (nat, nat) prod -> nat **)

let to_nat = function
| Pair (x, y) ->
  add y
    (let rec f = function
     | O -> O
     | S n0 -> add (S n0) (f n0)
     in f (add y x))

type 'a in0 = __

type 'a incl = 'a -> 'a in0 -> 'a in0

type ('a, 't) included = 'a -> 'a in0 -> 't

(** val in_eq : 'a1 -> 'a1 list -> 'a1 in0 **)

let in_eq _ _ =
  Obj.magic (Inl __)

(** val in_cons : 'a1 -> 'a1 -> 'a1 list -> 'a1 in0 -> 'a1 in0 **)

let in_cons _ _ _ h =
  Obj.magic (Inr h)

(** val nil_included : ('a1, 'a2) included **)

let nil_included _ _ =
  assert false (* absurd case *)

(** val nil_lem1 : 'a1 list -> 'a1 incl **)

let nil_lem1 _ _ _ =
  assert false (* absurd case *)

(** val in_app_or :
    'a1 list -> 'a1 list -> 'a1 -> 'a1 in0 -> ('a1 in0, 'a1 in0) sum **)

let rec in_app_or l m a h =
  match l with
  | Nil -> Inr h
  | Cons (_, l0) ->
    (match Obj.magic h with
     | Inl _ -> Inl (Obj.magic (Inl __))
     | Inr b ->
       (match in_app_or l0 m a b with
        | Inl a0 -> Inl (Obj.magic (Inr a0))
        | Inr b0 -> Inr b0))

(** val in_or_app :
    'a1 list -> 'a1 list -> 'a1 -> ('a1 in0, 'a1 in0) sum -> 'a1 in0 **)

let rec in_or_app l m a h =
  match l with
  | Nil -> (match h with
            | Inl _ -> assert false (* absurd case *)
            | Inr b -> b)
  | Cons (_, l0) ->
    (match h with
     | Inl a0 ->
       (match Obj.magic a0 with
        | Inl _ -> Obj.magic (Inl __)
        | Inr b -> Obj.magic (Inr (in_or_app l0 m a (Inl b))))
     | Inr b -> Obj.magic (Inr (in_or_app l0 m a (Inr b))))

(** val included_lem1 :
    'a1 list -> 'a1 list -> ('a1, 'a2) included -> ('a1, 'a2) included ->
    ('a1, 'a2) included **)

let included_lem1 l1 l2 x x0 f x1 =
  let s = in_app_or l1 l2 f x1 in
  (match s with
   | Inl i -> x f i
   | Inr i -> x0 f i)

(** val incl_tran :
    'a1 list -> 'a1 list -> 'a1 list -> 'a1 incl -> 'a1 incl -> 'a1 incl **)

let incl_tran _ _ _ h h0 a h1 =
  h0 a (h a h1)

(** val incl_refl : 'a1 list -> 'a1 incl **)

let incl_refl _ _ h =
  h

(** val in_dec :
    ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> ('a1 in0, 'a1 in0 ->
    empty_set) sum **)

let rec in_dec h a = function
| Nil -> Inr (fun h0 -> Obj.magic h0)
| Cons (y, l0) ->
  let s = h y a in
  (match s with
   | Left -> Inl (Obj.magic (Inl __))
   | Right ->
     (match in_dec h a l0 with
      | Inl i -> Inl (Obj.magic (Inr i))
      | Inr e ->
        Inr (fun h0 ->
          match Obj.magic h0 with
          | Inl _ -> assert false (* absurd case *)
          | Inr i -> e i)))

(** val incl_appl :
    'a1 list -> 'a1 list -> 'a1 list -> 'a1 incl -> 'a1 incl **)

let incl_appl _ m n h a h0 =
  in_or_app n m a (Inl (h a h0))

(** val incl_appr :
    'a1 list -> 'a1 list -> 'a1 list -> 'a1 incl -> 'a1 incl **)

let incl_appr _ m n h a h0 =
  in_or_app m n a (Inr (h a h0))

(** val in_inv : 'a1 -> 'a1 -> 'a1 list -> 'a1 in0 -> (__, 'a1 in0) sum **)

let in_inv _ _ _ h =
  Obj.magic h

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

module Coq_filter_completion =
 functor (Coq_cba:CBA) ->
 struct
  (** val eq_B_relation : (Coq_cba.coq_B, Coq_cba.eq_B) equivalence **)

  let eq_B_relation =
    { equivalence_Reflexive = Coq_cba.eq_B_refl; equivalence_Symmetric =
      Coq_cba.eq_B_symm; equivalence_Transitive = Coq_cba.eq_B_trans }

  (** val meet_morphism :
      (Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.coq_B, (Coq_cba.coq_B,
      Coq_cba.coq_B -> Coq_cba.coq_B, Coq_cba.eq_B, (Coq_cba.coq_B,
      Coq_cba.coq_B, Coq_cba.eq_B, Coq_cba.eq_B) respectful) respectful)
      proper **)

  let meet_morphism =
    Coq_cba.eq_B_meet_morph

  (** val join_morphism :
      (Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.coq_B, (Coq_cba.coq_B,
      Coq_cba.coq_B -> Coq_cba.coq_B, Coq_cba.eq_B, (Coq_cba.coq_B,
      Coq_cba.coq_B, Coq_cba.eq_B, Coq_cba.eq_B) respectful) respectful)
      proper **)

  let join_morphism =
    Coq_cba.eq_B_join_morph

  type leq = Coq_cba.eq_B

  type ('a, 'b) ciff = ('a -> 'b, 'b -> 'a) prod

  (** val leq' :
      Coq_cba.coq_B -> Coq_cba.coq_B -> (leq, Coq_cba.eq_B) ciff **)

  let leq' x y =
    Pair ((fun h ->
      Obj.magic trans_co_eq_inv_arrow_morphism
        eq_B_relation.equivalence_Transitive (Coq_cba.join x y)
        (Coq_cba.join (Coq_cba.meet x y) y)
        (join_morphism x (Coq_cba.meet x y)
          (symmetry eq_B_relation.equivalence_Symmetric (Coq_cba.meet x y) x
            h)
          y y (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive y))
        y y
        (let lemma = Coq_cba.meet_comm x y in
         trans_co_eq_inv_arrow_morphism eq_B_relation.equivalence_Transitive
           (Coq_cba.join (Coq_cba.meet x y) y)
           (Coq_cba.join (Coq_cba.meet y x) y)
           (join_morphism (Coq_cba.meet x y) (Coq_cba.meet y x) lemma y y
             (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive y))
           y y
           (let lemma0 = Coq_cba.join_comm (Coq_cba.meet y x) y in
            trans_co_eq_inv_arrow_morphism
              eq_B_relation.equivalence_Transitive
              (Coq_cba.join (Coq_cba.meet y x) y)
              (Coq_cba.join y (Coq_cba.meet y x)) lemma0 y y
              (Obj.magic Coq_cba.join_absorb y x)))),
      (fun h ->
      Obj.magic trans_co_eq_inv_arrow_morphism
        eq_B_relation.equivalence_Transitive (Coq_cba.meet x y)
        (Coq_cba.meet x (Coq_cba.join x y))
        (reflexive_partial_app_morphism Coq_cba.meet meet_morphism x
          (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive x) y
          (Coq_cba.join x y)
          (symmetry eq_B_relation.equivalence_Symmetric (Coq_cba.join x y) y
            h))
        x x (Coq_cba.meet_absorb x y)))

  type 'f coq_Filter = { nonempty : (Coq_cba.coq_B, 'f) sigT;
                         upwards_closed : (Coq_cba.coq_B -> Coq_cba.coq_B ->
                                          'f -> leq -> 'f);
                         meet_closed : (Coq_cba.coq_B -> Coq_cba.coq_B -> 'f
                                       -> 'f -> 'f) }

  (** val nonempty : 'a1 coq_Filter -> (Coq_cba.coq_B, 'a1) sigT **)

  let nonempty f =
    f.nonempty

  (** val upwards_closed :
      'a1 coq_Filter -> Coq_cba.coq_B -> Coq_cba.coq_B -> 'a1 -> leq -> 'a1 **)

  let upwards_closed f =
    f.upwards_closed

  (** val meet_closed :
      'a1 coq_Filter -> Coq_cba.coq_B -> Coq_cba.coq_B -> 'a1 -> 'a1 -> 'a1 **)

  let meet_closed f =
    f.meet_closed

  type 'x up =
    (nat, (Coq_cba.coq_B list, (__, (__, leq) prod) prod) sigT) sigT

  type 'f union_singl = 'f sumor

  type 'f inconsistent = 'f

  type ('f, 'g) equiconsistent =
    ('f inconsistent -> 'g inconsistent, 'g inconsistent -> 'f inconsistent)
    prod

  type 'f element_complete = ('f, 'f union_singl up) equiconsistent -> 'f

  type 'f complete = Coq_cba.coq_B -> 'f element_complete

  (** val leq_refl : Coq_cba.coq_B -> leq **)

  let leq_refl =
    Coq_cba.meet_idem

  (** val leq_trans :
      Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.coq_B -> leq -> leq -> leq **)

  let leq_trans x y z x0 x1 =
    subrelation_proper (Obj.magic __)
      (pER_type_morphism (equivalence_PER eq_B_relation)) Tt
      (subrelation_respectful subrelation_refl
        (subrelation_respectful subrelation_refl
          (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation))))
      (Coq_cba.meet x z) (Coq_cba.meet (Coq_cba.meet x y) z)
      (meet_morphism x (Coq_cba.meet x y)
        (symmetry eq_B_relation.equivalence_Symmetric (Coq_cba.meet x y) x x0)
        z z (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive z))
      x (Coq_cba.meet x y)
      (symmetry eq_B_relation.equivalence_Symmetric (Coq_cba.meet x y) x x0)
      (let lemma = Coq_cba.meet_assoc x y z in
       trans_co_eq_inv_arrow_morphism eq_B_relation.equivalence_Transitive
         (Coq_cba.meet (Coq_cba.meet x y) z)
         (Coq_cba.meet x (Coq_cba.meet y z))
         (symmetry eq_B_relation.equivalence_Symmetric
           (Coq_cba.meet x (Coq_cba.meet y z))
           (Coq_cba.meet (Coq_cba.meet x y) z) lemma)
         (Coq_cba.meet x y) (Coq_cba.meet x y)
         (trans_co_eq_inv_arrow_morphism eq_B_relation.equivalence_Transitive
           (Coq_cba.meet x (Coq_cba.meet y z)) (Coq_cba.meet x y)
           (reflexive_partial_app_morphism Coq_cba.meet meet_morphism x
             (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive x)
             (Coq_cba.meet y z) y x1)
           (Coq_cba.meet x y) (Coq_cba.meet x y)
           (reflexivity (Obj.magic eq_B_relation).equivalence_Reflexive
             (Coq_cba.meet x y))))

  (** val eq_B_leq : Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.eq_B -> leq **)

  let eq_B_leq x y h0 =
    subrelation_proper (Obj.magic __)
      (pER_type_morphism (equivalence_PER eq_B_relation)) Tt
      (subrelation_respectful subrelation_refl
        (subrelation_respectful subrelation_refl
          (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation))))
      (Coq_cba.meet x y) (Coq_cba.meet y y)
      (meet_morphism x y h0 y y
        (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive y))
      x y h0 (Coq_cba.meet_idem y)

  (** val leq_morphism :
      (__, (Coq_cba.coq_B, __, Coq_cba.eq_B, (Coq_cba.coq_B, __,
      Coq_cba.eq_B, (__, __) ciff) respectful) respectful) proper **)

  let leq_morphism x y h x0 y0 h0 =
    Pair ((fun h1 ->
      Obj.magic leq_trans y x y0
        (eq_B_leq y x (symmetry eq_B_relation.equivalence_Symmetric x y h))
        (leq_trans x x0 y0 (Obj.magic h1) (eq_B_leq x0 y0 h0))),
      (fun h1 ->
      Obj.magic leq_trans x y x0 (eq_B_leq x y h)
        (leq_trans y y0 x0 (Obj.magic h1)
          (eq_B_leq y0 x0
            (symmetry eq_B_relation.equivalence_Symmetric x0 y0 h0)))))

  (** val meet_leq_compat :
      Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.coq_B -> leq
      -> leq -> leq **)

  let meet_leq_compat a b c d x x0 =
    let lemma = Coq_cba.meet_assoc a c (Coq_cba.meet b d) in
    Obj.magic trans_co_eq_inv_arrow_morphism
      eq_B_relation.equivalence_Transitive
      (Coq_cba.meet (Coq_cba.meet a c) (Coq_cba.meet b d))
      (Coq_cba.meet a (Coq_cba.meet c (Coq_cba.meet b d)))
      (symmetry eq_B_relation.equivalence_Symmetric
        (Coq_cba.meet a (Coq_cba.meet c (Coq_cba.meet b d)))
        (Coq_cba.meet (Coq_cba.meet a c) (Coq_cba.meet b d)) lemma)
      (Coq_cba.meet a c) (Coq_cba.meet a c)
      (let h1 = Coq_cba.meet_comm b d in
       let h2 =
         let lemma0 = Coq_cba.meet_assoc c d b in
         trans_co_eq_inv_arrow_morphism eq_B_relation.equivalence_Transitive
           (Coq_cba.meet c (Coq_cba.meet d b))
           (Coq_cba.meet (Coq_cba.meet c d) b) lemma0 (Coq_cba.meet b c)
           (Coq_cba.meet b c)
           (trans_co_eq_inv_arrow_morphism
             eq_B_relation.equivalence_Transitive
             (Coq_cba.meet (Coq_cba.meet c d) b) (Coq_cba.meet c b)
             (meet_morphism (Coq_cba.meet c d) c x0 b b
               (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive b))
             (Coq_cba.meet b c) (Coq_cba.meet b c)
             (Obj.magic Coq_cba.meet_comm c b))
       in
       trans_co_eq_inv_arrow_morphism eq_B_relation.equivalence_Transitive
         (Coq_cba.meet a (Coq_cba.meet c (Coq_cba.meet b d)))
         (Coq_cba.meet a (Coq_cba.meet c (Coq_cba.meet d b)))
         (reflexive_partial_app_morphism Coq_cba.meet meet_morphism a
           (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive a)
           (Coq_cba.meet c (Coq_cba.meet b d))
           (Coq_cba.meet c (Coq_cba.meet d b))
           (reflexive_partial_app_morphism Coq_cba.meet meet_morphism c
             (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive c)
             (Coq_cba.meet b d) (Coq_cba.meet d b) h1))
         (Coq_cba.meet a c) (Coq_cba.meet a c)
         (trans_co_eq_inv_arrow_morphism eq_B_relation.equivalence_Transitive
           (Coq_cba.meet a (Coq_cba.meet c (Coq_cba.meet d b)))
           (Coq_cba.meet a (Coq_cba.meet b c))
           (reflexive_partial_app_morphism Coq_cba.meet
             (Obj.magic meet_morphism) a
             (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive a)
             (Coq_cba.meet c (Coq_cba.meet d b)) (Coq_cba.meet b c) h2)
           (Coq_cba.meet a c) (Coq_cba.meet a c)
           (let lemma0 = Coq_cba.meet_assoc a b c in
            trans_co_eq_inv_arrow_morphism
              eq_B_relation.equivalence_Transitive
              (Coq_cba.meet a (Coq_cba.meet b c))
              (Coq_cba.meet (Coq_cba.meet a b) c) lemma0 (Coq_cba.meet a c)
              (Coq_cba.meet a c)
              (trans_co_eq_inv_arrow_morphism
                eq_B_relation.equivalence_Transitive
                (Coq_cba.meet (Coq_cba.meet a b) c) (Coq_cba.meet a c)
                (meet_morphism (Coq_cba.meet a b) a x c c
                  (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive
                    c))
                (Coq_cba.meet a c) (Coq_cba.meet a c)
                (reflexivity (Obj.magic eq_B_relation).equivalence_Reflexive
                  (Coq_cba.meet a c))))))

  (** val fold_left_meet_morphism :
      Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.coq_B list -> Coq_cba.eq_B ->
      Coq_cba.eq_B **)

  let rec fold_left_meet_morphism x y bs x0 =
    match bs with
    | Nil -> x0
    | Cons (y0, l) ->
      Obj.magic fold_left_meet_morphism (Obj.magic Coq_cba.meet x y0)
        (Obj.magic Coq_cba.meet y y0) l
        (trans_co_eq_inv_arrow_morphism eq_B_relation.equivalence_Transitive
          (Coq_cba.meet x y0) (Coq_cba.meet y y0)
          (meet_morphism x y x0 y0 y0
            (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive y0))
          (Coq_cba.meet y y0) (Coq_cba.meet y y0)
          (reflexivity (Obj.magic eq_B_relation).equivalence_Reflexive
            (Coq_cba.meet y y0)))

  (** val fold_left_meet_cons :
      Coq_cba.coq_B list -> Coq_cba.coq_B -> Coq_cba.eq_B **)

  let rec fold_left_meet_cons = function
  | Nil -> (fun b -> Coq_cba.meet_comm Coq_cba.top b)
  | Cons (y, l0) ->
    let iHbs = fold_left_meet_cons l0 in
    (fun b ->
    let lemma = iHbs y in
    Obj.magic trans_sym_co_inv_impl_type_morphism
      (equivalence_PER eq_B_relation)
      (fold_left Coq_cba.meet l0
        (Coq_cba.meet (Coq_cba.meet Coq_cba.top b) y))
      (Coq_cba.meet b
        (fold_left Coq_cba.meet l0 (Coq_cba.meet Coq_cba.top y)))
      (Coq_cba.meet b
        (Coq_cba.meet y (fold_left Coq_cba.meet l0 Coq_cba.top)))
      (reflexive_partial_app_morphism Coq_cba.meet meet_morphism b
        (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive b)
        (fold_left Coq_cba.meet l0 (Coq_cba.meet Coq_cba.top y))
        (Coq_cba.meet y (fold_left Coq_cba.meet l0 Coq_cba.top)) lemma)
      (let lemma0 =
         Coq_cba.meet_assoc b y (fold_left Coq_cba.meet l0 Coq_cba.top)
       in
       trans_sym_co_inv_impl_type_morphism (equivalence_PER eq_B_relation)
         (fold_left Coq_cba.meet l0
           (Coq_cba.meet (Coq_cba.meet Coq_cba.top b) y))
         (Coq_cba.meet b
           (Coq_cba.meet y (fold_left Coq_cba.meet l0 Coq_cba.top)))
         (Coq_cba.meet (Coq_cba.meet b y)
           (fold_left Coq_cba.meet l0 Coq_cba.top))
         lemma0
         (transitivity (Obj.magic eq_B_relation).equivalence_Transitive
           (fold_left Coq_cba.meet l0
             (Coq_cba.meet (Coq_cba.meet Coq_cba.top b) y))
           (fold_left Coq_cba.meet l0
             (Coq_cba.meet Coq_cba.top (Coq_cba.meet b y)))
           (Coq_cba.meet (Coq_cba.meet b y)
             (fold_left Coq_cba.meet l0 Coq_cba.top))
           (Obj.magic fold_left_meet_morphism
             (Coq_cba.meet (Coq_cba.meet Coq_cba.top b) y)
             (Coq_cba.meet Coq_cba.top (Coq_cba.meet b y)) l0
             (let lemma1 = Coq_cba.meet_assoc Coq_cba.top b y in
              Obj.magic trans_co_eq_inv_arrow_morphism
                eq_B_relation.equivalence_Transitive
                (Coq_cba.meet (Coq_cba.meet Coq_cba.top b) y)
                (Coq_cba.meet Coq_cba.top (Coq_cba.meet b y))
                (symmetry eq_B_relation.equivalence_Symmetric
                  (Coq_cba.meet Coq_cba.top (Coq_cba.meet b y))
                  (Coq_cba.meet (Coq_cba.meet Coq_cba.top b) y) lemma1)
                (Coq_cba.meet Coq_cba.top (Coq_cba.meet b y))
                (Coq_cba.meet Coq_cba.top (Coq_cba.meet b y))
                (reflexivity (Obj.magic eq_B_relation).equivalence_Reflexive
                  (Coq_cba.meet Coq_cba.top (Coq_cba.meet b y)))))
           (Obj.magic iHbs (Coq_cba.meet b y)))))

  (** val fold_left_impl : Coq_cba.coq_B list -> ('a2 -> 'a3) -> __ -> __ **)

  let rec fold_left_impl l h =
    match l with
    | Nil -> Obj.magic h
    | Cons (_, l0) ->
      (fun x ->
        Obj.magic fold_left_impl l0 (fun h1 ->
          let Pair (a, b) = h1 in let h2 = h a in Pair (h2, b)) x)

  (** val fold_left_app_lem :
      Coq_cba.coq_B list -> Coq_cba.coq_B list -> Coq_cba.eq_B **)

  let rec fold_left_app_lem xs ys =
    match xs with
    | Nil ->
      let lemma = Coq_cba.meet_top (fold_left Coq_cba.meet ys Coq_cba.top) in
      Obj.magic trans_sym_co_inv_impl_type_morphism
        (equivalence_PER eq_B_relation)
        (fold_left Coq_cba.meet ys Coq_cba.top)
        (Coq_cba.meet Coq_cba.top (fold_left Coq_cba.meet ys Coq_cba.top))
        (fold_left Coq_cba.meet ys Coq_cba.top) lemma
        (reflexivity (Obj.magic eq_B_relation).equivalence_Reflexive
          (fold_left Coq_cba.meet ys Coq_cba.top))
    | Cons (y, l) ->
      let lemma = fold_left_meet_cons (app l ys) y in
      Obj.magic trans_co_eq_inv_arrow_morphism
        eq_B_relation.equivalence_Transitive
        (fold_left Coq_cba.meet (Cons (y, (app l ys))) Coq_cba.top)
        (Coq_cba.meet y (fold_left Coq_cba.meet (app l ys) Coq_cba.top))
        lemma
        (Coq_cba.meet (fold_left Coq_cba.meet (Cons (y, l)) Coq_cba.top)
          (fold_left Coq_cba.meet ys Coq_cba.top))
        (Coq_cba.meet (fold_left Coq_cba.meet (Cons (y, l)) Coq_cba.top)
          (fold_left Coq_cba.meet ys Coq_cba.top))
        (let lemma0 = fold_left_meet_cons l y in
         trans_sym_co_inv_impl_type_morphism (equivalence_PER eq_B_relation)
           (Coq_cba.meet y (fold_left Coq_cba.meet (app l ys) Coq_cba.top))
           (Coq_cba.meet (fold_left Coq_cba.meet (Cons (y, l)) Coq_cba.top)
             (fold_left Coq_cba.meet ys Coq_cba.top))
           (Coq_cba.meet
             (Coq_cba.meet y (fold_left Coq_cba.meet l Coq_cba.top))
             (fold_left Coq_cba.meet ys Coq_cba.top))
           (meet_morphism (fold_left Coq_cba.meet (Cons (y, l)) Coq_cba.top)
             (Coq_cba.meet y (fold_left Coq_cba.meet l Coq_cba.top)) lemma0
             (fold_left Coq_cba.meet ys Coq_cba.top)
             (fold_left Coq_cba.meet ys Coq_cba.top)
             (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive
               (fold_left Coq_cba.meet ys Coq_cba.top)))
           (let lemma1 =
              Coq_cba.meet_assoc y (fold_left Coq_cba.meet l Coq_cba.top)
                (fold_left Coq_cba.meet ys Coq_cba.top)
            in
            trans_sym_co_inv_impl_type_morphism
              (equivalence_PER eq_B_relation)
              (Coq_cba.meet y (fold_left Coq_cba.meet (app l ys) Coq_cba.top))
              (Coq_cba.meet
                (Coq_cba.meet y (fold_left Coq_cba.meet l Coq_cba.top))
                (fold_left Coq_cba.meet ys Coq_cba.top))
              (Coq_cba.meet y
                (Coq_cba.meet (fold_left Coq_cba.meet l Coq_cba.top)
                  (fold_left Coq_cba.meet ys Coq_cba.top)))
              (symmetry eq_B_relation.equivalence_Symmetric
                (Coq_cba.meet y
                  (Coq_cba.meet (fold_left Coq_cba.meet l Coq_cba.top)
                    (fold_left Coq_cba.meet ys Coq_cba.top)))
                (Coq_cba.meet
                  (Coq_cba.meet y (fold_left Coq_cba.meet l Coq_cba.top))
                  (fold_left Coq_cba.meet ys Coq_cba.top))
                lemma1)
              (trans_co_eq_inv_arrow_morphism
                eq_B_relation.equivalence_Transitive
                (Coq_cba.meet y
                  (fold_left Coq_cba.meet (app l ys) Coq_cba.top))
                (Coq_cba.meet y
                  (Coq_cba.meet (fold_left Coq_cba.meet l Coq_cba.top)
                    (fold_left Coq_cba.meet ys Coq_cba.top)))
                (reflexive_partial_app_morphism Coq_cba.meet meet_morphism y
                  (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive
                    y)
                  (fold_left Coq_cba.meet (app l ys) Coq_cba.top)
                  (Coq_cba.meet (fold_left Coq_cba.meet l Coq_cba.top)
                    (fold_left Coq_cba.meet ys Coq_cba.top))
                  (fold_left_app_lem l ys))
                (Coq_cba.meet y
                  (Coq_cba.meet (fold_left Coq_cba.meet l Coq_cba.top)
                    (fold_left Coq_cba.meet ys Coq_cba.top)))
                (Coq_cba.meet y
                  (Coq_cba.meet (fold_left Coq_cba.meet l Coq_cba.top)
                    (fold_left Coq_cba.meet ys Coq_cba.top)))
                (reflexivity (Obj.magic eq_B_relation).equivalence_Reflexive
                  (Coq_cba.meet y
                    (Coq_cba.meet (fold_left Coq_cba.meet l Coq_cba.top)
                      (fold_left Coq_cba.meet ys Coq_cba.top)))))))

  (** val up_filter : 'a1 up coq_Filter **)

  let up_filter =
    { nonempty = (ExistT (Coq_cba.top, (ExistT (O, (ExistT (Nil, (Pair (__,
      (Pair ((Obj.magic Tt), (leq_refl Coq_cba.top)))))))))));
      upwards_closed = (fun x y x0 x1 ->
      let ExistT (x2, s) = x0 in
      let ExistT (x3, p) = s in
      let Pair (_, p0) = p in
      let Pair (f, l) = p0 in
      ExistT (x2, (ExistT (x3, (Pair (__, (Pair (f,
      (leq_trans (fold_left Coq_cba.meet x3 Coq_cba.top) x y l x1)))))))));
      meet_closed = (fun x y x0 x1 ->
      let ExistT (x2, s) = x0 in
      let ExistT (x3, p) = s in
      let Pair (_, p0) = p in
      let Pair (f, l) = p0 in
      let ExistT (x4, s0) = x1 in
      let ExistT (x5, p1) = s0 in
      let Pair (_, p2) = p1 in
      let Pair (f0, l0) = p2 in
      ExistT ((add x2 x4), (ExistT ((app x3 x5), (Pair (__, (Pair
      ((fold_left_impl x5 (fun _ -> f) f0),
      (leq_trans (fold_left Coq_cba.meet (app x3 x5) Coq_cba.top)
        (Coq_cba.meet (fold_left Coq_cba.meet x3 Coq_cba.top)
          (fold_left Coq_cba.meet x5 Coq_cba.top))
        (Coq_cba.meet x y)
        (eq_B_leq (fold_left Coq_cba.meet (app x3 x5) Coq_cba.top)
          (Coq_cba.meet (fold_left Coq_cba.meet x3 Coq_cba.top)
            (fold_left Coq_cba.meet x5 Coq_cba.top))
          (fold_left_app_lem x3 x5))
        (meet_leq_compat (fold_left Coq_cba.meet x3 Coq_cba.top) x
          (fold_left Coq_cba.meet x5 Coq_cba.top) y l l0)))))))))) }

  (** val filter_top : 'a1 coq_Filter -> 'a1 **)

  let filter_top x =
    let s = x.nonempty in
    let ExistT (x0, f) = s in
    x.upwards_closed x0 Coq_cba.top f
      (let lemma = Coq_cba.meet_comm x0 Coq_cba.top in
       Obj.magic trans_co_eq_inv_arrow_morphism
         eq_B_relation.equivalence_Transitive (Coq_cba.meet x0 Coq_cba.top)
         (Coq_cba.meet Coq_cba.top x0) lemma x0 x0
         (let lemma0 = Coq_cba.meet_top x0 in
          trans_co_eq_inv_arrow_morphism eq_B_relation.equivalence_Transitive
            (Coq_cba.meet Coq_cba.top x0) x0 lemma0 x0 x0
            (reflexivity (Obj.magic eq_B_relation).equivalence_Reflexive x0)))

  (** val lemma3 : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> 'a1 incl **)

  let rec lemma3 hdec x ys a x0 =
    match ys with
    | Nil -> assert false (* absurd case *)
    | Cons (y, l) ->
      let h' = in_inv y a l x0 in
      (match h' with
       | Inl _ ->
         (match hdec x y with
          | Left -> in_eq y (remove hdec y l)
          | Right ->
            in_cons x y (Cons (y, (remove hdec x l)))
              (in_eq y (remove hdec x l)))
       | Inr i ->
         let iH = lemma3 hdec x l a i in
         (match hdec x y with
          | Left -> iH
          | Right ->
            (match h' with
             | Inl _ ->
               (match Obj.magic iH with
                | Inl _ -> Obj.magic (Inl __)
                | Inr _ -> Obj.magic (Inr (Inl __)))
             | Inr _ ->
               (match Obj.magic iH with
                | Inl _ -> Obj.magic (Inl __)
                | Inr b -> Obj.magic (Inr (Inr b))))))

  (** val lemma2 :
      Coq_cba.coq_B list -> Coq_cba.coq_B list -> Coq_cba.coq_B incl -> leq **)

  let rec lemma2 l c x =
    match l with
    | Nil ->
      let lemma =
        Coq_cba.meet_comm (fold_left Coq_cba.meet c Coq_cba.top) Coq_cba.top
      in
      Obj.magic trans_co_eq_inv_arrow_morphism
        eq_B_relation.equivalence_Transitive
        (Coq_cba.meet (fold_left Coq_cba.meet c Coq_cba.top) Coq_cba.top)
        (Coq_cba.meet Coq_cba.top (fold_left Coq_cba.meet c Coq_cba.top))
        lemma (fold_left Coq_cba.meet c Coq_cba.top)
        (fold_left Coq_cba.meet c Coq_cba.top)
        (let lemma0 = Coq_cba.meet_top (fold_left Coq_cba.meet c Coq_cba.top)
         in
         trans_co_eq_inv_arrow_morphism eq_B_relation.equivalence_Transitive
           (Coq_cba.meet Coq_cba.top (fold_left Coq_cba.meet c Coq_cba.top))
           (fold_left Coq_cba.meet c Coq_cba.top) lemma0
           (fold_left Coq_cba.meet c Coq_cba.top)
           (fold_left Coq_cba.meet c Coq_cba.top)
           (reflexivity (Obj.magic eq_B_relation).equivalence_Reflexive
             (fold_left Coq_cba.meet c Coq_cba.top)))
    | Cons (y, l0) ->
      leq_trans (fold_left Coq_cba.meet c Coq_cba.top)
        (Coq_cba.meet y (fold_left Coq_cba.meet l0 Coq_cba.top))
        (fold_left Coq_cba.meet (Cons (y, l0)) Coq_cba.top)
        (let iHA' = lemma2 l0 c in
         leq_trans (fold_left Coq_cba.meet c Coq_cba.top)
           (Coq_cba.meet y (fold_left Coq_cba.meet c Coq_cba.top))
           (Coq_cba.meet y (fold_left Coq_cba.meet l0 Coq_cba.top))
           (let h' = x y (in_eq y l0) in
            let rec f l1 h'0 =
              match l1 with
              | Nil -> assert false (* absurd case *)
              | Cons (y0, l2) ->
                (match Obj.magic h'0 with
                 | Inl _ ->
                   leq_trans
                     (fold_left Coq_cba.meet (Cons (y, l2)) Coq_cba.top)
                     (Coq_cba.meet y (fold_left Coq_cba.meet l2 Coq_cba.top))
                     (Coq_cba.meet y
                       (fold_left Coq_cba.meet (Cons (y, l2)) Coq_cba.top))
                     (eq_B_leq
                       (fold_left Coq_cba.meet (Cons (y, l2)) Coq_cba.top)
                       (Coq_cba.meet y
                         (fold_left Coq_cba.meet l2 Coq_cba.top))
                       (fold_left_meet_cons l2 y))
                     (leq_trans
                       (Coq_cba.meet y
                         (fold_left Coq_cba.meet l2 Coq_cba.top))
                       (Coq_cba.meet (Coq_cba.meet y y)
                         (fold_left Coq_cba.meet l2 Coq_cba.top))
                       (Coq_cba.meet y
                         (fold_left Coq_cba.meet (Cons (y, l2)) Coq_cba.top))
                       (eq_B_leq
                         (Coq_cba.meet y
                           (fold_left Coq_cba.meet l2 Coq_cba.top))
                         (Coq_cba.meet (Coq_cba.meet y y)
                           (fold_left Coq_cba.meet l2 Coq_cba.top))
                         (let lemma = Coq_cba.meet_idem y in
                          Obj.magic trans_sym_co_inv_impl_type_morphism
                            (equivalence_PER eq_B_relation)
                            (Coq_cba.meet y
                              (fold_left Coq_cba.meet l2 Coq_cba.top))
                            (Coq_cba.meet (Coq_cba.meet y y)
                              (fold_left Coq_cba.meet l2 Coq_cba.top))
                            (Coq_cba.meet y
                              (fold_left Coq_cba.meet l2 Coq_cba.top))
                            (meet_morphism (Coq_cba.meet y y) y lemma
                              (fold_left Coq_cba.meet l2 Coq_cba.top)
                              (fold_left Coq_cba.meet l2 Coq_cba.top)
                              (reflexive_proper_proxy
                                eq_B_relation.equivalence_Reflexive
                                (fold_left Coq_cba.meet l2 Coq_cba.top)))
                            (reflexivity
                              (Obj.magic eq_B_relation).equivalence_Reflexive
                              (Coq_cba.meet y
                                (fold_left Coq_cba.meet l2 Coq_cba.top)))))
                       (eq_B_leq
                         (Coq_cba.meet (Coq_cba.meet y y)
                           (fold_left Coq_cba.meet l2 Coq_cba.top))
                         (Coq_cba.meet y
                           (fold_left Coq_cba.meet (Cons (y, l2)) Coq_cba.top))
                         (let lemma = fold_left_meet_cons l2 y in
                          Obj.magic trans_sym_co_inv_impl_type_morphism
                            (equivalence_PER eq_B_relation)
                            (Coq_cba.meet (Coq_cba.meet y y)
                              (fold_left Coq_cba.meet l2 Coq_cba.top))
                            (Coq_cba.meet y
                              (fold_left Coq_cba.meet (Cons (y, l2))
                                Coq_cba.top))
                            (Coq_cba.meet y
                              (Coq_cba.meet y
                                (fold_left Coq_cba.meet l2 Coq_cba.top)))
                            (reflexive_partial_app_morphism Coq_cba.meet
                              meet_morphism y
                              (reflexive_proper_proxy
                                eq_B_relation.equivalence_Reflexive y)
                              (fold_left Coq_cba.meet (Cons (y, l2))
                                Coq_cba.top)
                              (Coq_cba.meet y
                                (fold_left Coq_cba.meet l2 Coq_cba.top))
                              lemma)
                            (let lemma0 =
                               Coq_cba.meet_assoc y y
                                 (fold_left Coq_cba.meet l2 Coq_cba.top)
                             in
                             trans_sym_co_inv_impl_type_morphism
                               (equivalence_PER eq_B_relation)
                               (Coq_cba.meet (Coq_cba.meet y y)
                                 (fold_left Coq_cba.meet l2 Coq_cba.top))
                               (Coq_cba.meet y
                                 (Coq_cba.meet y
                                   (fold_left Coq_cba.meet l2 Coq_cba.top)))
                               (Coq_cba.meet (Coq_cba.meet y y)
                                 (fold_left Coq_cba.meet l2 Coq_cba.top))
                               lemma0
                               (reflexivity
                                 (Obj.magic eq_B_relation).equivalence_Reflexive
                                 (Coq_cba.meet (Coq_cba.meet y y)
                                   (fold_left Coq_cba.meet l2 Coq_cba.top)))))))
                 | Inr i ->
                   leq_trans
                     (fold_left Coq_cba.meet (Cons (y0, l2)) Coq_cba.top)
                     (Coq_cba.meet y0 (fold_left Coq_cba.meet l2 Coq_cba.top))
                     (Coq_cba.meet y
                       (fold_left Coq_cba.meet (Cons (y0, l2)) Coq_cba.top))
                     (eq_B_leq
                       (fold_left Coq_cba.meet (Cons (y0, l2)) Coq_cba.top)
                       (Coq_cba.meet y0
                         (fold_left Coq_cba.meet l2 Coq_cba.top))
                       (fold_left_meet_cons l2 y0))
                     (leq_trans
                       (Coq_cba.meet y0
                         (fold_left Coq_cba.meet l2 Coq_cba.top))
                       (Coq_cba.meet
                         (Coq_cba.meet y0
                           (Coq_cba.meet y
                             (fold_left Coq_cba.meet l2 Coq_cba.top)))
                         (Coq_cba.meet y0
                           (Coq_cba.meet y
                             (fold_left Coq_cba.meet l2 Coq_cba.top))))
                       (Coq_cba.meet y
                         (fold_left Coq_cba.meet (Cons (y0, l2)) Coq_cba.top))
                       (leq_trans
                         (Coq_cba.meet y0
                           (fold_left Coq_cba.meet l2 Coq_cba.top))
                         (Coq_cba.meet y0
                           (Coq_cba.meet y
                             (fold_left Coq_cba.meet l2 Coq_cba.top)))
                         (Coq_cba.meet
                           (Coq_cba.meet y0
                             (Coq_cba.meet y
                               (fold_left Coq_cba.meet l2 Coq_cba.top)))
                           (Coq_cba.meet y0
                             (Coq_cba.meet y
                               (fold_left Coq_cba.meet l2 Coq_cba.top))))
                         (meet_leq_compat y0 y0
                           (fold_left Coq_cba.meet l2 Coq_cba.top)
                           (Coq_cba.meet y
                             (fold_left Coq_cba.meet l2 Coq_cba.top))
                           (leq_refl y0) (f l2 i))
                         (eq_B_leq
                           (Coq_cba.meet y0
                             (Coq_cba.meet y
                               (fold_left Coq_cba.meet l2 Coq_cba.top)))
                           (Coq_cba.meet
                             (Coq_cba.meet y0
                               (Coq_cba.meet y
                                 (fold_left Coq_cba.meet l2 Coq_cba.top)))
                             (Coq_cba.meet y0
                               (Coq_cba.meet y
                                 (fold_left Coq_cba.meet l2 Coq_cba.top))))
                           (let lemma =
                              Coq_cba.meet_idem
                                (Coq_cba.meet y0
                                  (Coq_cba.meet y
                                    (fold_left Coq_cba.meet l2 Coq_cba.top)))
                            in
                            Obj.magic trans_sym_co_inv_impl_type_morphism
                              (equivalence_PER eq_B_relation)
                              (Coq_cba.meet y0
                                (Coq_cba.meet y
                                  (fold_left Coq_cba.meet l2 Coq_cba.top)))
                              (Coq_cba.meet
                                (Coq_cba.meet y0
                                  (Coq_cba.meet y
                                    (fold_left Coq_cba.meet l2 Coq_cba.top)))
                                (Coq_cba.meet y0
                                  (Coq_cba.meet y
                                    (fold_left Coq_cba.meet l2 Coq_cba.top))))
                              (Coq_cba.meet y0
                                (Coq_cba.meet y
                                  (fold_left Coq_cba.meet l2 Coq_cba.top)))
                              lemma
                              (reflexivity
                                (Obj.magic eq_B_relation).equivalence_Reflexive
                                (Coq_cba.meet y0
                                  (Coq_cba.meet y
                                    (fold_left Coq_cba.meet l2 Coq_cba.top)))))))
                       (eq_B_leq
                         (Coq_cba.meet
                           (Coq_cba.meet y0
                             (Coq_cba.meet y
                               (fold_left Coq_cba.meet l2 Coq_cba.top)))
                           (Coq_cba.meet y0
                             (Coq_cba.meet y
                               (fold_left Coq_cba.meet l2 Coq_cba.top))))
                         (Coq_cba.meet y
                           (fold_left Coq_cba.meet (Cons (y0, l2))
                             Coq_cba.top))
                         (let lemma = fold_left_meet_cons l2 y0 in
                          Obj.magic trans_sym_co_inv_impl_type_morphism
                            (equivalence_PER eq_B_relation)
                            (Coq_cba.meet
                              (Coq_cba.meet y0
                                (Coq_cba.meet y
                                  (fold_left Coq_cba.meet l2 Coq_cba.top)))
                              (Coq_cba.meet y0
                                (Coq_cba.meet y
                                  (fold_left Coq_cba.meet l2 Coq_cba.top))))
                            (Coq_cba.meet y
                              (fold_left Coq_cba.meet (Cons (y0, l2))
                                Coq_cba.top))
                            (Coq_cba.meet y
                              (Coq_cba.meet y0
                                (fold_left Coq_cba.meet l2 Coq_cba.top)))
                            (reflexive_partial_app_morphism Coq_cba.meet
                              meet_morphism y
                              (reflexive_proper_proxy
                                eq_B_relation.equivalence_Reflexive y)
                              (fold_left Coq_cba.meet (Cons (y0, l2))
                                Coq_cba.top)
                              (Coq_cba.meet y0
                                (fold_left Coq_cba.meet l2 Coq_cba.top))
                              lemma)
                            (let lemma0 =
                               Coq_cba.meet_assoc y y0
                                 (fold_left Coq_cba.meet l2 Coq_cba.top)
                             in
                             trans_sym_co_inv_impl_type_morphism
                               (equivalence_PER eq_B_relation)
                               (Coq_cba.meet
                                 (Coq_cba.meet y0
                                   (Coq_cba.meet y
                                     (fold_left Coq_cba.meet l2 Coq_cba.top)))
                                 (Coq_cba.meet y0
                                   (Coq_cba.meet y
                                     (fold_left Coq_cba.meet l2 Coq_cba.top))))
                               (Coq_cba.meet y
                                 (Coq_cba.meet y0
                                   (fold_left Coq_cba.meet l2 Coq_cba.top)))
                               (Coq_cba.meet (Coq_cba.meet y y0)
                                 (fold_left Coq_cba.meet l2 Coq_cba.top))
                               lemma0
                               (let lemma1 = Coq_cba.meet_comm y y0 in
                                trans_sym_co_inv_impl_type_morphism
                                  (equivalence_PER eq_B_relation)
                                  (Coq_cba.meet
                                    (Coq_cba.meet y0
                                      (Coq_cba.meet y
                                        (fold_left Coq_cba.meet l2
                                          Coq_cba.top)))
                                    (Coq_cba.meet y0
                                      (Coq_cba.meet y
                                        (fold_left Coq_cba.meet l2
                                          Coq_cba.top))))
                                  (Coq_cba.meet (Coq_cba.meet y y0)
                                    (fold_left Coq_cba.meet l2 Coq_cba.top))
                                  (Coq_cba.meet (Coq_cba.meet y0 y)
                                    (fold_left Coq_cba.meet l2 Coq_cba.top))
                                  (meet_morphism (Coq_cba.meet y y0)
                                    (Coq_cba.meet y0 y) lemma1
                                    (fold_left Coq_cba.meet l2 Coq_cba.top)
                                    (fold_left Coq_cba.meet l2 Coq_cba.top)
                                    (reflexive_proper_proxy
                                      eq_B_relation.equivalence_Reflexive
                                      (fold_left Coq_cba.meet l2 Coq_cba.top)))
                                  (let lemma6 =
                                     Coq_cba.meet_assoc y0 y
                                       (fold_left Coq_cba.meet l2 Coq_cba.top)
                                   in
                                   trans_sym_co_inv_impl_type_morphism
                                     (equivalence_PER eq_B_relation)
                                     (Coq_cba.meet
                                       (Coq_cba.meet y0
                                         (Coq_cba.meet y
                                           (fold_left Coq_cba.meet l2
                                             Coq_cba.top)))
                                       (Coq_cba.meet y0
                                         (Coq_cba.meet y
                                           (fold_left Coq_cba.meet l2
                                             Coq_cba.top))))
                                     (Coq_cba.meet (Coq_cba.meet y0 y)
                                       (fold_left Coq_cba.meet l2 Coq_cba.top))
                                     (Coq_cba.meet y0
                                       (Coq_cba.meet y
                                         (fold_left Coq_cba.meet l2
                                           Coq_cba.top)))
                                     (symmetry
                                       eq_B_relation.equivalence_Symmetric
                                       (Coq_cba.meet y0
                                         (Coq_cba.meet y
                                           (fold_left Coq_cba.meet l2
                                             Coq_cba.top)))
                                       (Coq_cba.meet (Coq_cba.meet y0 y)
                                         (fold_left Coq_cba.meet l2
                                           Coq_cba.top))
                                       lemma6)
                                     (Obj.magic leq_refl
                                       (Coq_cba.meet y0
                                         (Coq_cba.meet y
                                           (fold_left Coq_cba.meet l2
                                             Coq_cba.top)))))))))))
            in f c h')
           (meet_leq_compat y y (fold_left Coq_cba.meet c Coq_cba.top)
             (fold_left Coq_cba.meet l0 Coq_cba.top) (leq_refl y)
             (iHA'
               (incl_tran l0 (Cons (y, l0)) c (fun _ x0 ->
                 Obj.magic (Inr x0)) x))))
        (eq_B_leq (Coq_cba.meet y (fold_left Coq_cba.meet l0 Coq_cba.top))
          (fold_left Coq_cba.meet (Cons (y, l0)) Coq_cba.top)
          (symmetry eq_B_relation.equivalence_Symmetric
            (fold_left Coq_cba.meet (Cons (y, l0)) Coq_cba.top)
            (Coq_cba.meet y (fold_left Coq_cba.meet l0 Coq_cba.top))
            (fold_left_meet_cons l0 y)))

  (** val filter_memb_morph :
      'a1 coq_Filter -> Coq_cba.coq_B -> Coq_cba.coq_B -> Coq_cba.eq_B -> 'a1
      -> 'a1 **)

  let filter_memb_morph x x0 y x1 x2 =
    x.upwards_closed x0 y x2 (eq_B_leq x0 y x1)

  (** val lemma4 : Coq_cba.coq_B list -> 'a1 coq_Filter -> __ -> 'a1 **)

  let rec lemma4 xs x x0 =
    match xs with
    | Nil -> filter_top x
    | Cons (y, l) ->
      let iHxs = fun x1 -> lemma4 l x x1 in
      filter_memb_morph x
        (Coq_cba.meet y (fold_left Coq_cba.meet l Coq_cba.top))
        (fold_left Coq_cba.meet (Cons (y, l)) Coq_cba.top)
        (let lemma = fold_left_meet_cons l y in
         Obj.magic trans_sym_co_inv_impl_type_morphism
           (equivalence_PER eq_B_relation)
           (Coq_cba.meet y (fold_left Coq_cba.meet l Coq_cba.top))
           (fold_left Coq_cba.meet (Cons (y, l)) Coq_cba.top)
           (Coq_cba.meet y (fold_left Coq_cba.meet l Coq_cba.top)) lemma
           (reflexivity (Obj.magic eq_B_relation).equivalence_Reflexive
             (Coq_cba.meet y (fold_left Coq_cba.meet l Coq_cba.top))))
        (x.meet_closed y (fold_left Coq_cba.meet l Coq_cba.top)
          (let rec f l0 h0 iHxs0 =
             match l0 with
             | Nil -> let Pair (_, b) = Obj.magic h0 in b
             | Cons (y0, l1) ->
               f l1
                 (fold_left_impl l1 (fun h1 ->
                   let Pair (a, _) = h1 in let Pair (_, b) = a in Pair (Tt, b))
                   h0)
                 (fun _ ->
                 let hr = fold_left_meet_cons l1 y0 in
                 x.upwards_closed
                   (Coq_cba.meet y0 (fold_left Coq_cba.meet l1 Coq_cba.top))
                   (fold_left Coq_cba.meet l1 Coq_cba.top)
                   (filter_memb_morph x
                     (fold_left Coq_cba.meet (Cons (y0, l1)) Coq_cba.top)
                     (Coq_cba.meet y0 (fold_left Coq_cba.meet l1 Coq_cba.top))
                     hr
                     (iHxs0 (fold_left_impl (Cons (y0, l1)) (fun _ -> Tt) h0)))
                   (let lemma =
                      Coq_cba.meet_assoc y0
                        (fold_left Coq_cba.meet l1 Coq_cba.top)
                        (fold_left Coq_cba.meet l1 Coq_cba.top)
                    in
                    Obj.magic trans_co_eq_inv_arrow_morphism
                      eq_B_relation.equivalence_Transitive
                      (Coq_cba.meet
                        (Coq_cba.meet y0
                          (fold_left Coq_cba.meet l1 Coq_cba.top))
                        (fold_left Coq_cba.meet l1 Coq_cba.top))
                      (Coq_cba.meet y0
                        (Coq_cba.meet (fold_left Coq_cba.meet l1 Coq_cba.top)
                          (fold_left Coq_cba.meet l1 Coq_cba.top)))
                      (symmetry eq_B_relation.equivalence_Symmetric
                        (Coq_cba.meet y0
                          (Coq_cba.meet
                            (fold_left Coq_cba.meet l1 Coq_cba.top)
                            (fold_left Coq_cba.meet l1 Coq_cba.top)))
                        (Coq_cba.meet
                          (Coq_cba.meet y0
                            (fold_left Coq_cba.meet l1 Coq_cba.top))
                          (fold_left Coq_cba.meet l1 Coq_cba.top))
                        lemma)
                      (Coq_cba.meet y0
                        (fold_left Coq_cba.meet l1 Coq_cba.top))
                      (Coq_cba.meet y0
                        (fold_left Coq_cba.meet l1 Coq_cba.top))
                      (let lemma0 =
                         Coq_cba.meet_idem
                           (fold_left Coq_cba.meet l1 Coq_cba.top)
                       in
                       trans_co_eq_inv_arrow_morphism
                         eq_B_relation.equivalence_Transitive
                         (Coq_cba.meet y0
                           (Coq_cba.meet
                             (fold_left Coq_cba.meet l1 Coq_cba.top)
                             (fold_left Coq_cba.meet l1 Coq_cba.top)))
                         (Coq_cba.meet y0
                           (fold_left Coq_cba.meet l1 Coq_cba.top))
                         (reflexive_partial_app_morphism Coq_cba.meet
                           meet_morphism y0
                           (reflexive_proper_proxy
                             eq_B_relation.equivalence_Reflexive y0)
                           (Coq_cba.meet
                             (fold_left Coq_cba.meet l1 Coq_cba.top)
                             (fold_left Coq_cba.meet l1 Coq_cba.top))
                           (fold_left Coq_cba.meet l1 Coq_cba.top) lemma0)
                         (Coq_cba.meet y0
                           (fold_left Coq_cba.meet l1 Coq_cba.top))
                         (Coq_cba.meet y0
                           (fold_left Coq_cba.meet l1 Coq_cba.top))
                         (reflexivity
                           (Obj.magic eq_B_relation).equivalence_Reflexive
                           (Coq_cba.meet y0
                             (fold_left Coq_cba.meet l1 Coq_cba.top))))))
           in f l x0 iHxs)
          (iHxs (fold_left_impl l (fun _ -> Tt) x0)))

  (** val lemma61 : Coq_cba.coq_B list -> __ -> (__, 'a3) prod **)

  let rec lemma61 l h =
    match l with
    | Nil -> Obj.magic h
    | Cons (_, l0) ->
      lemma61 l0
        (fold_left_impl l0 (fun h0 ->
          let Pair (a, b) = h0 in
          let Pair (a0, b0) = a in Pair ((Pair (a0, b)), b0)) h)

  (** val lemma62 : Coq_cba.coq_B list -> (__, 'a3) prod -> __ **)

  let rec lemma62 l h =
    match l with
    | Nil -> Obj.magic h
    | Cons (_, l0) ->
      fold_left_impl l0 (fun h0 ->
        let Pair (a, b) = h0 in
        let Pair (a0, b0) = a in Pair ((Pair (a0, b)), b0)) (lemma62 l0 h)

  (** val lemma5 :
      Coq_cba.coq_B list -> nat -> __ -> (__, (Coq_cba.coq_B, (Coq_cba.coq_B
      in0, (__, (__, ('a1, 'a1 union_singl up) equiconsistent) prod) prod)
      prod) sigT) sum **)

  let rec lemma5 ys n h =
    match ys with
    | Nil -> Inl h
    | Cons (y, l) ->
      let h' = lemma61 l h in
      let Pair (f, s) = h' in
      let h5 = lemma5 l n f in
      (match h5 with
       | Inl f0 ->
         (match s with
          | Inl x ->
            Inl
              (lemma62 l
                (match s with
                 | Inl a -> Pair (f0, a)
                 | Inr _ -> Pair (f0, x)))
          | Inr p ->
            Inr (ExistT (y, (Pair ((Obj.magic (Inl __)), (Pair (__, (Pair
              ((let s0 = Coq_cba.id_B_dec y y in
                match s0 with
                | Left ->
                  let rec f1 l0 h0 =
                    match l0 with
                    | Nil -> h0
                    | Cons (y0, l1) ->
                      let h'0 = lemma61 l1 h0 in
                      let Pair (f2, x) = h'0 in
                      let iH = f1 l1 f2 in
                      (match Coq_cba.id_B_dec y y0 with
                       | Left -> iH
                       | Right ->
                         lemma62 (remove Coq_cba.id_B_dec y l1) (Pair (iH, x)))
                  in f1 l f0
                | Right -> assert false (* absurd case *)),
              (let Pair (_, b) = p in
               (match s with
                | Inl _ -> b
                | Inr b0 -> let Pair (_, b1) = b0 in b1)))))))))))
       | Inr s0 ->
         let ExistT (x, p) = s0 in
         let Pair (i, p0) = p in
         let Pair (_, p1) = p0 in
         let Pair (f0, e) = p1 in
         (match s with
          | Inl x0 ->
            Inr (ExistT (x, (Pair ((Obj.magic (Inr i)), (Pair (__, (Pair
              ((let hdec = Coq_cba.id_B_dec x y in
                match hdec with
                | Left ->
                  let s1 = Coq_cba.id_B_dec x x in
                  (match s1 with
                   | Left -> f0
                   | Right -> assert false (* absurd case *))
                | Right ->
                  let s1 = Coq_cba.id_B_dec x y in
                  (match s1 with
                   | Left -> f0
                   | Right ->
                     lemma62 (remove Coq_cba.id_B_dec x l)
                       (match s with
                        | Inl a ->
                          (match hdec with
                           | Left ->
                             Pair ((assert false (* absurd case *)),
                               (assert false (* absurd case *)))
                           | Right -> Pair (f0, a))
                        | Inr _ ->
                          (match hdec with
                           | Left ->
                             Pair ((assert false (* absurd case *)),
                               (assert false (* absurd case *)))
                           | Right -> Pair (f0, x0))))),
              e))))))))
          | Inr _ ->
            Inr (ExistT (y, (Pair ((Obj.magic (Inl __)), (Pair (__,
              (let s1 = Coq_cba.id_B_dec y y in
               match s1 with
               | Left -> Pair (f0, e)
               | Right -> assert false (* absurd case *))))))))))

  type 'f coq_F_ = __

  type 'f coq_Z = (nat, 'f coq_F_) sigT

  (** val lem223 : Coq_cba.coq_B -> 'a2 -> 'a2 up **)

  let lem223 x x0 =
    ExistT ((S O), (ExistT ((Cons (x, Nil)), (Pair (__, (Pair
      ((Obj.magic (Pair (Tt, x0))),
      (let lemma = Coq_cba.meet_top x in
       subrelation_proper (Obj.magic __)
         (pER_type_morphism (equivalence_PER eq_B_relation)) Tt
         (subrelation_respectful subrelation_refl
           (subrelation_respectful subrelation_refl
             (Obj.magic (fun _ _ -> iffT_flip_arrow_subrelation))))
         (Coq_cba.meet (Coq_cba.meet Coq_cba.top x) x) (Coq_cba.meet x x)
         (meet_morphism (Coq_cba.meet Coq_cba.top x) x lemma x x
           (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive x))
         (Coq_cba.meet Coq_cba.top x) x lemma
         (let lemma0 = Coq_cba.meet_idem x in
          trans_co_eq_inv_arrow_morphism eq_B_relation.equivalence_Transitive
            (Coq_cba.meet x x) x lemma0 x x
            (reflexivity (Obj.magic eq_B_relation).equivalence_Reflexive x))))))))))

  type le =
  | Coq_le_n
  | Coq_le_S of nat * le

  (** val le_rect :
      nat -> 'a1 -> (nat -> le -> 'a1 -> 'a1) -> nat -> le -> 'a1 **)

  let rec le_rect n0 f f0 _ = function
  | Coq_le_n -> f
  | Coq_le_S (m, l0) -> f0 m l0 (le_rect n0 f f0 m l0)

  (** val le_rec :
      nat -> 'a1 -> (nat -> le -> 'a1 -> 'a1) -> nat -> le -> 'a1 **)

  let rec le_rec n0 f f0 _ = function
  | Coq_le_n -> f
  | Coq_le_S (m, l0) -> f0 m l0 (le_rec n0 f f0 m l0)

  type lt = le

  (** val le_lt_dec : nat -> nat -> (le, lt) sum **)

  let rec le_lt_dec n m =
    match n with
    | O ->
      Inl
        (let rec f = function
         | O -> Coq_le_n
         | S n1 -> Coq_le_S (n1, (f n1))
         in f m)
    | S n0 ->
      (match m with
       | O ->
         Inr
           (let rec f = function
            | O -> Coq_le_n
            | S n2 -> Coq_le_S ((S n2), (f n2))
            in f n0)
       | S n1 ->
         let s = le_lt_dec n0 n1 in
         (match s with
          | Inl l ->
            Inl
              (let rec f _ = function
               | Coq_le_n -> Coq_le_n
               | Coq_le_S (m0, l1) -> Coq_le_S ((S m0), (f m0 l1))
               in f n1 l)
          | Inr l ->
            Inr
              (let rec f _ = function
               | Coq_le_n -> Coq_le_n
               | Coq_le_S (m0, l1) -> Coq_le_S ((S m0), (f m0 l1))
               in f n0 l)))

  (** val lt_le_incl : nat -> nat -> lt -> le **)

  let rec lt_le_incl n _ = function
  | Coq_le_n -> Coq_le_S (n, Coq_le_n)
  | Coq_le_S (m, l) -> Coq_le_S (m, (lt_le_incl n m l))

  (** val lem222 :
      nat -> nat -> le -> Coq_cba.coq_B -> 'a1 coq_F_ -> 'a1 coq_F_ **)

  let lem222 _ =
    let lem2221 = fun _ x x0 -> lem223 x (Inl x0) in
    (fun m x x0 x1 ->
    let rec f _ = function
    | Coq_le_n -> x1
    | Coq_le_S (m0, l0) -> Obj.magic lem2221 m0 x0 (f m0 l0)
    in f m x)

  (** val thm22 :
      'a1 coq_Filter -> ('a1 coq_Z coq_Filter, (('a1, 'a1 coq_Z)
      equiconsistent, 'a1 coq_Z complete) prod) prod **)

  let thm22 x =
    let lem221 = fun n -> match n with
                          | O -> x
                          | S _ -> Obj.magic up_filter in
    let fn_filter = fun n -> match n with
                             | O -> x
                             | S _ -> Obj.magic up_filter
    in
    Pair ({ nonempty =
    (let h1 = x.nonempty in
     let ExistT (x0, f) = h1 in ExistT (x0, (ExistT (O, (Obj.magic f)))));
    upwards_closed = (fun x0 y x1 x2 ->
    let ExistT (x3, f) = x1 in
    ExistT (x3, ((Obj.magic lem221 x3).upwards_closed x0 y f x2)));
    meet_closed = (fun x0 y x1 x2 ->
    let ExistT (x3, f) = x1 in
    let ExistT (x4, f0) = x2 in
    (match le_lt_dec x3 x4 with
     | Inl l ->
       ExistT (x4,
         ((Obj.magic lem221 x4).meet_closed x0 y (lem222 x3 x4 l x0 f) f0))
     | Inr l ->
       let l' = lt_le_incl x4 x3 l in
       ExistT (x3,
       ((Obj.magic lem221 x3).meet_closed x0 y f (lem222 x4 x3 l' y f0))))) },
    (let lem224 = fun n ->
       let rec f = function
       | O -> Pair ((fun h0 -> h0), (fun h0 -> h0))
       | S n1 ->
         let iHn = f n1 in
         Pair ((fun h0 ->
         let ExistT (_, s) = h0 in
         let ExistT (x0, p) = s in
         let Pair (_, p0) = p in
         let Pair (f0, l) = p0 in
         let Pair (i, _) = iHn in
         Obj.magic i
           (let caseAnalysis = lemma5 x0 n1 f0 in
            match caseAnalysis with
            | Inl f1 ->
              (lem221 n1).upwards_closed
                (fold_left Coq_cba.meet x0 Coq_cba.top) Coq_cba.bott
                (lemma4 x0 (fn_filter n1) f1) l
            | Inr s0 ->
              let ExistT (x1, p1) = s0 in
              let Pair (_, p2) = p1 in
              let Pair (_, p3) = p2 in
              let Pair (f1, e) = p3 in
              let y = remove Coq_cba.id_B_dec x1 x0 in
              let a0 =
                leq_trans (fold_left Coq_cba.meet (Cons (x1, y)) Coq_cba.top)
                  (fold_left Coq_cba.meet x0 Coq_cba.top) Coq_cba.bott
                  (lemma2 x0 (Cons (x1, y)) (lemma3 Coq_cba.id_B_dec x1 x0)) l
              in
              let a1 =
                let lemma = fold_left_meet_cons y x1 in
                subrelation_proper (Obj.magic __)
                  (pER_type_morphism (equivalence_PER eq_B_relation)) Tt
                  (subrelation_respectful subrelation_refl
                    (subrelation_respectful subrelation_refl
                      (Obj.magic (fun _ _ -> iffT_arrow_subrelation))))
                  (Coq_cba.meet
                    (fold_left Coq_cba.meet (Cons (x1, y)) Coq_cba.top)
                    Coq_cba.bott)
                  (Coq_cba.meet
                    (Coq_cba.meet x1 (fold_left Coq_cba.meet y Coq_cba.top))
                    Coq_cba.bott)
                  (meet_morphism
                    (fold_left Coq_cba.meet (Cons (x1, y)) Coq_cba.top)
                    (Coq_cba.meet x1 (fold_left Coq_cba.meet y Coq_cba.top))
                    lemma Coq_cba.bott Coq_cba.bott
                    (reflexive_proper_proxy
                      eq_B_relation.equivalence_Reflexive Coq_cba.bott))
                  (fold_left Coq_cba.meet (Cons (x1, y)) Coq_cba.top)
                  (Coq_cba.meet x1 (fold_left Coq_cba.meet y Coq_cba.top))
                  lemma a0
              in
              let a2 =
                let y0 = fold_left Coq_cba.meet y Coq_cba.top in
                let a2 =
                  let lemma =
                    Coq_cba.meet_comm (Coq_cba.meet x1 y0) Coq_cba.bott
                  in
                  subrelation_proper (Obj.magic __)
                    (pER_type_morphism (equivalence_PER eq_B_relation)) Tt
                    (subrelation_respectful subrelation_refl
                      (subrelation_respectful subrelation_refl (fun _ _ ->
                        iffT_arrow_subrelation)))
                    (Coq_cba.meet (Coq_cba.meet x1 y0) Coq_cba.bott)
                    (Coq_cba.meet Coq_cba.bott (Coq_cba.meet x1 y0)) lemma
                    (Coq_cba.meet x1 y0) (Coq_cba.meet x1 y0)
                    (reflexive_proper_proxy
                      eq_B_relation.equivalence_Reflexive
                      (Coq_cba.meet x1 y0))
                    a1
                in
                let a3 =
                  let lemma = Coq_cba.meet_bott (Coq_cba.meet x1 y0) in
                  subrelation_proper (Obj.magic __)
                    (pER_type_morphism (equivalence_PER eq_B_relation)) Tt
                    (subrelation_respectful subrelation_refl
                      (subrelation_respectful subrelation_refl (fun _ _ ->
                        iffT_arrow_subrelation)))
                    (Coq_cba.meet Coq_cba.bott (Coq_cba.meet x1 y0))
                    Coq_cba.bott lemma (Coq_cba.meet x1 y0)
                    (Coq_cba.meet x1 y0)
                    (reflexive_proper_proxy
                      eq_B_relation.equivalence_Reflexive
                      (Coq_cba.meet x1 y0))
                    a2
                in
                let a0' =
                  trans_co_eq_inv_arrow_morphism
                    eq_B_relation.equivalence_Transitive
                    (Coq_cba.join Coq_cba.bott (Coq_cba.compl x1))
                    (Coq_cba.join (Coq_cba.meet x1 y0) (Coq_cba.compl x1))
                    (join_morphism Coq_cba.bott (Coq_cba.meet x1 y0)
                      (Obj.magic a3) (Coq_cba.compl x1) (Coq_cba.compl x1)
                      (reflexive_proper_proxy
                        eq_B_relation.equivalence_Reflexive
                        (Coq_cba.compl x1)))
                    (Coq_cba.join (Coq_cba.meet x1 y0) (Coq_cba.compl x1))
                    (Coq_cba.join (Coq_cba.meet x1 y0) (Coq_cba.compl x1))
                    (reflexivity
                      (Obj.magic eq_B_relation).equivalence_Reflexive
                      (Coq_cba.join (Coq_cba.meet x1 y0) (Coq_cba.compl x1)))
                in
                let a0'0 =
                  let lemma = Coq_cba.join_bott (Coq_cba.compl x1) in
                  subrelation_proper (Obj.magic __)
                    (pER_type_morphism (equivalence_PER eq_B_relation)) Tt
                    (subrelation_respectful subrelation_refl
                      (subrelation_respectful subrelation_refl (fun _ _ ->
                        iffT_arrow_subrelation)))
                    (Coq_cba.join Coq_cba.bott (Coq_cba.compl x1))
                    (Coq_cba.compl x1) lemma
                    (Coq_cba.join (Coq_cba.meet x1 y0) (Coq_cba.compl x1))
                    (Coq_cba.join (Coq_cba.meet x1 y0) (Coq_cba.compl x1))
                    (reflexive_proper_proxy
                      eq_B_relation.equivalence_Reflexive
                      (Coq_cba.join (Coq_cba.meet x1 y0) (Coq_cba.compl x1)))
                    a0'
                in
                let a0'1 =
                  let lemma = Coq_cba.join_distrib x1 y0 (Coq_cba.compl x1) in
                  trans_co_impl_type_morphism
                    eq_B_relation.equivalence_Transitive (Coq_cba.compl x1)
                    (Coq_cba.join (Coq_cba.meet x1 y0) (Coq_cba.compl x1))
                    (Coq_cba.meet (Coq_cba.join x1 (Coq_cba.compl x1))
                      (Coq_cba.join y0 (Coq_cba.compl x1)))
                    lemma a0'0
                in
                let a0'2 =
                  let lemma = Coq_cba.join_compl x1 in
                  trans_co_impl_type_morphism
                    eq_B_relation.equivalence_Transitive (Coq_cba.compl x1)
                    (Coq_cba.meet (Coq_cba.join x1 (Coq_cba.compl x1))
                      (Coq_cba.join y0 (Coq_cba.compl x1)))
                    (Coq_cba.meet Coq_cba.top
                      (Coq_cba.join y0 (Coq_cba.compl x1)))
                    (meet_morphism (Coq_cba.join x1 (Coq_cba.compl x1))
                      Coq_cba.top lemma (Coq_cba.join y0 (Coq_cba.compl x1))
                      (Coq_cba.join y0 (Coq_cba.compl x1))
                      (reflexive_proper_proxy
                        eq_B_relation.equivalence_Reflexive
                        (Coq_cba.join y0 (Coq_cba.compl x1))))
                    a0'1
                in
                let a0'3 =
                  let lemma =
                    Coq_cba.meet_top (Coq_cba.join y0 (Coq_cba.compl x1))
                  in
                  trans_co_impl_type_morphism
                    eq_B_relation.equivalence_Transitive (Coq_cba.compl x1)
                    (Coq_cba.meet Coq_cba.top
                      (Coq_cba.join y0 (Coq_cba.compl x1)))
                    (Coq_cba.join y0 (Coq_cba.compl x1)) lemma a0'2
                in
                let a0'4 =
                  symmetry (Obj.magic eq_B_relation).equivalence_Symmetric
                    (Coq_cba.compl x1) (Coq_cba.join y0 (Coq_cba.compl x1))
                    a0'3
                in
                let h = leq' y0 (Coq_cba.compl x1) in
                let h1 = let Pair (_, x2) = h in x2 in Obj.magic h1 a0'4
              in
              let a3 = lemma4 y (lem221 n1) f1 in
              let a4 =
                (lem221 n1).upwards_closed
                  (fold_left Coq_cba.meet y Coq_cba.top) (Coq_cba.compl x1)
                  a3 a2
              in
              let Pair (_, i0) = e in
              i0
                (let a5 = lem223 (Coq_cba.compl x1) (Inleft a4) in
                 let a6 = lem223 x1 Inright in
                 filter_memb_morph up_filter
                   (Coq_cba.meet x1 (Coq_cba.compl x1)) Coq_cba.bott
                   (Coq_cba.meet_compl x1)
                   (up_filter.meet_closed x1 (Coq_cba.compl x1) a6 a5)))),
         (fun fincon ->
         let Pair (_, i) = iHn in lem223 Coq_cba.bott (Inl (i fincon))))
       in f n
     in
     let lem226 = Pair ((fun fincon -> ExistT (O, fincon)), (fun zincon ->
       let ExistT (x0, f) = zincon in
       let h = lem224 x0 in let Pair (a, _) = h in a f))
     in
     Pair ((Obj.magic lem226),
     (let subseteq_up_mono = fun _ x0 x1 ->
        let ExistT (x2, s) = x1 in
        let ExistT (x3, p) = s in
        let Pair (_, p0) = p in
        let Pair (f, l) = p0 in
        ExistT (x2, (ExistT (x3, (Pair (__, (Pair
        ((let rec f0 l0 h2 =
            match l0 with
            | Nil -> h2
            | Cons (y, l1) ->
              let h2' = lemma61 l1 h2 in
              lemma62 l1 (Pair ((f0 l1 (let Pair (a, _) = h2' in a)),
                (x0 y (let Pair (_, b) = h2' in b))))
          in f0 x3 f),
        l)))))))
      in
      fun x0 x1 ->
      let n = Coq_cba.enum x0 in
      let claim = Pair ((fun h1 -> lem223 Coq_cba.bott (Inleft h1)),
        (fun h1 ->
        let h2 =
          subseteq_up_mono Coq_cba.bott (fun _ x2 ->
            match x2 with
            | Inleft a -> Inleft (ExistT (n, a))
            | Inright -> Inright) h1
        in
        let h3 =
          let Pair (_, b) = x1 in
          let ExistT (x2, p) = h2 in
          let ExistT (x3, p0) = p in
          let Pair (_, b0) = p0 in
          let Pair (a, b1) = b0 in
          let h = fun x4 x5 -> b (ExistT (x4, x5)) in
          let h3 = h x2 in
          let h4 = fun x4 x5 -> h3 (ExistT (x4, x5)) in
          let h5 = h4 x3 in let x4 = Pair (a, b1) in h5 (Pair (__, x4))
        in
        let h4 = fun n0 ->
          let Pair (a, _) = lem226 in
          Pair ((fun h0 -> ExistT (n0, h0)), (fun h0 ->
          let ExistT (x2, p) = h0 in
          let h4 = lem224 x2 in
          let Pair (a0, _) = h4 in
          let h5 = a0 p in
          let h6 = a h5 in
          let ExistT (x3, _) = h6 in
          let h7 = lem224 x3 in
          let Pair (a1, b) = h7 in
          let h8 = b h5 in
          let h9 = a1 h8 in
          let h10 = lem224 n0 in let Pair (_, b0) = h10 in b0 h9))
        in
        let ExistT (x2, p) = h3 in
        let h = h4 (Coq_cba.enum x0) in
        let Pair (_, b) = h in
        let h0 = fun x3 x4 -> b (ExistT (x3, x4)) in
        let h5 = h0 x2 in Obj.magic h5 p))
      in
      ExistT ((S n), (Obj.magic lem223 x0 (Inr (Pair (__, claim)))))))))

  (** val lemma8 :
      Coq_cba.coq_B -> Coq_cba.coq_B list -> __ -> (__, __) sum **)

  let rec lemma8 f ys h =
    match ys with
    | Nil -> Inl (Obj.magic Tt)
    | Cons (b, l) ->
      let h0 = lemma61 l h in
      let Pair (f0, u) = h0 in
      let s = lemma8 f l f0 in
      (match s with
       | Inl f1 ->
         (match u with
          | Inleft x -> Inl (lemma62 l (Pair (f1, x)))
          | Inright ->
            Inr
              (let s0 = Coq_cba.id_B_dec f b in
               match s0 with
               | Left ->
                 let rec f2 l0 f3 =
                   match l0 with
                   | Nil -> f3
                   | Cons (y, l1) ->
                     let f4 = lemma61 l1 f3 in
                     let s1 = Coq_cba.id_B_dec f y in
                     (match s1 with
                      | Left -> let Pair (a, _) = f4 in f2 l1 a
                      | Right ->
                        lemma62 (remove Coq_cba.id_B_dec f l1)
                          (let Pair (a, b0) = f4 in
                           let h1 = f2 l1 a in Pair (h1, b0)))
                 in f2 l f1
               | Right -> assert false (* absurd case *)))
       | Inr f1 ->
         Inr
           (let s0 = Coq_cba.id_B_dec f b in
            match s0 with
            | Left -> f1
            | Right ->
              lemma62 (remove Coq_cba.id_B_dec f l) (Pair (f1,
                (match u with
                 | Inleft x -> x
                 | Inright -> assert false (* absurd case *))))))

  (** val leq_bott : Coq_cba.coq_B -> leq **)

  let leq_bott x =
    let lemma = Coq_cba.meet_bott x in
    Obj.magic trans_co_eq_inv_arrow_morphism
      eq_B_relation.equivalence_Transitive (Coq_cba.meet Coq_cba.bott x)
      Coq_cba.bott lemma Coq_cba.bott Coq_cba.bott
      (reflexivity (Obj.magic eq_B_relation).equivalence_Reflexive
        Coq_cba.bott)
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

module Coq_classical_completeness =
 functor (Coq_ccsig:Coq_classical_completeness_signature) ->
 struct
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

  (** val formula_rect :
      'a1 -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
      'a1) -> (Coq_ccsig.predicate -> term -> 'a1) -> formula -> 'a1 **)

  let rec formula_rect f f0 f1 f2 = function
  | Coq_bot -> f
  | Coq_imp (f4, f5) ->
    f0 f4 (formula_rect f f0 f1 f2 f4) f5 (formula_rect f f0 f1 f2 f5)
  | Coq_all f4 -> f1 f4 (formula_rect f f0 f1 f2 f4)
  | Coq_atom (p, t) -> f2 p t

  (** val formula_rec :
      'a1 -> (formula -> 'a1 -> formula -> 'a1 -> 'a1) -> (formula -> 'a1 ->
      'a1) -> (Coq_ccsig.predicate -> term -> 'a1) -> formula -> 'a1 **)

  let rec formula_rec f f0 f1 f2 = function
  | Coq_bot -> f
  | Coq_imp (f4, f5) ->
    f0 f4 (formula_rec f f0 f1 f2 f4) f5 (formula_rec f f0 f1 f2 f5)
  | Coq_all f4 -> f1 f4 (formula_rec f f0 f1 f2 f4)
  | Coq_atom (p, t) -> f2 p t

  (** val term_rect :
      (nat -> 'a1) -> (nat -> 'a1) -> (constant -> 'a1) ->
      (Coq_ccsig.coq_function -> term -> 'a1 -> 'a1) -> term -> 'a1 **)

  let rec term_rect f f0 f1 f2 = function
  | Coq_bvar n -> f n
  | Coq_fvar n -> f0 n
  | Coq_cnst c -> f1 c
  | Coq_func (f3, t0) -> f2 f3 t0 (term_rect f f0 f1 f2 t0)

  (** val term_rec :
      (nat -> 'a1) -> (nat -> 'a1) -> (constant -> 'a1) ->
      (Coq_ccsig.coq_function -> term -> 'a1 -> 'a1) -> term -> 'a1 **)

  let rec term_rec f f0 f1 f2 = function
  | Coq_bvar n -> f n
  | Coq_fvar n -> f0 n
  | Coq_cnst c -> f1 c
  | Coq_func (f3, t0) -> f2 f3 t0 (term_rec f f0 f1 f2 t0)

  (** val constant_rect :
      (Coq_ccsig.constant0 -> 'a1) -> (formula -> 'a1) -> constant -> 'a1 **)

  let constant_rect f f0 = function
  | Coq_original c0 -> f c0
  | Coq_added f1 -> f0 f1

  (** val constant_rec :
      (Coq_ccsig.constant0 -> 'a1) -> (formula -> 'a1) -> constant -> 'a1 **)

  let constant_rec f f0 = function
  | Coq_original c0 -> f c0
  | Coq_added f1 -> f0 f1

  (** val open_rec_term : nat -> term -> term -> term **)

  let rec open_rec_term k u = function
  | Coq_bvar i -> (match Nat.eqb k i with
                   | True -> u
                   | False -> Coq_bvar i)
  | Coq_func (f, t1) -> Coq_func (f, (open_rec_term k u t1))
  | x -> x

  (** val open_rec : nat -> term -> formula -> formula **)

  let rec open_rec k u = function
  | Coq_bot -> Coq_bot
  | Coq_imp (t1, t2) -> Coq_imp ((open_rec k u t1), (open_rec k u t2))
  | Coq_all t1 -> Coq_all (open_rec (S k) u t1)
  | Coq_atom (p, t1) -> Coq_atom (p, (open_rec_term k u t1))

  (** val coq_open : formula -> term -> formula **)

  let coq_open t u =
    open_rec O u t

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

  (** val proof_rect :
      (formula list -> proof -> 'a1 -> formula -> 'a1) -> (formula list ->
      formula -> formula -> proof -> 'a1 -> proof -> 'a1 -> 'a1) -> (formula
      list -> formula -> formula -> proof -> 'a1 -> 'a1) -> (formula list ->
      formula -> proof -> 'a1 -> 'a1) -> (formula list -> formula -> formula
      in0 -> 'a1) -> (formula list -> formula -> proof -> 'a1 -> term -> 'a1)
      -> (formula list -> formula -> nat list -> __ -> (nat -> notin ->
      proof) -> (nat -> notin -> 'a1) -> 'a1) -> (formula list -> formula ->
      formula -> proof -> 'a1 -> 'a1) -> formula list -> formula -> proof ->
      'a1 **)

  let rec proof_rect f f0 f1 f2 f3 f4 f5 f6 _ _ = function
  | Coq_bot_elim (gamma, p0, a) ->
    f gamma p0 (proof_rect f f0 f1 f2 f3 f4 f5 f6 gamma Coq_bot p0) a
  | Coq_imp_elim (gamma, a, b, p0, p1) ->
    f0 gamma a b p0
      (proof_rect f f0 f1 f2 f3 f4 f5 f6 gamma (Coq_imp (a, b)) p0) p1
      (proof_rect f f0 f1 f2 f3 f4 f5 f6 gamma a p1)
  | Coq_imp_intro (gamma, a, b, p0) ->
    f1 gamma a b p0 (proof_rect f f0 f1 f2 f3 f4 f5 f6 (Cons (a, gamma)) b p0)
  | Coq_dneg (gamma, a, p0) ->
    f2 gamma a p0
      (proof_rect f f0 f1 f2 f3 f4 f5 f6 gamma (Coq_imp ((Coq_imp (a,
        Coq_bot)), Coq_bot)) p0)
  | Coq_hypo (gamma, a, i) -> f3 gamma a i
  | Coq_all_elim (gamma, a, p0, t) ->
    f4 gamma a p0 (proof_rect f f0 f1 f2 f3 f4 f5 f6 gamma (Coq_all a) p0) t
  | Coq_all_intro (gamma, a, l, p0) ->
    f5 gamma a l __ p0 (fun x n ->
      proof_rect f f0 f1 f2 f3 f4 f5 f6 gamma (coq_open a (Coq_fvar x))
        (p0 x n))
  | Coq_weaken (gamma, a, b, p0) ->
    f6 gamma a b p0 (proof_rect f f0 f1 f2 f3 f4 f5 f6 gamma a p0)

  (** val proof_rec :
      (formula list -> proof -> 'a1 -> formula -> 'a1) -> (formula list ->
      formula -> formula -> proof -> 'a1 -> proof -> 'a1 -> 'a1) -> (formula
      list -> formula -> formula -> proof -> 'a1 -> 'a1) -> (formula list ->
      formula -> proof -> 'a1 -> 'a1) -> (formula list -> formula -> formula
      in0 -> 'a1) -> (formula list -> formula -> proof -> 'a1 -> term -> 'a1)
      -> (formula list -> formula -> nat list -> __ -> (nat -> notin ->
      proof) -> (nat -> notin -> 'a1) -> 'a1) -> (formula list -> formula ->
      formula -> proof -> 'a1 -> 'a1) -> formula list -> formula -> proof ->
      'a1 **)

  let rec proof_rec f f0 f1 f2 f3 f4 f5 f6 _ _ = function
  | Coq_bot_elim (gamma, p0, a) ->
    f gamma p0 (proof_rec f f0 f1 f2 f3 f4 f5 f6 gamma Coq_bot p0) a
  | Coq_imp_elim (gamma, a, b, p0, p1) ->
    f0 gamma a b p0
      (proof_rec f f0 f1 f2 f3 f4 f5 f6 gamma (Coq_imp (a, b)) p0) p1
      (proof_rec f f0 f1 f2 f3 f4 f5 f6 gamma a p1)
  | Coq_imp_intro (gamma, a, b, p0) ->
    f1 gamma a b p0 (proof_rec f f0 f1 f2 f3 f4 f5 f6 (Cons (a, gamma)) b p0)
  | Coq_dneg (gamma, a, p0) ->
    f2 gamma a p0
      (proof_rec f f0 f1 f2 f3 f4 f5 f6 gamma (Coq_imp ((Coq_imp (a,
        Coq_bot)), Coq_bot)) p0)
  | Coq_hypo (gamma, a, i) -> f3 gamma a i
  | Coq_all_elim (gamma, a, p0, t) ->
    f4 gamma a p0 (proof_rec f f0 f1 f2 f3 f4 f5 f6 gamma (Coq_all a) p0) t
  | Coq_all_intro (gamma, a, l, p0) ->
    f5 gamma a l __ p0 (fun x n ->
      proof_rec f f0 f1 f2 f3 f4 f5 f6 gamma (coq_open a (Coq_fvar x))
        (p0 x n))
  | Coq_weaken (gamma, a, b, p0) ->
    f6 gamma a b p0 (proof_rec f f0 f1 f2 f3 f4 f5 f6 gamma a p0)

  type 'm model = { model_dneg : (formula -> 'm);
                    model_imp_faithful1 : (formula -> formula -> 'm -> 'm ->
                                          'm);
                    model_imp_faithful2 : (formula -> formula -> ('m -> 'm)
                                          -> 'm);
                    model_all_faithful1 : (formula -> 'm -> term -> 'm);
                    model_all_faithful2 : (formula -> __ -> __ -> (term -> __
                                          -> 'm) -> 'm) }

  (** val model_imp_faithful1 :
      'a1 model -> formula -> formula -> 'a1 -> 'a1 -> 'a1 **)

  let model_imp_faithful1 m =
    m.model_imp_faithful1

  type 'm interprets = (formula -> formula in0 -> 'm) -> 'm

  type valid = __ -> __ model -> __ interprets

  (** val peirce : formula list -> formula -> formula -> proof **)

  let peirce gamma p q =
    Coq_imp_intro (gamma, (Coq_imp ((Coq_imp (p, q)), p)), p, (Coq_dneg
      ((Cons ((Coq_imp ((Coq_imp (p, q)), p)), gamma)), p, (Coq_imp_intro
      ((Cons ((Coq_imp ((Coq_imp (p, q)), p)), gamma)), (Coq_imp (p,
      Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (p, Coq_bot)), (Cons
      ((Coq_imp ((Coq_imp (p, q)), p)), gamma)))), p, Coq_bot, (Coq_hypo
      ((Cons ((Coq_imp (p, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (p, q)), p)),
      gamma)))), (Coq_imp (p, Coq_bot)), (Obj.magic (Inl __)))),
      (Coq_imp_elim ((Cons ((Coq_imp (p, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
      (p, q)), p)), gamma)))), (Coq_imp (p, q)), p, (Coq_hypo ((Cons
      ((Coq_imp (p, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (p, q)), p)),
      gamma)))), (Coq_imp ((Coq_imp (p, q)), p)),
      (Obj.magic (Inr (Inl __))))), (Coq_imp_intro ((Cons ((Coq_imp (p,
      Coq_bot)), (Cons ((Coq_imp ((Coq_imp (p, q)), p)), gamma)))), p, q,
      (Coq_bot_elim ((Cons (p, (Cons ((Coq_imp (p, Coq_bot)), (Cons ((Coq_imp
      ((Coq_imp (p, q)), p)), gamma)))))), (Coq_imp_elim ((Cons (p, (Cons
      ((Coq_imp (p, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (p, q)), p)),
      gamma)))))), p, Coq_bot, (Coq_hypo ((Cons (p, (Cons ((Coq_imp (p,
      Coq_bot)), (Cons ((Coq_imp ((Coq_imp (p, q)), p)), gamma)))))),
      (Coq_imp (p, Coq_bot)), (Obj.magic (Inr (Inl __))))), (Coq_hypo ((Cons
      (p, (Cons ((Coq_imp (p, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (p, q)),
      p)), gamma)))))), p, (Obj.magic (Inl __)))))), q)))))))))))))

  (** val proof_imp_trans :
      formula list -> formula -> formula -> formula -> proof -> proof -> proof **)

  let proof_imp_trans gamma x y z hxy hyz =
    Coq_imp_intro (gamma, x, z, (Coq_imp_elim ((Cons (x, gamma)), y, z,
      (Coq_weaken (gamma, (Coq_imp (y, z)), x, hyz)), (Coq_imp_elim ((Cons
      (x, gamma)), x, y, (Coq_weaken (gamma, (Coq_imp (x, y)), x, hxy)),
      (Coq_hypo ((Cons (x, gamma)), x, (Obj.magic (Inl __)))))))))

  (** val proof_imp_contrapos :
      formula list -> formula -> formula -> proof -> proof **)

  let proof_imp_contrapos gamma x y x0 =
    Coq_imp_intro (gamma, (Coq_imp (y, Coq_bot)), (Coq_imp (x, Coq_bot)),
      (Coq_imp_intro ((Cons ((Coq_imp (y, Coq_bot)), gamma)), x, Coq_bot,
      (Coq_imp_elim ((Cons (x, (Cons ((Coq_imp (y, Coq_bot)), gamma)))), y,
      Coq_bot, (Coq_weaken ((Cons ((Coq_imp (y, Coq_bot)), gamma)), (Coq_imp
      (y, Coq_bot)), x, (Coq_hypo ((Cons ((Coq_imp (y, Coq_bot)), gamma)),
      (Coq_imp (y, Coq_bot)), (Obj.magic (Inl __)))))), (Coq_imp_elim ((Cons
      (x, (Cons ((Coq_imp (y, Coq_bot)), gamma)))), x, y, (Coq_weaken ((Cons
      ((Coq_imp (y, Coq_bot)), gamma)), (Coq_imp (x, y)), x, (Coq_weaken
      (gamma, (Coq_imp (x, y)), (Coq_imp (y, Coq_bot)), x0)))), (Coq_hypo
      ((Cons (x, (Cons ((Coq_imp (y, Coq_bot)), gamma)))), x,
      (Obj.magic (Inl __)))))))))))

  (** val formula_dec : formula -> formula -> sumbool **)

  let rec formula_dec x y =
    match x with
    | Coq_bot -> (match y with
                  | Coq_bot -> Left
                  | _ -> Right)
    | Coq_imp (f, f0) ->
      (match y with
       | Coq_imp (f1, f2) ->
         (match formula_dec f f1 with
          | Left -> formula_dec f0 f2
          | Right -> Right)
       | _ -> Right)
    | Coq_all f -> (match y with
                    | Coq_all f0 -> formula_dec f f0
                    | _ -> Right)
    | Coq_atom (p, t) ->
      (match y with
       | Coq_atom (p0, t0) ->
         (match Coq_ccsig.predicate_dec p p0 with
          | Left ->
            let rec f t1 x0 =
              match t1 with
              | Coq_bvar n ->
                (match x0 with
                 | Coq_bvar n0 ->
                   let rec f0 n1 x1 =
                     match n1 with
                     | O -> (match x1 with
                             | O -> Left
                             | S _ -> Right)
                     | S n2 -> (match x1 with
                                | O -> Right
                                | S n3 -> f0 n2 n3)
                   in f0 n n0
                 | _ -> Right)
              | Coq_fvar n ->
                (match x0 with
                 | Coq_fvar n0 ->
                   let rec f0 n1 x1 =
                     match n1 with
                     | O -> (match x1 with
                             | O -> Left
                             | S _ -> Right)
                     | S n2 -> (match x1 with
                                | O -> Right
                                | S n3 -> f0 n2 n3)
                   in f0 n n0
                 | _ -> Right)
              | Coq_cnst c ->
                (match x0 with
                 | Coq_cnst c0 ->
                   (match c with
                    | Coq_original c1 ->
                      (match c0 with
                       | Coq_original c2 -> Coq_ccsig.constant0_dec c1 c2
                       | Coq_added _ -> Right)
                    | Coq_added f0 ->
                      (match c0 with
                       | Coq_original _ -> Right
                       | Coq_added f1 -> formula_dec f0 f1))
                 | _ -> Right)
              | Coq_func (f0, t2) ->
                (match x0 with
                 | Coq_func (f1, t3) ->
                   (match Coq_ccsig.function_dec f0 f1 with
                    | Left -> f t2 t3
                    | Right -> Right)
                 | _ -> Right)
            in f t t0
          | Right -> Right)
       | _ -> Right)

  (** val constant_dec : constant -> constant -> sumbool **)

  let rec constant_dec f1 f2 =
    match f1 with
    | Coq_original c ->
      (match f2 with
       | Coq_original c0 -> Coq_ccsig.constant0_dec c c0
       | Coq_added _ -> Right)
    | Coq_added f ->
      (match f2 with
       | Coq_original _ -> Right
       | Coq_added f0 -> formula_dec f f0)

  module CBAproof =
   struct
    (** val compl : formula -> formula **)

    let compl x =
      Coq_imp (x, Coq_bot)

    (** val meet : formula -> formula -> formula **)

    let meet x y =
      Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)

    (** val join : formula -> formula -> formula **)

    let join x y =
      Coq_imp ((Coq_imp (x, Coq_bot)), y)

    (** val top : formula **)

    let top =
      Coq_imp (Coq_bot, Coq_bot)

    type eq_B = (proof, proof) prod

    (** val eq_B_refl : (formula, eq_B) reflexive **)

    let eq_B_refl x =
      let h = Coq_imp_intro (Nil, x, x, (Coq_hypo ((Cons (x, Nil)), x,
        (Obj.magic (Inl __)))))
      in
      Pair (h, h)

    (** val eq_B_symm : (formula, eq_B) symmetric **)

    let eq_B_symm _ _ = function
    | Pair (a, b) -> Pair (b, a)

    (** val eq_B_trans : (formula, eq_B) transitive **)

    let eq_B_trans x y z x0 x1 =
      let Pair (p, p0) = x0 in
      let Pair (p1, p2) = x1 in
      let pXZ = proof_imp_trans Nil x y z p p1 in
      let pZX = proof_imp_trans Nil z y x p2 p0 in Pair (pXZ, pZX)

    (** val eq_B_relation : (formula, eq_B) equivalence **)

    let eq_B_relation =
      { equivalence_Reflexive = eq_B_refl; equivalence_Symmetric = eq_B_symm;
        equivalence_Transitive = eq_B_trans }

    (** val join_morphism :
        (formula -> formula -> formula, (formula, formula -> formula, eq_B,
        (formula, formula, eq_B, eq_B) respectful) respectful) proper **)

    let join_morphism x y h x0 y0 h0 =
      let Pair (p, p0) = h in
      let Pair (p1, p2) = h0 in
      Pair
      ((proof_imp_trans Nil (Coq_imp ((Coq_imp (x, Coq_bot)), x0)) (Coq_imp
         ((Coq_imp (x, Coq_bot)), y0)) (Coq_imp ((Coq_imp (y, Coq_bot)), y0))
         (Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (x, Coq_bot)), x0)),
         (Coq_imp ((Coq_imp (x, Coq_bot)), y0)), (Coq_imp_intro ((Cons
         ((Coq_imp ((Coq_imp (x, Coq_bot)), x0)), Nil)), (Coq_imp (x,
         Coq_bot)), y0, (Coq_imp_elim ((Cons ((Coq_imp (x, Coq_bot)), (Cons
         ((Coq_imp ((Coq_imp (x, Coq_bot)), x0)), Nil)))), x0, y0,
         (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), x0)), Nil)),
         (Coq_imp (x0, y0)), (Coq_imp (x, Coq_bot)), (Coq_weaken (Nil,
         (Coq_imp (x0, y0)), (Coq_imp ((Coq_imp (x, Coq_bot)), x0)), p1)))),
         (Coq_imp_elim ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp
         ((Coq_imp (x, Coq_bot)), x0)), Nil)))), (Coq_imp (x, Coq_bot)), x0,
         (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), x0)), Nil)),
         (Coq_imp ((Coq_imp (x, Coq_bot)), x0)), (Coq_imp (x, Coq_bot)),
         (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), x0)), Nil)),
         (Coq_imp ((Coq_imp (x, Coq_bot)), x0)), (Obj.magic (Inl __)))))),
         (Coq_hypo ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
         (x, Coq_bot)), x0)), Nil)))), (Coq_imp (x, Coq_bot)),
         (Obj.magic (Inl __)))))))))))) (Coq_imp_intro (Nil, (Coq_imp
         ((Coq_imp (x, Coq_bot)), y0)), (Coq_imp ((Coq_imp (y, Coq_bot)),
         y0)), (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), y0)),
         Nil)), (Coq_imp (y, Coq_bot)), y0, (Coq_imp_elim ((Cons ((Coq_imp
         (y, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), y0)),
         Nil)))), (Coq_imp (x, Coq_bot)), y0, (Coq_weaken ((Cons ((Coq_imp
         ((Coq_imp (x, Coq_bot)), y0)), Nil)), (Coq_imp ((Coq_imp (x,
         Coq_bot)), y0)), (Coq_imp (y, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp
         ((Coq_imp (x, Coq_bot)), y0)), Nil)), (Coq_imp ((Coq_imp (x,
         Coq_bot)), y0)), (Obj.magic (Inl __)))))), (Coq_imp_elim ((Cons
         ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)),
         y0)), Nil)))), (Coq_imp (y, Coq_bot)), (Coq_imp (x, Coq_bot)),
         (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), y0)), Nil)),
         (Coq_imp ((Coq_imp (y, Coq_bot)), (Coq_imp (x, Coq_bot)))), (Coq_imp
         (y, Coq_bot)), (Coq_weaken (Nil, (Coq_imp ((Coq_imp (y, Coq_bot)),
         (Coq_imp (x, Coq_bot)))), (Coq_imp ((Coq_imp (x, Coq_bot)), y0)),
         (proof_imp_contrapos Nil x y p))))), (Coq_hypo ((Cons ((Coq_imp (y,
         Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), y0)), Nil)))),
         (Coq_imp (y, Coq_bot)), (Obj.magic (Inl __))))))))))))),
      (proof_imp_trans Nil (Coq_imp ((Coq_imp (y, Coq_bot)), y0)) (Coq_imp
        ((Coq_imp (y, Coq_bot)), x0)) (Coq_imp ((Coq_imp (x, Coq_bot)), x0))
        (Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (y, Coq_bot)), y0)), (Coq_imp
        ((Coq_imp (y, Coq_bot)), x0)), (Coq_imp_intro ((Cons ((Coq_imp
        ((Coq_imp (y, Coq_bot)), y0)), Nil)), (Coq_imp (y, Coq_bot)), x0,
        (Coq_imp_elim ((Cons ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp (y, Coq_bot)), y0)), Nil)))), y0, x0, (Coq_weaken ((Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), y0)), Nil)), (Coq_imp (y0, x0)),
        (Coq_imp (y, Coq_bot)), (Coq_weaken (Nil, (Coq_imp (y0, x0)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), y0)), p2)))), (Coq_imp_elim ((Cons
        ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)),
        y0)), Nil)))), (Coq_imp (y, Coq_bot)), y0, (Coq_weaken ((Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), y0)), Nil)), (Coq_imp ((Coq_imp
        (y, Coq_bot)), y0)), (Coq_imp (y, Coq_bot)), (Coq_hypo ((Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), y0)), Nil)), (Coq_imp ((Coq_imp
        (y, Coq_bot)), y0)), (Obj.magic (Inl __)))))), (Coq_hypo ((Cons
        ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)),
        y0)), Nil)))), (Coq_imp (y, Coq_bot)), (Obj.magic (Inl __))))))))))))
        (Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (y, Coq_bot)), x0)), (Coq_imp
        ((Coq_imp (x, Coq_bot)), x0)), (Coq_imp_intro ((Cons ((Coq_imp
        ((Coq_imp (y, Coq_bot)), x0)), Nil)), (Coq_imp (x, Coq_bot)), x0,
        (Coq_imp_elim ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp (y, Coq_bot)), x0)), Nil)))), (Coq_imp (y, Coq_bot)), x0,
        (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), x0)), Nil)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), x0)), (Coq_imp (x, Coq_bot)),
        (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), x0)), Nil)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), x0)), (Obj.magic (Inl __)))))),
        (Coq_imp_elim ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp (y, Coq_bot)), x0)), Nil)))), (Coq_imp (x, Coq_bot)),
        (Coq_imp (y, Coq_bot)), (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (y,
        Coq_bot)), x0)), Nil)), (Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp
        (y, Coq_bot)))), (Coq_imp (x, Coq_bot)), (Coq_weaken (Nil, (Coq_imp
        ((Coq_imp (x, Coq_bot)), (Coq_imp (y, Coq_bot)))), (Coq_imp ((Coq_imp
        (y, Coq_bot)), x0)), (proof_imp_contrapos Nil y x p0))))), (Coq_hypo
        ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y,
        Coq_bot)), x0)), Nil)))), (Coq_imp (x, Coq_bot)),
        (Obj.magic (Inl __))))))))))))))

    (** val meet_morphism :
        (formula -> formula -> formula, (formula, formula -> formula, eq_B,
        (formula, formula, eq_B, eq_B) respectful) respectful) proper **)

    let meet_morphism x y h x0 y0 h0 =
      let Pair (p, p0) = h in
      let Pair (p1, p2) = h0 in
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (x, (Coq_imp (x0,
      Coq_bot)))), Coq_bot)), (Coq_imp ((Coq_imp (y, (Coq_imp (y0,
      Coq_bot)))), Coq_bot)), (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp (x,
      (Coq_imp (x0, Coq_bot)))), Coq_bot)), Nil)), (Coq_imp (y, (Coq_imp (y0,
      Coq_bot)))), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (y, (Coq_imp (y0,
      Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))),
      Coq_bot)), Nil)))), (Coq_imp (x, (Coq_imp (x0, Coq_bot)))), Coq_bot,
      (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))),
      Coq_bot)), Nil)), (Coq_imp ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))),
      Coq_bot)), (Coq_imp (y, (Coq_imp (y0, Coq_bot)))), (Coq_hypo ((Cons
      ((Coq_imp ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))), Coq_bot)), Nil)),
      (Coq_imp ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))), Coq_bot)),
      (Obj.magic (Inl __)))))), (Coq_imp_intro ((Cons ((Coq_imp (y, (Coq_imp
      (y0, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x0,
      Coq_bot)))), Coq_bot)), Nil)))), x, (Coq_imp (x0, Coq_bot)),
      (Coq_imp_elim ((Cons (x, (Cons ((Coq_imp (y, (Coq_imp (y0, Coq_bot)))),
      (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))), Coq_bot)),
      Nil)))))), (Coq_imp (y0, Coq_bot)), (Coq_imp (x0, Coq_bot)),
      (proof_imp_contrapos (Cons (x, (Cons ((Coq_imp (y, (Coq_imp (y0,
        Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))),
        Coq_bot)), Nil)))))) x0 y0 (Coq_weaken ((Cons ((Coq_imp (y, (Coq_imp
        (y0, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x0,
        Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (x0, y0)), x, (Coq_weaken
        ((Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))), Coq_bot)),
        Nil)), (Coq_imp (x0, y0)), (Coq_imp (y, (Coq_imp (y0, Coq_bot)))),
        (Coq_weaken (Nil, (Coq_imp (x0, y0)), (Coq_imp ((Coq_imp (x, (Coq_imp
        (x0, Coq_bot)))), Coq_bot)), p1))))))),
      (Coq_imp_elim ((Cons (x, (Cons ((Coq_imp (y, (Coq_imp (y0, Coq_bot)))),
      (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))), Coq_bot)),
      Nil)))))), y, (Coq_imp (y0, Coq_bot)), (Coq_hypo ((Cons (x, (Cons
      ((Coq_imp (y, (Coq_imp (y0, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (x,
      (Coq_imp (x0, Coq_bot)))), Coq_bot)), Nil)))))), (Coq_imp (y, (Coq_imp
      (y0, Coq_bot)))), (Obj.magic (Inr (Inl __))))), (Coq_imp_elim ((Cons
      (x, (Cons ((Coq_imp (y, (Coq_imp (y0, Coq_bot)))), (Cons ((Coq_imp
      ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))), Coq_bot)), Nil)))))), x, y,
      (Coq_weaken ((Cons ((Coq_imp (y, (Coq_imp (y0, Coq_bot)))), (Cons
      ((Coq_imp ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))), Coq_bot)), Nil)))),
      (Coq_imp (x, y)), x, (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x,
      (Coq_imp (x0, Coq_bot)))), Coq_bot)), Nil)), (Coq_imp (x, y)), (Coq_imp
      (y, (Coq_imp (y0, Coq_bot)))), (Coq_weaken (Nil, (Coq_imp (x, y)),
      (Coq_imp ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))), Coq_bot)), p)))))),
      (Coq_hypo ((Cons (x, (Cons ((Coq_imp (y, (Coq_imp (y0, Coq_bot)))),
      (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))), Coq_bot)),
      Nil)))))), x, (Obj.magic (Inl __)))))))))))))))))),
      (proof_imp_contrapos Nil (Coq_imp (x, (Coq_imp (x0, Coq_bot))))
        (Coq_imp (y, (Coq_imp (y0, Coq_bot)))) (Coq_imp_intro (Nil, (Coq_imp
        (x, (Coq_imp (x0, Coq_bot)))), (Coq_imp (y, (Coq_imp (y0,
        Coq_bot)))),
        (proof_imp_trans (Cons ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))), Nil))
          y (Coq_imp (x0, Coq_bot)) (Coq_imp (y0, Coq_bot))
          (proof_imp_trans (Cons ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))),
            Nil)) y x (Coq_imp (x0, Coq_bot)) (Coq_weaken (Nil, (Coq_imp (y,
            x)), (Coq_imp (x, (Coq_imp (x0, Coq_bot)))), p0)) (Coq_hypo
            ((Cons ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))), Nil)), (Coq_imp
            (x, (Coq_imp (x0, Coq_bot)))), (Obj.magic (Inl __)))))
          (proof_imp_contrapos (Cons ((Coq_imp (x, (Coq_imp (x0, Coq_bot)))),
            Nil)) y0 x0 (Coq_weaken (Nil, (Coq_imp (y0, x0)), (Coq_imp (x,
            (Coq_imp (x0, Coq_bot)))), p2))))))))

    (** val id_B_dec : formula -> formula -> sumbool **)

    let id_B_dec =
      formula_dec

    (** val join_idem : formula -> eq_B **)

    let join_idem x =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (x, Coq_bot)), x)), x,
        (Coq_dneg ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), x)), Nil)), x,
        (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), x)), Nil)),
        (Coq_imp (x, Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), x)), Nil)))), x,
        Coq_bot, (Coq_hypo ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp (x, Coq_bot)), x)), Nil)))), (Coq_imp (x, Coq_bot)),
        (Obj.magic (Inl __)))), (Coq_imp_elim ((Cons ((Coq_imp (x, Coq_bot)),
        (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), x)), Nil)))), (Coq_imp (x,
        Coq_bot)), x, (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)),
        x)), Nil)), (Coq_imp ((Coq_imp (x, Coq_bot)), x)), (Coq_imp (x,
        Coq_bot)), (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), x)),
        Nil)), (Coq_imp ((Coq_imp (x, Coq_bot)), x)),
        (Obj.magic (Inl __)))))), (Coq_hypo ((Cons ((Coq_imp (x, Coq_bot)),
        (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), x)), Nil)))), (Coq_imp (x,
        Coq_bot)), (Obj.magic (Inl __)))))))))))))), (Coq_imp_intro (Nil, x,
        (Coq_imp ((Coq_imp (x, Coq_bot)), x)), (Coq_imp_intro ((Cons (x,
        Nil)), (Coq_imp (x, Coq_bot)), x, (Coq_weaken ((Cons (x, Nil)), x,
        (Coq_imp (x, Coq_bot)), (Coq_hypo ((Cons (x, Nil)), x,
        (Obj.magic (Inl __)))))))))))

    (** val meet_idem : formula -> eq_B **)

    let meet_idem x =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (x, (Coq_imp (x,
        Coq_bot)))), Coq_bot)), x, (Coq_dneg ((Cons ((Coq_imp ((Coq_imp (x,
        (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)), x, (Coq_imp_intro ((Cons
        ((Coq_imp ((Coq_imp (x, (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)),
        (Coq_imp (x, Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x, Coq_bot)))),
        Coq_bot)), Nil)))), (Coq_imp (x, (Coq_imp (x, Coq_bot)))), Coq_bot,
        (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x, Coq_bot)))),
        Coq_bot)), Nil)), (Coq_imp ((Coq_imp (x, (Coq_imp (x, Coq_bot)))),
        Coq_bot)), (Coq_imp (x, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp
        ((Coq_imp (x, (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)), (Coq_imp
        ((Coq_imp (x, (Coq_imp (x, Coq_bot)))), Coq_bot)),
        (Obj.magic (Inl __)))))), (Coq_imp_intro ((Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x, Coq_bot)))),
        Coq_bot)), Nil)))), x, (Coq_imp (x, Coq_bot)), (Coq_weaken ((Cons
        ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (x,
        Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (x, Coq_bot)), x, (Coq_hypo
        ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x,
        (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (x, Coq_bot)),
        (Obj.magic (Inl __)))))))))))))))), (Coq_imp_intro (Nil, x, (Coq_imp
        ((Coq_imp (x, (Coq_imp (x, Coq_bot)))), Coq_bot)), (Coq_imp_intro
        ((Cons (x, Nil)), (Coq_imp (x, (Coq_imp (x, Coq_bot)))), Coq_bot,
        (Coq_imp_elim ((Cons ((Coq_imp (x, (Coq_imp (x, Coq_bot)))), (Cons
        (x, Nil)))), x, Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (x, (Coq_imp
        (x, Coq_bot)))), (Cons (x, Nil)))), x, (Coq_imp (x, Coq_bot)),
        (Coq_hypo ((Cons ((Coq_imp (x, (Coq_imp (x, Coq_bot)))), (Cons (x,
        Nil)))), (Coq_imp (x, (Coq_imp (x, Coq_bot)))),
        (Obj.magic (Inl __)))), (Coq_weaken ((Cons (x, Nil)), x, (Coq_imp (x,
        (Coq_imp (x, Coq_bot)))), (Coq_hypo ((Cons (x, Nil)), x,
        (Obj.magic (Inl __)))))))), (Coq_weaken ((Cons (x, Nil)), x, (Coq_imp
        (x, (Coq_imp (x, Coq_bot)))), (Coq_hypo ((Cons (x, Nil)), x,
        (Obj.magic (Inl __)))))))))))))

    (** val join_comm : formula -> formula -> eq_B **)

    let join_comm x y =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), x)), (Coq_imp_intro ((Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Nil)), (Coq_imp (y,
        Coq_bot)), x, (Coq_dneg ((Cons ((Coq_imp (y, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Nil)))), x, (Coq_imp_intro
        ((Cons ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Nil)))), (Coq_imp (x, Coq_bot)), Coq_bot,
        (Coq_imp_elim ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp (y,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Nil)))))),
        y, Coq_bot, (Coq_weaken ((Cons ((Coq_imp (y, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Nil)))), (Coq_imp (y,
        Coq_bot)), (Coq_imp (x, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp (y,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Nil)))),
        (Coq_imp (y, Coq_bot)), (Obj.magic (Inl __)))))), (Coq_imp_elim
        ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp (y, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Nil)))))), (Coq_imp (x,
        Coq_bot)), y, (Coq_weaken ((Cons ((Coq_imp (y, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Nil)))), (Coq_imp ((Coq_imp
        (x, Coq_bot)), y)), (Coq_imp (x, Coq_bot)), (Coq_weaken ((Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Nil)), (Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), (Coq_imp (y, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Nil)), (Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), (Obj.magic (Inl __)))))))), (Coq_hypo ((Cons
        ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp (y, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Nil)))))), (Coq_imp (x,
        Coq_bot)), (Obj.magic (Inl __)))))))))))))))), (Coq_imp_intro (Nil,
        (Coq_imp ((Coq_imp (y, Coq_bot)), x)), (Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp (y,
        Coq_bot)), x)), Nil)), (Coq_imp (x, Coq_bot)), y, (Coq_dneg ((Cons
        ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)),
        x)), Nil)))), y, (Coq_imp_intro ((Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), x)), Nil)))), (Coq_imp (y,
        Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (y, Coq_bot)),
        (Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y,
        Coq_bot)), x)), Nil)))))), x, Coq_bot, (Coq_weaken ((Cons ((Coq_imp
        (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), x)), Nil)))),
        (Coq_imp (x, Coq_bot)), (Coq_imp (y, Coq_bot)), (Coq_hypo ((Cons
        ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)),
        x)), Nil)))), (Coq_imp (x, Coq_bot)), (Obj.magic (Inl __)))))),
        (Coq_imp_elim ((Cons ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), x)), Nil)))))),
        (Coq_imp (y, Coq_bot)), x, (Coq_weaken ((Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), x)), Nil)))),
        (Coq_imp ((Coq_imp (y, Coq_bot)), x)), (Coq_imp (y, Coq_bot)),
        (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), x)), Nil)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), x)), (Coq_imp (x, Coq_bot)),
        (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), x)), Nil)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), x)), (Obj.magic (Inl __)))))))),
        (Coq_hypo ((Cons ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), x)), Nil)))))),
        (Coq_imp (y, Coq_bot)), (Obj.magic (Inl __)))))))))))))))))

    (** val meet_comm : formula -> formula -> eq_B **)

    let meet_comm x y =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), (Coq_imp ((Coq_imp (y, (Coq_imp (x,
        Coq_bot)))), Coq_bot)), (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Nil)), (Coq_imp (y, (Coq_imp (x,
        Coq_bot)))), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (y, (Coq_imp (x,
        Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Nil)))), (Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot,
        (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Nil)), (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), (Coq_imp (y, (Coq_imp (x, Coq_bot)))), (Coq_hypo ((Cons
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Nil)),
        (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        (Obj.magic (Inl __)))))), (Coq_imp_intro ((Cons ((Coq_imp (y,
        (Coq_imp (x, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Nil)))), x, (Coq_imp (y, Coq_bot)),
        (Coq_imp_intro ((Cons (x, (Cons ((Coq_imp (y, (Coq_imp (x,
        Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Nil)))))), y, Coq_bot, (Coq_imp_elim ((Cons (y, (Cons (x,
        (Cons ((Coq_imp (y, (Coq_imp (x, Coq_bot)))), (Cons ((Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Nil)))))))), x,
        Coq_bot, (Coq_imp_elim ((Cons (y, (Cons (x, (Cons ((Coq_imp (y,
        (Coq_imp (x, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Nil)))))))), y, (Coq_imp (x, Coq_bot)),
        (Coq_weaken ((Cons (x, (Cons ((Coq_imp (y, (Coq_imp (x, Coq_bot)))),
        (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Nil)))))), (Coq_imp (y, (Coq_imp (x, Coq_bot)))), y, (Coq_weaken
        ((Cons ((Coq_imp (y, (Coq_imp (x, Coq_bot)))), (Cons ((Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp
        (y, (Coq_imp (x, Coq_bot)))), x, (Coq_hypo ((Cons ((Coq_imp (y,
        (Coq_imp (x, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (y, (Coq_imp (x,
        Coq_bot)))), (Obj.magic (Inl __)))))))), (Coq_hypo ((Cons (y, (Cons
        (x, (Cons ((Coq_imp (y, (Coq_imp (x, Coq_bot)))), (Cons ((Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Nil)))))))), y,
        (Obj.magic (Inl __)))))), (Coq_weaken ((Cons (x, (Cons ((Coq_imp (y,
        (Coq_imp (x, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Nil)))))), x, y, (Coq_hypo ((Cons (x, (Cons
        ((Coq_imp (y, (Coq_imp (x, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Nil)))))), x,
        (Obj.magic (Inl __)))))))))))))))))), (Coq_imp_intro (Nil, (Coq_imp
        ((Coq_imp (y, (Coq_imp (x, Coq_bot)))), Coq_bot)), (Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_imp_intro ((Cons
        ((Coq_imp ((Coq_imp (y, (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)),
        (Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot, (Coq_imp_elim ((Cons
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (y,
        (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (y, (Coq_imp
        (x, Coq_bot)))), Coq_bot, (Coq_hypo ((Cons ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (x, Coq_bot)))),
        Coq_bot)), Nil)))), (Coq_imp ((Coq_imp (y, (Coq_imp (x, Coq_bot)))),
        Coq_bot)), (Obj.magic (Inr (Inl __))))), (Coq_imp_intro ((Cons
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (y,
        (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)))), y, (Coq_imp (x,
        Coq_bot)), (Coq_imp_intro ((Cons (y, (Cons ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (x, Coq_bot)))),
        Coq_bot)), Nil)))))), x, Coq_bot, (Coq_imp_elim ((Cons (x, (Cons (y,
        (Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp
        ((Coq_imp (y, (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)))))))), y,
        Coq_bot, (Coq_imp_elim ((Cons (x, (Cons (y, (Cons ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (x,
        Coq_bot)))), Coq_bot)), Nil)))))))), x, (Coq_imp (y, Coq_bot)),
        (Coq_weaken ((Cons (y, (Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (x, Coq_bot)))), Coq_bot)),
        Nil)))))), (Coq_imp (x, (Coq_imp (y, Coq_bot)))), x, (Coq_weaken
        ((Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp
        ((Coq_imp (y, (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), y, (Coq_hypo ((Cons ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (x,
        Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), (Obj.magic (Inl __)))))))), (Coq_hypo ((Cons (x, (Cons
        (y, (Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp
        ((Coq_imp (y, (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)))))))), x,
        (Obj.magic (Inl __)))))), (Coq_weaken ((Cons (y, (Cons ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (x,
        Coq_bot)))), Coq_bot)), Nil)))))), y, x, (Coq_hypo ((Cons (y, (Cons
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp ((Coq_imp (y,
        (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)))))), y,
        (Obj.magic (Inl __)))))))))))))))))))

    (** val join_assoc : formula -> formula -> formula -> eq_B **)

    let join_assoc x y z =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp
        ((Coq_imp (y, Coq_bot)), z)))), (Coq_imp ((Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), z)), (Coq_imp_intro ((Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)),
        z)))), Nil)), (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        Coq_bot)), z, (Coq_imp_elim ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), z)))), Nil)))), (Coq_imp (y,
        Coq_bot)), z, (Coq_imp_elim ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), z)))), Nil)))), (Coq_imp (x,
        Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Coq_weaken ((Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)),
        z)))), Nil)), (Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp
        (y, Coq_bot)), z)))), (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)),
        y)), Coq_bot)), (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), z)))), Nil)), (Coq_imp ((Coq_imp
        (x, Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)), z)))),
        (Obj.magic (Inl __)))))), (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        (x, Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)), z)))), Nil)))), x,
        Coq_bot, (Coq_imp_elim ((Cons (x, (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (x, Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)), z)))), Nil)))))),
        (Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot, (Coq_weaken ((Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)),
        z)))), Nil)))), (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        Coq_bot)), x, (Coq_hypo ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), z)))), Nil)))), (Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), (Obj.magic (Inl __)))))),
        (Coq_imp_intro ((Cons (x, (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), z)))), Nil)))))), (Coq_imp (x,
        Coq_bot)), y, (Coq_bot_elim ((Cons ((Coq_imp (x, Coq_bot)), (Cons (x,
        (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)),
        (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (y,
        Coq_bot)), z)))), Nil)))))))), (Coq_imp_elim ((Cons ((Coq_imp (x,
        Coq_bot)), (Cons (x, (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), z)))), Nil)))))))), x, Coq_bot,
        (Coq_hypo ((Cons ((Coq_imp (x, Coq_bot)), (Cons (x, (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)), z)))),
        Nil)))))))), (Coq_imp (x, Coq_bot)), (Obj.magic (Inl __)))),
        (Coq_weaken ((Cons (x, (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), z)))), Nil)))))), x, (Coq_imp (x,
        Coq_bot)), (Coq_hypo ((Cons (x, (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (x, Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)), z)))), Nil)))))), x,
        (Obj.magic (Inl __)))))))), y)))))))))), (Coq_imp_intro ((Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)),
        z)))), Nil)))), y, Coq_bot, (Coq_imp_elim ((Cons (y, (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)), z)))),
        Nil)))))), (Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot,
        (Coq_weaken ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp
        ((Coq_imp (y, Coq_bot)), z)))), Nil)))), (Coq_imp ((Coq_imp ((Coq_imp
        (x, Coq_bot)), y)), Coq_bot)), y, (Coq_hypo ((Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)), z)))),
        Nil)))), (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)),
        (Obj.magic (Inl __)))))), (Coq_imp_intro ((Cons (y, (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)), z)))),
        Nil)))))), (Coq_imp (x, Coq_bot)), y, (Coq_weaken ((Cons (y, (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)),
        z)))), Nil)))))), y, (Coq_imp (x, Coq_bot)), (Coq_hypo ((Cons (y,
        (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)),
        (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (y,
        Coq_bot)), z)))), Nil)))))), y, (Obj.magic (Inl __)))))))))))))))))),
        (Coq_imp_intro (Nil, (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), z)), (Coq_imp ((Coq_imp (x, Coq_bot)),
        (Coq_imp ((Coq_imp (y, Coq_bot)), z)))), (Coq_imp_intro ((Cons
        ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        Coq_bot)), z)), Nil)), (Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), (Coq_imp_intro ((Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        Coq_bot)), z)), Nil)))), (Coq_imp (y, Coq_bot)), z, (Coq_imp_elim
        ((Cons ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        Coq_bot)), z)), Nil)))))), (Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), z, (Coq_weaken ((Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), z)), Nil)))), (Coq_imp ((Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), z)), (Coq_imp (y, Coq_bot)),
        (Coq_weaken ((Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), z)), Nil)), (Coq_imp ((Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), z)), (Coq_imp (x, Coq_bot)),
        (Coq_hypo ((Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), z)), Nil)), (Coq_imp ((Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), z)),
        (Obj.magic (Inl __)))))))), (Coq_imp_intro ((Cons ((Coq_imp (y,
        Coq_bot)), (Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), z)), Nil)))))),
        (Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot, (Coq_imp_elim ((Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), (Cons ((Coq_imp (y,
        Coq_bot)), (Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), z)), Nil)))))))),
        y, Coq_bot, (Coq_weaken ((Cons ((Coq_imp (y, Coq_bot)), (Cons
        ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), z)), Nil)))))), (Coq_imp (y,
        Coq_bot)), (Coq_imp ((Coq_imp (x, Coq_bot)), y)), (Coq_hypo ((Cons
        ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        Coq_bot)), z)), Nil)))))), (Coq_imp (y, Coq_bot)),
        (Obj.magic (Inl __)))))), (Coq_imp_elim ((Cons ((Coq_imp ((Coq_imp
        (x, Coq_bot)), y)), (Cons ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp
        (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), z)), Nil)))))))), (Coq_imp (x, Coq_bot)),
        y, (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), (Cons
        ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        Coq_bot)), z)), Nil)))))))), (Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        (Obj.magic (Inl __)))), (Coq_weaken ((Cons ((Coq_imp (y, Coq_bot)),
        (Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), z)), Nil)))))), (Coq_imp (x,
        Coq_bot)), (Coq_imp ((Coq_imp (x, Coq_bot)), y)), (Coq_weaken ((Cons
        ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)), z)), Nil)))), (Coq_imp (x,
        Coq_bot)), (Coq_imp (y, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), z)), Nil)))), (Coq_imp (x, Coq_bot)),
        (Obj.magic (Inl __)))))))))))))))))))))))

    (** val meet_assoc : formula -> formula -> formula -> eq_B **)

    let meet_assoc x y z =
      Pair
        ((proof_imp_contrapos Nil (Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp
           (y, Coq_bot)))), Coq_bot)), (Coq_imp (z, Coq_bot)))) (Coq_imp (x,
           (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))),
           Coq_bot)), Coq_bot)))) (Coq_imp_intro (Nil, (Coq_imp ((Coq_imp
           ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_imp (z,
           Coq_bot)))), (Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (y,
           (Coq_imp (z, Coq_bot)))), Coq_bot)), Coq_bot)))), (Coq_imp_intro
           ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
           Coq_bot)), (Coq_imp (z, Coq_bot)))), Nil)), x, (Coq_imp ((Coq_imp
           ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), Coq_bot)),
           (Coq_imp_intro ((Cons (x, (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
           (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_imp (z, Coq_bot)))),
           Nil)))), (Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))),
           Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp ((Coq_imp (y,
           (Coq_imp (z, Coq_bot)))), Coq_bot)), (Cons (x, (Cons ((Coq_imp
           ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
           (Coq_imp (z, Coq_bot)))), Nil)))))), (Coq_imp (y, (Coq_imp (z,
           Coq_bot)))), Coq_bot, (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (y,
           (Coq_imp (z, Coq_bot)))), Coq_bot)), (Cons (x, (Cons ((Coq_imp
           ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
           (Coq_imp (z, Coq_bot)))), Nil)))))), (Coq_imp ((Coq_imp (y,
           (Coq_imp (z, Coq_bot)))), Coq_bot)), (Obj.magic (Inl __)))),
           (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (z,
           Coq_bot)))), Coq_bot)), (Cons (x, (Cons ((Coq_imp ((Coq_imp
           ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_imp (z,
           Coq_bot)))), Nil)))))), y, (Coq_imp (z, Coq_bot)), (Coq_imp_elim
           ((Cons (y, (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))),
           Coq_bot)), (Cons (x, (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
           (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_imp (z, Coq_bot)))),
           Nil)))))))), (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
           Coq_bot)), (Coq_imp (z, Coq_bot)), (Coq_weaken ((Cons ((Coq_imp
           ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), (Cons (x, (Cons
           ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
           Coq_bot)), (Coq_imp (z, Coq_bot)))), Nil)))))), (Coq_imp ((Coq_imp
           ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_imp (z,
           Coq_bot)))), y, (Coq_weaken ((Cons (x, (Cons ((Coq_imp ((Coq_imp
           ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_imp (z,
           Coq_bot)))), Nil)))), (Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp
           (y, Coq_bot)))), Coq_bot)), (Coq_imp (z, Coq_bot)))), (Coq_imp
           ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), (Coq_weaken
           ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
           Coq_bot)), (Coq_imp (z, Coq_bot)))), Nil)), (Coq_imp ((Coq_imp
           ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_imp (z,
           Coq_bot)))), x, (Coq_hypo ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
           (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_imp (z, Coq_bot)))),
           Nil)), (Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
           Coq_bot)), (Coq_imp (z, Coq_bot)))), (Obj.magic (Inl __)))))))))),
           (Coq_imp_intro ((Cons (y, (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp
           (z, Coq_bot)))), Coq_bot)), (Cons (x, (Cons ((Coq_imp ((Coq_imp
           ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_imp (z,
           Coq_bot)))), Nil)))))))), (Coq_imp (x, (Coq_imp (y, Coq_bot)))),
           Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (x, (Coq_imp (y,
           Coq_bot)))), (Cons (y, (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (z,
           Coq_bot)))), Coq_bot)), (Cons (x, (Cons ((Coq_imp ((Coq_imp
           ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_imp (z,
           Coq_bot)))), Nil)))))))))), y, Coq_bot, (Coq_imp_elim ((Cons
           ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons (y, (Cons ((Coq_imp
           ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), (Cons (x, (Cons
           ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
           Coq_bot)), (Coq_imp (z, Coq_bot)))), Nil)))))))))), x, (Coq_imp
           (y, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp (x, (Coq_imp (y,
           Coq_bot)))), (Cons (y, (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (z,
           Coq_bot)))), Coq_bot)), (Cons (x, (Cons ((Coq_imp ((Coq_imp
           ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_imp (z,
           Coq_bot)))), Nil)))))))))), (Coq_imp (x, (Coq_imp (y, Coq_bot)))),
           (Obj.magic (Inl __)))), (Coq_weaken ((Cons (y, (Cons ((Coq_imp
           ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), (Cons (x, (Cons
           ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
           Coq_bot)), (Coq_imp (z, Coq_bot)))), Nil)))))))), x, (Coq_imp (x,
           (Coq_imp (y, Coq_bot)))), (Coq_weaken ((Cons ((Coq_imp ((Coq_imp
           (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), (Cons (x, (Cons ((Coq_imp
           ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
           (Coq_imp (z, Coq_bot)))), Nil)))))), x, y, (Coq_weaken ((Cons (x,
           (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
           Coq_bot)), (Coq_imp (z, Coq_bot)))), Nil)))), x, (Coq_imp
           ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), (Coq_hypo
           ((Cons (x, (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
           Coq_bot)))), Coq_bot)), (Coq_imp (z, Coq_bot)))), Nil)))), x,
           (Obj.magic (Inl __)))))))))))), (Coq_weaken ((Cons (y, (Cons
           ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), (Cons
           (x, (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
           Coq_bot)))), Coq_bot)), (Coq_imp (z, Coq_bot)))), Nil)))))))), y,
           (Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Coq_hypo ((Cons (y, (Cons
           ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), (Cons
           (x, (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
           Coq_bot)))), Coq_bot)), (Coq_imp (z, Coq_bot)))), Nil)))))))), y,
           (Obj.magic (Inl __))))))))))))))))))))))),
        (proof_imp_contrapos Nil (Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp
          (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), Coq_bot)))) (Coq_imp
          ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
          (Coq_imp (z, Coq_bot)))) (Coq_imp_intro (Nil, (Coq_imp (x, (Coq_imp
          ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)),
          Coq_bot)))), (Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
          Coq_bot)))), Coq_bot)), (Coq_imp (z, Coq_bot)))),
          (proof_imp_contrapos (Cons ((Coq_imp (x, (Coq_imp ((Coq_imp
            ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), Coq_bot)))),
            Nil)) z (Coq_imp (x, (Coq_imp (y, Coq_bot)))) (Coq_imp_intro
            ((Cons ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp
            (z, Coq_bot)))), Coq_bot)), Coq_bot)))), Nil)), z, (Coq_imp (x,
            (Coq_imp (y, Coq_bot)))), (Coq_imp_intro ((Cons (z, (Cons
            ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (z,
            Coq_bot)))), Coq_bot)), Coq_bot)))), Nil)))), x, (Coq_imp (y,
            Coq_bot)), (Coq_imp_intro ((Cons (x, (Cons (z, (Cons ((Coq_imp
            (x, (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))),
            Coq_bot)), Coq_bot)))), Nil)))))), y, Coq_bot, (Coq_imp_elim
            ((Cons (y, (Cons (x, (Cons (z, (Cons ((Coq_imp (x, (Coq_imp
            ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)),
            Coq_bot)))), Nil)))))))), (Coq_imp ((Coq_imp (y, (Coq_imp (z,
            Coq_bot)))), Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons (y, (Cons
            (x, (Cons (z, (Cons ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp
            (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), Coq_bot)))),
            Nil)))))))), x, (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (z,
            Coq_bot)))), Coq_bot)), Coq_bot)), (Coq_weaken ((Cons (x, (Cons
            (z, (Cons ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp
            (z, Coq_bot)))), Coq_bot)), Coq_bot)))), Nil)))))), (Coq_imp (x,
            (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))),
            Coq_bot)), Coq_bot)))), y, (Coq_weaken ((Cons (z, (Cons ((Coq_imp
            (x, (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))),
            Coq_bot)), Coq_bot)))), Nil)))), (Coq_imp (x, (Coq_imp ((Coq_imp
            ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), Coq_bot)))),
            x, (Coq_weaken ((Cons ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp
            (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), Coq_bot)))), Nil)),
            (Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (z,
            Coq_bot)))), Coq_bot)), Coq_bot)))), z, (Coq_hypo ((Cons
            ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (z,
            Coq_bot)))), Coq_bot)), Coq_bot)))), Nil)), (Coq_imp (x, (Coq_imp
            ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)),
            Coq_bot)))), (Obj.magic (Inl __)))))))))), (Coq_weaken ((Cons (x,
            (Cons (z, (Cons ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (y,
            (Coq_imp (z, Coq_bot)))), Coq_bot)), Coq_bot)))), Nil)))))), x,
            y, (Coq_hypo ((Cons (x, (Cons (z, (Cons ((Coq_imp (x, (Coq_imp
            ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)),
            Coq_bot)))), Nil)))))), x, (Obj.magic (Inl __)))))))),
            (Coq_imp_intro ((Cons (y, (Cons (x, (Cons (z, (Cons ((Coq_imp (x,
            (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))),
            Coq_bot)), Coq_bot)))), Nil)))))))), (Coq_imp (y, (Coq_imp (z,
            Coq_bot)))), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (y, (Coq_imp
            (z, Coq_bot)))), (Cons (y, (Cons (x, (Cons (z, (Cons ((Coq_imp
            (x, (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))),
            Coq_bot)), Coq_bot)))), Nil)))))))))), z, Coq_bot, (Coq_imp_elim
            ((Cons ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), (Cons (y, (Cons
            (x, (Cons (z, (Cons ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp
            (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), Coq_bot)))),
            Nil)))))))))), y, (Coq_imp (z, Coq_bot)), (Coq_hypo ((Cons
            ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), (Cons (y, (Cons (x, (Cons
            (z, (Cons ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp
            (z, Coq_bot)))), Coq_bot)), Coq_bot)))), Nil)))))))))), (Coq_imp
            (y, (Coq_imp (z, Coq_bot)))), (Obj.magic (Inl __)))), (Coq_weaken
            ((Cons (y, (Cons (x, (Cons (z, (Cons ((Coq_imp (x, (Coq_imp
            ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)),
            Coq_bot)))), Nil)))))))), y, (Coq_imp (y, (Coq_imp (z,
            Coq_bot)))), (Coq_hypo ((Cons (y, (Cons (x, (Cons (z, (Cons
            ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (z,
            Coq_bot)))), Coq_bot)), Coq_bot)))), Nil)))))))), y,
            (Obj.magic (Inl __)))))))), (Coq_weaken ((Cons (y, (Cons (x,
            (Cons (z, (Cons ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (y,
            (Coq_imp (z, Coq_bot)))), Coq_bot)), Coq_bot)))), Nil)))))))), z,
            (Coq_imp (y, (Coq_imp (z, Coq_bot)))), (Coq_weaken ((Cons (x,
            (Cons (z, (Cons ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (y,
            (Coq_imp (z, Coq_bot)))), Coq_bot)), Coq_bot)))), Nil)))))), z,
            y, (Coq_weaken ((Cons (z, (Cons ((Coq_imp (x, (Coq_imp ((Coq_imp
            ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)), Coq_bot)))),
            Nil)))), z, x, (Coq_hypo ((Cons (z, (Cons ((Coq_imp (x, (Coq_imp
            ((Coq_imp ((Coq_imp (y, (Coq_imp (z, Coq_bot)))), Coq_bot)),
            Coq_bot)))), Nil)))), z, (Obj.magic (Inl __)))))))))))))))))))))))))))

    (** val meet_absorb : formula -> formula -> eq_B **)

    let meet_absorb x y =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))), Coq_bot)), x, (Coq_dneg
        ((Cons ((Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)))), Coq_bot)), Nil)), x, (Coq_imp_intro
        ((Cons ((Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)))), Coq_bot)), Nil)), (Coq_imp (x,
        Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (x, Coq_bot)),
        (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (x,
        (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))),
        Coq_bot, (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x, (Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))), Coq_bot)),
        Nil)), (Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)))), Coq_bot)), (Coq_imp (x, Coq_bot)),
        (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp
        (x, Coq_bot)), y)), Coq_bot)))), Coq_bot)), Nil)), (Coq_imp ((Coq_imp
        (x, (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))),
        Coq_bot)), (Obj.magic (Inl __)))))), (Coq_imp_intro ((Cons ((Coq_imp
        (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))), Coq_bot)), Nil)))), x,
        (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)),
        (Coq_bot_elim ((Cons (x, (Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)),
        y)), Coq_bot)))), Coq_bot)), Nil)))))), (Coq_imp_elim ((Cons (x,
        (Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))), Coq_bot)),
        Nil)))))), x, Coq_bot, (Coq_weaken ((Cons ((Coq_imp (x, Coq_bot)),
        (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (x,
        Coq_bot)), x, (Coq_hypo ((Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)),
        y)), Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (x, Coq_bot)),
        (Obj.magic (Inl __)))))), (Coq_hypo ((Cons (x, (Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp
        (x, Coq_bot)), y)), Coq_bot)))), Coq_bot)), Nil)))))), x,
        (Obj.magic (Inl __)))))), (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)),
        y)), Coq_bot)))))))))))))), (Coq_imp_intro (Nil, x, (Coq_imp
        ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        Coq_bot)))), Coq_bot)), (Coq_imp_intro ((Cons (x, Nil)), (Coq_imp (x,
        (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))),
        Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (x, (Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))), (Cons (x, Nil)))),
        (Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot, (Coq_imp_elim ((Cons
        ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        Coq_bot)))), (Cons (x, Nil)))), x, (Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), y)), Coq_bot)), (Coq_hypo ((Cons ((Coq_imp (x, (Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))), (Cons (x,
        Nil)))), (Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)),
        y)), Coq_bot)))), (Obj.magic (Inl __)))), (Coq_weaken ((Cons (x,
        Nil)), x, (Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)),
        y)), Coq_bot)))), (Coq_hypo ((Cons (x, Nil)), x,
        (Obj.magic (Inl __)))))))), (Coq_imp_intro ((Cons ((Coq_imp (x,
        (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))), (Cons
        (x, Nil)))), (Coq_imp (x, Coq_bot)), y, (Coq_bot_elim ((Cons
        ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp (x, (Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))), (Cons (x, Nil)))))),
        (Coq_imp_elim ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp (x,
        (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))), (Cons
        (x, Nil)))))), x, Coq_bot, (Coq_hypo ((Cons ((Coq_imp (x, Coq_bot)),
        (Cons ((Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        Coq_bot)))), (Cons (x, Nil)))))), (Coq_imp (x, Coq_bot)),
        (Obj.magic (Inl __)))), (Coq_weaken ((Cons ((Coq_imp (x, (Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), y)), Coq_bot)))), (Cons (x,
        Nil)))), x, (Coq_imp (x, Coq_bot)), (Coq_weaken ((Cons (x, Nil)), x,
        (Coq_imp (x, (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), y)),
        Coq_bot)))), (Coq_hypo ((Cons (x, Nil)), x,
        (Obj.magic (Inl __)))))))))), y)))))))))))

    (** val join_absorb : formula -> formula -> eq_B **)

    let join_absorb x y =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)))), x, (Coq_dneg
        ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)))), Nil)), x, (Coq_imp_intro
        ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)))), Nil)), (Coq_imp (x, Coq_bot)),
        Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (x, (Coq_imp
        (y, Coq_bot)))), Coq_bot)))), Nil)))), (Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (x, Coq_bot)),
        (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)))), Nil)))), (Coq_imp (x,
        Coq_bot)), (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)),
        (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)))), Nil)),
        (Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)))), (Coq_imp (x, Coq_bot)), (Coq_hypo ((Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (x, (Coq_imp
        (y, Coq_bot)))), Coq_bot)))), Nil)), (Coq_imp ((Coq_imp (x,
        Coq_bot)), (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)))), (Obj.magic (Inl __)))))), (Coq_hypo ((Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)))), Nil)))),
        (Coq_imp (x, Coq_bot)), (Obj.magic (Inl __)))))), (Coq_imp_intro
        ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)))), Nil)))), x, (Coq_imp (y, Coq_bot)), (Coq_bot_elim ((Cons
        (x, (Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)))), Nil)))))), (Coq_imp_elim ((Cons (x, (Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)))), Nil)))))), x,
        Coq_bot, (Coq_weaken ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)))), Nil)))), (Coq_imp (x, Coq_bot)), x,
        (Coq_hypo ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        (x, Coq_bot)), (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)))), Nil)))), (Coq_imp (x, Coq_bot)),
        (Obj.magic (Inl __)))))), (Coq_hypo ((Cons (x, (Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)))), Nil)))))), x,
        (Obj.magic (Inl __)))))), (Coq_imp (y, Coq_bot)))))))))))))),
        (Coq_imp_intro (Nil, x, (Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)))), (Coq_imp_intro
        ((Cons (x, Nil)), (Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), (Coq_bot_elim ((Cons ((Coq_imp
        (x, Coq_bot)), (Cons (x, Nil)))), (Coq_imp_elim ((Cons ((Coq_imp (x,
        Coq_bot)), (Cons (x, Nil)))), x, Coq_bot, (Coq_hypo ((Cons ((Coq_imp
        (x, Coq_bot)), (Cons (x, Nil)))), (Coq_imp (x, Coq_bot)),
        (Obj.magic (Inl __)))), (Coq_weaken ((Cons (x, Nil)), x, (Coq_imp (x,
        Coq_bot)), (Coq_hypo ((Cons (x, Nil)), x, (Obj.magic (Inl __)))))))),
        (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)))))))))

    (** val join_distrib : formula -> formula -> formula -> eq_B **)

    let join_distrib x y z =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)), (Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), (Coq_imp_intro
        ((Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)), (Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), Coq_bot)))), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)),
        Nil)))), (Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot,
        (Coq_imp_elim ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)),
        z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))),
        (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)))), (Coq_imp ((Coq_imp
        (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)), (Coq_hypo ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)))),
        (Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Obj.magic (Inl __)))),
        (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)),
        z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))),
        (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)))), (Coq_imp (x,
        Coq_bot)), z, (Coq_imp_elim ((Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), z)), Nil)))))), (Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp
        (y, Coq_bot)))), Coq_bot)), Coq_bot)), z, (Coq_weaken ((Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), z)), Nil)))), (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)), (Coq_imp (x,
        Coq_bot)), (Coq_weaken ((Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)),
        (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), (Coq_hypo ((Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)),
        (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Coq_bot)), z)), (Obj.magic (Inl __)))))))), (Coq_imp_intro
        ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)))))),
        (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot,
        (Coq_imp_elim ((Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), (Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), z)), Nil)))))))), (Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot, (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), (Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), z)), Nil)))))))), (Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), (Obj.magic (Inl __)))), (Coq_imp_intro ((Cons
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Cons
        ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)))))))), x,
        (Coq_imp (y, Coq_bot)), (Coq_bot_elim ((Cons (x, (Cons ((Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Cons ((Coq_imp
        (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)),
        z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))),
        (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)))))))))), (Coq_imp_elim
        ((Cons (x, (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), (Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)),
        Nil)))))))))), x, Coq_bot, (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), (Cons ((Coq_imp (x, Coq_bot)),
        (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Coq_bot)), z)), Nil)))))))), (Coq_imp (x, Coq_bot)), x,
        (Coq_weaken ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)),
        Nil)))))), (Coq_imp (x, Coq_bot)), (Coq_imp ((Coq_imp (x, (Coq_imp
        (y, Coq_bot)))), Coq_bot)), (Coq_hypo ((Cons ((Coq_imp (x, Coq_bot)),
        (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Coq_bot)), z)), Nil)))))), (Coq_imp (x, Coq_bot)),
        (Obj.magic (Inl __)))))))), (Coq_hypo ((Cons (x, (Cons ((Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Cons ((Coq_imp
        (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)),
        z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))),
        (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)))))))))), x,
        (Obj.magic (Inl __)))))), (Coq_imp (y, Coq_bot)))))))))))))))),
        (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)),
        z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))),
        (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)))), (Coq_imp (y,
        Coq_bot)), z, (Coq_imp_elim ((Cons ((Coq_imp (y, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), z)), Nil)))))), (Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp
        (y, Coq_bot)))), Coq_bot)), Coq_bot)), z, (Coq_weaken ((Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), z)), Nil)))), (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)), (Coq_imp (y,
        Coq_bot)), (Coq_weaken ((Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)),
        (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), (Coq_hypo ((Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)),
        (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Coq_bot)), z)), (Obj.magic (Inl __)))))))), (Coq_imp_intro
        ((Cons ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)))))),
        (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot,
        (Coq_imp_elim ((Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), (Cons ((Coq_imp (y, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), z)), Nil)))))))), (Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot, (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), (Cons ((Coq_imp (y, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), z)), Nil)))))))), (Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), (Obj.magic (Inl __)))), (Coq_imp_intro ((Cons
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), (Cons
        ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)), Nil)))))))), x,
        (Coq_imp (y, Coq_bot)), (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), (Cons ((Coq_imp (y, Coq_bot)),
        (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Coq_bot)), z)), Nil)))))))), (Coq_imp (y, Coq_bot)), x,
        (Coq_weaken ((Cons ((Coq_imp (y, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z)),
        Nil)))))), (Coq_imp (y, Coq_bot)), (Coq_imp ((Coq_imp (x, (Coq_imp
        (y, Coq_bot)))), Coq_bot)), (Coq_hypo ((Cons ((Coq_imp (y, Coq_bot)),
        (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Coq_bot)), z)), Nil)))))), (Coq_imp (y, Coq_bot)),
        (Obj.magic (Inl __)))))))))))))))))))))))), (Coq_imp_intro (Nil,
        (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)),
        (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Coq_bot)), z)), (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)), (Coq_imp ((Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), z,
        (Coq_dneg ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))), z,
        (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (z,
        Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (z, Coq_bot)),
        (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp
        (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))), (Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot, (Coq_weaken ((Cons ((Coq_imp ((Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)),
        Nil)))), (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)),
        (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))),
        Coq_bot)), (Coq_imp (z, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp ((Coq_imp ((Coq_imp
        ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), Coq_bot)))), Coq_bot)),
        (Obj.magic (Inr (Inl __))))))), (Coq_imp_intro ((Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))), (Coq_imp
        ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), Coq_bot)), (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp
        (x, Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))), (Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons
        ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))))),
        z, Coq_bot, (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)),
        z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)),
        Nil)))))))), (Coq_imp (z, Coq_bot)), (Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), (Coq_weaken ((Cons ((Coq_imp (z, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp
        (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))), (Coq_imp (z, Coq_bot)), (Coq_imp
        ((Coq_imp (x, Coq_bot)), z)), (Coq_hypo ((Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))), (Coq_imp (z,
        Coq_bot)), (Obj.magic (Inl __)))))))), (Coq_dneg ((Cons ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))), z, (Coq_imp_intro ((Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))), (Coq_imp (z, Coq_bot)),
        Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (z, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))))), (Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot, (Coq_weaken ((Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))), (Coq_imp ((Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Coq_imp (z,
        Coq_bot)), (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)),
        (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))),
        (Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Coq_weaken ((Cons
        ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))),
        (Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_hypo ((Cons
        ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))),
        (Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Obj.magic (Inr (Inl __))))))))))), (Coq_imp_intro ((Cons
        ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)),
        z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons ((Coq_imp
        (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))))))), (Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp (z, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))))))), x, Coq_bot, (Coq_imp_intro
        ((Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))))))))), x,
        Coq_bot, (Coq_imp_elim ((Cons (x, (Cons ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)),
        (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)),
        Nil)))))))))))))))), z, Coq_bot, (Coq_weaken ((Cons ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp (z, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))))))), (Coq_imp (z, Coq_bot)), x,
        (Coq_weaken ((Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)),
        (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)),
        Nil)))))))))))), (Coq_imp (z, Coq_bot)), (Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), (Coq_hypo ((Cons ((Coq_imp (z, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))))), (Coq_imp (z, Coq_bot)),
        (Obj.magic (Inr (Inr (Inr (Inl __))))))))))), (Coq_imp_elim ((Cons
        (x, (Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))))))))))),
        (Coq_imp (y, Coq_bot)), z, (Coq_weaken ((Cons ((Coq_imp (x, (Coq_imp
        (y, Coq_bot)))), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))))))), (Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), x, (Coq_weaken ((Cons ((Coq_imp (z, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))))), (Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), (Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Coq_weaken
        ((Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp
        ((Coq_imp (x, Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp
        (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))), (Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), (Coq_imp (z, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))), (Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), (Obj.magic (Inl __)))))))))), (Coq_imp_elim ((Cons
        (x, (Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))))))))))), x,
        (Coq_imp (y, Coq_bot)), (Coq_weaken ((Cons ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)),
        (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)),
        Nil)))))))))))))), (Coq_imp (x, (Coq_imp (y, Coq_bot)))), x,
        (Coq_hypo ((Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons
        ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)),
        z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons ((Coq_imp
        (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))))))))),
        (Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Obj.magic (Inl __)))))),
        (Coq_hypo ((Cons (x, (Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons
        ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)),
        Nil)))))))))))))))), x, (Obj.magic (Inl __)))))))))))), (Coq_dneg
        ((Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))))))))), x,
        (Coq_imp_intro ((Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons
        ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)),
        z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons ((Coq_imp
        (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))))))))),
        (Coq_imp (x, Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons
        ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)),
        z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons ((Coq_imp
        (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))))))))))), z,
        Coq_bot, (Coq_weaken ((Cons ((Coq_imp (x, (Coq_imp (y, Coq_bot)))),
        (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons
        ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)),
        Nil)))))))))))))), (Coq_imp (z, Coq_bot)), (Coq_imp (x, Coq_bot)),
        (Coq_weaken ((Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)),
        (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)),
        Nil)))))))))))), (Coq_imp (z, Coq_bot)), (Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), (Coq_hypo ((Cons ((Coq_imp (z, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))))), (Coq_imp (z, Coq_bot)),
        (Obj.magic (Inr (Inr (Inr (Inl __))))))))))), (Coq_imp_elim ((Cons
        ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)),
        (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)),
        Nil)))))))))))))))), (Coq_imp (x, Coq_bot)), z, (Coq_weaken ((Cons
        ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))))))))),
        (Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp (x, Coq_bot)),
        (Coq_weaken ((Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)),
        (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (x, (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)),
        Nil)))))))))))), (Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (y,
        Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons
        ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp
        ((Coq_imp (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))))),
        (Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp (z, Coq_bot)),
        (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Cons ((Coq_imp (z,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp (x, (Coq_imp (y,
        Coq_bot)))), Coq_bot)), Coq_bot)), (Cons ((Coq_imp ((Coq_imp
        ((Coq_imp ((Coq_imp (x, Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp
        (y, Coq_bot)), z)), Coq_bot)))), Coq_bot)), Nil)))))))))), (Coq_imp
        ((Coq_imp (x, Coq_bot)), z)), (Obj.magic (Inr (Inl __))))))))))),
        (Coq_hypo ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp (x,
        (Coq_imp (y, Coq_bot)))), (Cons ((Coq_imp (z, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp (y, Coq_bot)), z)), (Cons ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (x,
        Coq_bot)), z)), (Coq_imp ((Coq_imp ((Coq_imp (y, Coq_bot)), z)),
        Coq_bot)))), Coq_bot)), Nil)))))))))))))))), (Coq_imp (x, Coq_bot)),
        (Obj.magic (Inl __)))))))))))))))))))))))))))))))))))))))

    (** val meet_bott : formula -> eq_B **)

    let meet_bott x =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (Coq_bot, (Coq_imp (x,
        Coq_bot)))), Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp
        ((Coq_imp (Coq_bot, (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)),
        (Coq_imp (Coq_bot, (Coq_imp (x, Coq_bot)))), Coq_bot, (Coq_hypo
        ((Cons ((Coq_imp ((Coq_imp (Coq_bot, (Coq_imp (x, Coq_bot)))),
        Coq_bot)), Nil)), (Coq_imp ((Coq_imp (Coq_bot, (Coq_imp (x,
        Coq_bot)))), Coq_bot)), (Obj.magic (Inl __)))), (Coq_imp_intro ((Cons
        ((Coq_imp ((Coq_imp (Coq_bot, (Coq_imp (x, Coq_bot)))), Coq_bot)),
        Nil)), Coq_bot, (Coq_imp (x, Coq_bot)), (Coq_imp_intro ((Cons
        (Coq_bot, (Cons ((Coq_imp ((Coq_imp (Coq_bot, (Coq_imp (x,
        Coq_bot)))), Coq_bot)), Nil)))), x, Coq_bot, (Coq_weaken ((Cons
        (Coq_bot, (Cons ((Coq_imp ((Coq_imp (Coq_bot, (Coq_imp (x,
        Coq_bot)))), Coq_bot)), Nil)))), Coq_bot, x, (Coq_hypo ((Cons
        (Coq_bot, (Cons ((Coq_imp ((Coq_imp (Coq_bot, (Coq_imp (x,
        Coq_bot)))), Coq_bot)), Nil)))), Coq_bot,
        (Obj.magic (Inl __)))))))))))))), (Coq_imp_intro (Nil, Coq_bot,
        (Coq_imp ((Coq_imp (Coq_bot, (Coq_imp (x, Coq_bot)))), Coq_bot)),
        (Coq_imp_intro ((Cons (Coq_bot, Nil)), (Coq_imp (Coq_bot, (Coq_imp
        (x, Coq_bot)))), Coq_bot, (Coq_weaken ((Cons (Coq_bot, Nil)),
        Coq_bot, (Coq_imp (Coq_bot, (Coq_imp (x, Coq_bot)))), (Coq_hypo
        ((Cons (Coq_bot, Nil)), Coq_bot, (Obj.magic (Inl __)))))))))))

    (** val join_bott : formula -> eq_B **)

    let join_bott x =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), x)),
        x, (Coq_imp_elim ((Cons ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), x)),
        Nil)), (Coq_imp (Coq_bot, Coq_bot)), x, (Coq_hypo ((Cons ((Coq_imp
        ((Coq_imp (Coq_bot, Coq_bot)), x)), Nil)), (Coq_imp ((Coq_imp
        (Coq_bot, Coq_bot)), x)), (Obj.magic (Inl __)))), (Coq_imp_intro
        ((Cons ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), x)), Nil)), Coq_bot,
        Coq_bot, (Coq_hypo ((Cons (Coq_bot, (Cons ((Coq_imp ((Coq_imp
        (Coq_bot, Coq_bot)), x)), Nil)))), Coq_bot,
        (Obj.magic (Inl __)))))))))), (Coq_imp_intro (Nil, x, (Coq_imp
        ((Coq_imp (Coq_bot, Coq_bot)), x)), (Coq_imp_intro ((Cons (x, Nil)),
        (Coq_imp (Coq_bot, Coq_bot)), x, (Coq_weaken ((Cons (x, Nil)), x,
        (Coq_imp (Coq_bot, Coq_bot)), (Coq_hypo ((Cons (x, Nil)), x,
        (Obj.magic (Inl __)))))))))))

    (** val meet_top : formula -> eq_B **)

    let meet_top x =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp ((Coq_imp (Coq_bot,
        Coq_bot)), (Coq_imp (x, Coq_bot)))), Coq_bot)), x, (Coq_dneg ((Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x,
        Coq_bot)))), Coq_bot)), Nil)), x, (Coq_imp_intro ((Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)))),
        Coq_bot)), Nil)), (Coq_imp (x, Coq_bot)), Coq_bot, (Coq_imp_elim
        ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)))),
        (Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)))),
        Coq_bot, (Coq_weaken ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (Coq_bot,
        Coq_bot)), (Coq_imp (x, Coq_bot)))), Coq_bot)), Nil)), (Coq_imp
        ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)))),
        Coq_bot)), (Coq_imp (x, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)))),
        Coq_bot)), Nil)), (Coq_imp ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)),
        (Coq_imp (x, Coq_bot)))), Coq_bot)), (Obj.magic (Inl __)))))),
        (Coq_imp_intro ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)))),
        Coq_bot)), Nil)))), (Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x,
        Coq_bot)), (Coq_weaken ((Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x,
        Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (x, Coq_bot)), (Coq_imp
        (Coq_bot, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp (x, Coq_bot)), (Cons
        ((Coq_imp ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x,
        Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (x, Coq_bot)),
        (Obj.magic (Inl __)))))))))))))))), (Coq_imp_intro (Nil, x, (Coq_imp
        ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)))),
        Coq_bot)), (Coq_imp_intro ((Cons (x, Nil)), (Coq_imp ((Coq_imp
        (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)))), Coq_bot, (Coq_imp_elim
        ((Cons ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x,
        Coq_bot)))), (Cons (x, Nil)))), (Coq_imp (Coq_bot, Coq_bot)),
        Coq_bot, (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp (Coq_bot,
        Coq_bot)), (Coq_imp (x, Coq_bot)))), (Cons (x, Nil)))), (Coq_imp
        (Coq_bot, Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp
        (Coq_bot, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)),
        (Coq_imp (x, Coq_bot)))), (Cons (x, Nil)))))), x, Coq_bot,
        (Coq_imp_elim ((Cons ((Coq_imp (Coq_bot, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)))), (Cons (x,
        Nil)))))), (Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)),
        (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp
        (x, Coq_bot)))), (Cons (x, Nil)))), (Coq_imp ((Coq_imp (Coq_bot,
        Coq_bot)), (Coq_imp (x, Coq_bot)))), (Coq_imp (Coq_bot, Coq_bot)),
        (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp
        (x, Coq_bot)))), (Cons (x, Nil)))), (Coq_imp ((Coq_imp (Coq_bot,
        Coq_bot)), (Coq_imp (x, Coq_bot)))), (Obj.magic (Inl __)))))),
        (Coq_hypo ((Cons ((Coq_imp (Coq_bot, Coq_bot)), (Cons ((Coq_imp
        ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)))), (Cons (x,
        Nil)))))), (Coq_imp (Coq_bot, Coq_bot)), (Obj.magic (Inl __)))))),
        (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp
        (x, Coq_bot)))), (Cons (x, Nil)))), x, (Coq_imp (Coq_bot, Coq_bot)),
        (Coq_weaken ((Cons (x, Nil)), x, (Coq_imp ((Coq_imp (Coq_bot,
        Coq_bot)), (Coq_imp (x, Coq_bot)))), (Coq_hypo ((Cons (x, Nil)), x,
        (Obj.magic (Inl __)))))))))))), (Coq_imp_intro ((Cons ((Coq_imp
        ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)))), (Cons (x,
        Nil)))), Coq_bot, Coq_bot, (Coq_hypo ((Cons (Coq_bot, (Cons ((Coq_imp
        ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)))), (Cons (x,
        Nil)))))), Coq_bot, (Obj.magic (Inl __)))))))))))))

    (** val join_top : formula -> eq_B **)

    let join_top x =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp ((Coq_imp (Coq_bot,
        Coq_bot)), Coq_bot)), x)), (Coq_imp (Coq_bot, Coq_bot)),
        (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp ((Coq_imp (Coq_bot,
        Coq_bot)), Coq_bot)), x)), Nil)), Coq_bot, Coq_bot, (Coq_hypo ((Cons
        (Coq_bot, (Cons ((Coq_imp ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)),
        Coq_bot)), x)), Nil)))), Coq_bot, (Obj.magic (Inl __)))))))),
        (Coq_imp_intro (Nil, (Coq_imp (Coq_bot, Coq_bot)), (Coq_imp ((Coq_imp
        ((Coq_imp (Coq_bot, Coq_bot)), Coq_bot)), x)), (Coq_imp_intro ((Cons
        ((Coq_imp (Coq_bot, Coq_bot)), Nil)), (Coq_imp ((Coq_imp (Coq_bot,
        Coq_bot)), Coq_bot)), x, (Coq_dneg ((Cons ((Coq_imp ((Coq_imp
        (Coq_bot, Coq_bot)), Coq_bot)), (Cons ((Coq_imp (Coq_bot, Coq_bot)),
        Nil)))), x, (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp (Coq_bot,
        Coq_bot)), Coq_bot)), (Cons ((Coq_imp (Coq_bot, Coq_bot)), Nil)))),
        (Coq_imp (x, Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (x,
        Coq_bot)), (Cons ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), Coq_bot)),
        (Cons ((Coq_imp (Coq_bot, Coq_bot)), Nil)))))), (Coq_imp (Coq_bot,
        Coq_bot)), Coq_bot, (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (Coq_bot,
        Coq_bot)), Coq_bot)), (Cons ((Coq_imp (Coq_bot, Coq_bot)), Nil)))),
        (Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), Coq_bot)), (Coq_imp (x,
        Coq_bot)), (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp (Coq_bot, Coq_bot)), Nil)))), (Coq_imp
        ((Coq_imp (Coq_bot, Coq_bot)), Coq_bot)), (Obj.magic (Inl __)))))),
        (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)),
        Coq_bot)), (Cons ((Coq_imp (Coq_bot, Coq_bot)), Nil)))), (Coq_imp
        (Coq_bot, Coq_bot)), (Coq_imp (x, Coq_bot)), (Coq_weaken ((Cons
        ((Coq_imp (Coq_bot, Coq_bot)), Nil)), (Coq_imp (Coq_bot, Coq_bot)),
        (Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), Coq_bot)), (Coq_hypo ((Cons
        ((Coq_imp (Coq_bot, Coq_bot)), Nil)), (Coq_imp (Coq_bot, Coq_bot)),
        (Obj.magic (Inl __)))))))))))))))))))

    (** val meet_compl : formula -> eq_B **)

    let meet_compl x =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp
        (x, Coq_bot)), Coq_bot)))), Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons
        ((Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp (x, Coq_bot)),
        Coq_bot)))), Coq_bot)), Nil)), (Coq_imp (x, (Coq_imp ((Coq_imp (x,
        Coq_bot)), Coq_bot)))), Coq_bot, (Coq_hypo ((Cons ((Coq_imp ((Coq_imp
        (x, (Coq_imp ((Coq_imp (x, Coq_bot)), Coq_bot)))), Coq_bot)), Nil)),
        (Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp (x, Coq_bot)), Coq_bot)))),
        Coq_bot)), (Obj.magic (Inl __)))), (Coq_imp_intro ((Cons ((Coq_imp
        ((Coq_imp (x, (Coq_imp ((Coq_imp (x, Coq_bot)), Coq_bot)))),
        Coq_bot)), Nil)), x, (Coq_imp ((Coq_imp (x, Coq_bot)), Coq_bot)),
        (Coq_imp_intro ((Cons (x, (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp
        ((Coq_imp (x, Coq_bot)), Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp
        (x, Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (x, Coq_bot)),
        (Cons (x, (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp (x,
        Coq_bot)), Coq_bot)))), Coq_bot)), Nil)))))), x, Coq_bot, (Coq_hypo
        ((Cons ((Coq_imp (x, Coq_bot)), (Cons (x, (Cons ((Coq_imp ((Coq_imp
        (x, (Coq_imp ((Coq_imp (x, Coq_bot)), Coq_bot)))), Coq_bot)),
        Nil)))))), (Coq_imp (x, Coq_bot)), (Obj.magic (Inl __)))),
        (Coq_weaken ((Cons (x, (Cons ((Coq_imp ((Coq_imp (x, (Coq_imp
        ((Coq_imp (x, Coq_bot)), Coq_bot)))), Coq_bot)), Nil)))), x, (Coq_imp
        (x, Coq_bot)), (Coq_hypo ((Cons (x, (Cons ((Coq_imp ((Coq_imp (x,
        (Coq_imp ((Coq_imp (x, Coq_bot)), Coq_bot)))), Coq_bot)), Nil)))), x,
        (Obj.magic (Inl __)))))))))))))))), (Coq_imp_intro (Nil, Coq_bot,
        (Coq_imp ((Coq_imp (x, (Coq_imp ((Coq_imp (x, Coq_bot)), Coq_bot)))),
        Coq_bot)), (Coq_imp_intro ((Cons (Coq_bot, Nil)), (Coq_imp (x,
        (Coq_imp ((Coq_imp (x, Coq_bot)), Coq_bot)))), Coq_bot, (Coq_weaken
        ((Cons (Coq_bot, Nil)), Coq_bot, (Coq_imp (x, (Coq_imp ((Coq_imp (x,
        Coq_bot)), Coq_bot)))), (Coq_hypo ((Cons (Coq_bot, Nil)), Coq_bot,
        (Obj.magic (Inl __)))))))))))

    (** val join_compl : formula -> eq_B **)

    let join_compl x =
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp
        (x, Coq_bot)))), (Coq_imp (Coq_bot, Coq_bot)), (Coq_imp_intro ((Cons
        ((Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp (x, Coq_bot)))), Nil)),
        Coq_bot, Coq_bot, (Coq_hypo ((Cons (Coq_bot, (Cons ((Coq_imp
        ((Coq_imp (x, Coq_bot)), (Coq_imp (x, Coq_bot)))), Nil)))), Coq_bot,
        (Obj.magic (Inl __)))))))), (Coq_imp_intro (Nil, (Coq_imp (Coq_bot,
        Coq_bot)), (Coq_imp ((Coq_imp (x, Coq_bot)), (Coq_imp (x,
        Coq_bot)))), (Coq_imp_intro ((Cons ((Coq_imp (Coq_bot, Coq_bot)),
        Nil)), (Coq_imp (x, Coq_bot)), (Coq_imp (x, Coq_bot)), (Coq_hypo
        ((Cons ((Coq_imp (x, Coq_bot)), (Cons ((Coq_imp (Coq_bot, Coq_bot)),
        Nil)))), (Coq_imp (x, Coq_bot)), (Obj.magic (Inl __)))))))))

    (** val meet_distrib : formula -> formula -> formula -> eq_B **)

    let meet_distrib b c a =
      let lemma = meet_comm (join b c) a in
      Obj.magic trans_co_eq_inv_arrow_morphism
        eq_B_relation.equivalence_Transitive (meet (join b c) a)
        (meet a (join b c)) lemma (join (meet b a) (meet c a))
        (join (meet b a) (meet c a))
        (let lemma0 = meet_comm b a in
         trans_sym_co_inv_impl_type_morphism (equivalence_PER eq_B_relation)
           (meet a (join b c)) (join (meet b a) (meet c a))
           (join (meet a b) (meet c a))
           (join_morphism (meet b a) (meet a b) lemma0 (meet c a) (meet c a)
             (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive
               (meet c a)))
           (let lemma1 = meet_comm c a in
            trans_sym_co_inv_impl_type_morphism
              (equivalence_PER eq_B_relation) (meet a (join b c))
              (join (meet a b) (meet c a)) (join (meet a b) (meet a c))
              (reflexive_partial_app_morphism join join_morphism (meet a b)
                (reflexive_proper_proxy eq_B_relation.equivalence_Reflexive
                  (meet a b))
                (meet c a) (meet a c) lemma1)
              (let lemma6 = join_distrib a b (meet a c) in
               trans_sym_co_inv_impl_type_morphism
                 (equivalence_PER eq_B_relation) (meet a (join b c))
                 (join (meet a b) (meet a c))
                 (meet (join a (meet a c)) (join b (meet a c))) lemma6
                 (let lemma7 = join_absorb a c in
                  trans_sym_co_inv_impl_type_morphism
                    (equivalence_PER eq_B_relation) (meet a (join b c))
                    (meet (join a (meet a c)) (join b (meet a c)))
                    (meet a (join b (meet a c)))
                    (meet_morphism (join a (meet a c)) a lemma7
                      (join b (meet a c)) (join b (meet a c))
                      (reflexive_proper_proxy
                        eq_B_relation.equivalence_Reflexive
                        (join b (meet a c))))
                    (let lemma9 = join_comm b (meet a c) in
                     trans_sym_co_inv_impl_type_morphism
                       (equivalence_PER eq_B_relation) (meet a (join b c))
                       (meet a (join b (meet a c)))
                       (meet a (join (meet a c) b))
                       (reflexive_partial_app_morphism meet meet_morphism a
                         (reflexive_proper_proxy
                           eq_B_relation.equivalence_Reflexive a)
                         (join b (meet a c)) (join (meet a c) b) lemma9)
                       (let lemma10 = join_distrib a c b in
                        trans_sym_co_inv_impl_type_morphism
                          (equivalence_PER eq_B_relation) (meet a (join b c))
                          (meet a (join (meet a c) b))
                          (meet a (meet (join a b) (join c b)))
                          (reflexive_partial_app_morphism meet meet_morphism
                            a
                            (reflexive_proper_proxy
                              eq_B_relation.equivalence_Reflexive a)
                            (join (meet a c) b) (meet (join a b) (join c b))
                            lemma10)
                          (let lemma11 = meet_assoc a (join a b) (join c b) in
                           trans_sym_co_inv_impl_type_morphism
                             (equivalence_PER eq_B_relation)
                             (meet a (join b c))
                             (meet a (meet (join a b) (join c b)))
                             (meet (meet a (join a b)) (join c b)) lemma11
                             (let lemma12 = meet_absorb a b in
                              trans_sym_co_inv_impl_type_morphism
                                (equivalence_PER eq_B_relation)
                                (meet a (join b c))
                                (meet (meet a (join a b)) (join c b))
                                (meet a (join c b))
                                (meet_morphism (meet a (join a b)) a lemma12
                                  (join c b) (join c b)
                                  (reflexive_proper_proxy
                                    eq_B_relation.equivalence_Reflexive
                                    (join c b)))
                                (let lemma13 = join_comm b c in
                                 trans_co_eq_inv_arrow_morphism
                                   eq_B_relation.equivalence_Transitive
                                   (meet a (join b c)) (meet a (join c b))
                                   (reflexive_partial_app_morphism meet
                                     meet_morphism a
                                     (reflexive_proper_proxy
                                       eq_B_relation.equivalence_Reflexive a)
                                     (join b c) (join c b) lemma13)
                                   (meet a (join c b)) (meet a (join c b))
                                   (reflexivity
                                     (Obj.magic eq_B_relation).equivalence_Reflexive
                                     (meet a (join c b))))))))))))

    (** val enump : Coq_ccsig.predicate -> nat **)

    let enump p =
      to_nat (Pair ((S (S (S (S (S (S (S (S (S (S (S O))))))))))),
        (Coq_ccsig.enum_predicate p)))

    (** val enumc0 : Coq_ccsig.constant0 -> nat **)

    let enumc0 c =
      to_nat (Pair ((S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))),
        (Coq_ccsig.enum_constant0 c)))

    (** val enumfunc : Coq_ccsig.coq_function -> nat **)

    let enumfunc f =
      to_nat (Pair ((S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))),
        (Coq_ccsig.enum_function f)))

    (** val enumf : formula -> nat **)

    let rec enumf = function
    | Coq_bot -> to_nat (Pair ((S (S (S (S O)))), O))
    | Coq_imp (g, h) ->
      to_nat (Pair ((S (S (S O))), (to_nat (Pair ((enumf g), (enumf h))))))
    | Coq_all g -> to_nat (Pair ((S (S O)), (enumf g)))
    | Coq_atom (p, t) ->
      to_nat (Pair ((S O), (to_nat (Pair ((enump p), (enumt t))))))

    (** val enumt : term -> nat **)

    and enumt = function
    | Coq_bvar x -> to_nat (Pair ((S (S (S (S (S (S (S (S O)))))))), x))
    | Coq_fvar x -> to_nat (Pair ((S (S (S (S (S (S (S O))))))), x))
    | Coq_cnst c -> to_nat (Pair ((S (S (S (S (S (S O)))))), (enumc c)))
    | Coq_func (phi, t') ->
      to_nat (Pair ((S (S (S (S (S O))))),
        (to_nat (Pair ((enumfunc phi), (enumt t'))))))

    (** val enumc : constant -> nat **)

    and enumc = function
    | Coq_original x ->
      to_nat (Pair ((S (S (S (S (S (S (S (S (S (S O)))))))))), (enumc0 x)))
    | Coq_added x ->
      to_nat (Pair ((S (S (S (S (S (S (S (S (S O))))))))), (enumf x)))

    (** val enum : formula -> nat **)

    let enum =
      enumf

    (** val eq_B_join_morph :
        (formula -> formula -> formula, (formula, formula -> formula, eq_B,
        (formula, formula, eq_B, eq_B) respectful) respectful) proper **)

    let eq_B_join_morph =
      join_morphism

    (** val eq_B_meet_morph :
        (formula -> formula -> formula, (formula, formula -> formula, eq_B,
        (formula, formula, eq_B, eq_B) respectful) respectful) proper **)

    let eq_B_meet_morph =
      meet_morphism

    (** val bott : formula **)

    let bott =
      Coq_bot

    type coq_B = formula
   end

  (** val weaken_lem1 :
      formula list -> formula list -> formula -> formula incl -> proof ->
      proof **)

  let rec weaken_lem1 _ delta _ x = function
  | Coq_bot_elim (gamma, p, a) ->
    Coq_bot_elim (delta, (weaken_lem1 gamma delta Coq_bot x p), a)
  | Coq_imp_elim (gamma, a, b, p, p0) ->
    Coq_imp_elim (delta, a, b,
      (weaken_lem1 gamma delta (Coq_imp (a, b)) x p),
      (weaken_lem1 gamma delta a x p0))
  | Coq_imp_intro (gamma, a, b, p) ->
    Coq_imp_intro (delta, a, b,
      (Obj.magic weaken_lem1 (Cons (a, gamma)) (Cons (a, delta)) b
        (fun a0 x1 ->
        match x1 with
        | Inl _ -> Inl __
        | Inr b0 -> Inr (x a0 b0)) p))
  | Coq_dneg (gamma, a, p) ->
    Coq_dneg (delta, a,
      (weaken_lem1 gamma delta (Coq_imp ((Coq_imp (a, Coq_bot)), Coq_bot)) x
        p))
  | Coq_hypo (_, a, i) -> Coq_hypo (delta, a, (x a i))
  | Coq_all_elim (gamma, a, p, t) ->
    Coq_all_elim (delta, a, (weaken_lem1 gamma delta (Coq_all a) x p), t)
  | Coq_all_intro (gamma, a, l, p) ->
    Coq_all_intro (delta, a, l, (fun x1 h1 ->
      weaken_lem1 gamma delta (coq_open a (Coq_fvar x1)) x (p x1 h1)))
  | Coq_weaken (gamma, a, _, p) ->
    let h1 = fun a0 x1 -> Obj.magic x a0 (Inr x1) in
    weaken_lem1 gamma delta a h1 p

  (** val c2t_term : term -> constant -> term -> term **)

  let rec c2t_term t c x =
    match t with
    | Coq_cnst k ->
      (match constant_dec k c with
       | Left -> x
       | Right -> Coq_cnst k)
    | Coq_func (f, t1) -> Coq_func (f, (c2t_term t1 c x))
    | x0 -> x0

  (** val c2t : formula -> constant -> term -> formula **)

  let rec c2t t c x =
    match t with
    | Coq_bot -> Coq_bot
    | Coq_imp (t1, t2) -> Coq_imp ((c2t t1 c x), (c2t t2 c x))
    | Coq_all t1 -> Coq_all (c2t t1 c x)
    | Coq_atom (p, t1) -> Coq_atom (p, (c2t_term t1 c x))

  (** val c2tl : formula list -> constant -> term -> formula list **)

  let rec c2tl l c v =
    match l with
    | Nil -> Nil
    | Cons (x, x0) -> Cons ((c2t x c v), (c2tl x0 c v))

  (** val thm283 :
      formula list -> formula -> nat -> formula -> proof -> proof **)

  let rec thm283 _ _ x k = function
  | Coq_bot_elim (gamma, p, a) ->
    let c = Coq_added k in
    Coq_bot_elim ((c2tl gamma c (Coq_fvar x)), (thm283 gamma Coq_bot x k p),
    (c2t a c (Coq_fvar x)))
  | Coq_imp_elim (gamma, a, b, p, p0) ->
    let c = Coq_added k in
    Coq_imp_elim ((c2tl gamma c (Coq_fvar x)), (c2t a c (Coq_fvar x)),
    (c2t b c (Coq_fvar x)), (thm283 gamma (Coq_imp (a, b)) x k p),
    (thm283 gamma a x k p0))
  | Coq_imp_intro (gamma, a, b, p) ->
    let c = Coq_added k in
    Coq_imp_intro ((c2tl gamma c (Coq_fvar x)), (c2t a c (Coq_fvar x)),
    (c2t b c (Coq_fvar x)), (thm283 (Cons (a, gamma)) b x k p))
  | Coq_dneg (gamma, a, p) ->
    let c = Coq_added k in
    Coq_dneg ((c2tl gamma c (Coq_fvar x)), (c2t a c (Coq_fvar x)),
    (thm283 gamma (Coq_imp ((Coq_imp (a, Coq_bot)), Coq_bot)) x k p))
  | Coq_hypo (gamma, a, i) ->
    let c = Coq_added k in
    Coq_hypo ((c2tl gamma c (Coq_fvar x)), (c2t a c (Coq_fvar x)),
    (let rec f l i0 =
       match l with
       | Nil -> i0
       | Cons (_, l0) ->
         (match Obj.magic i0 with
          | Inl _ -> Obj.magic (Inl __)
          | Inr i1 -> Obj.magic (Inr (f l0 i1)))
     in f gamma i))
  | Coq_all_elim (gamma, a, p, t) ->
    let c = Coq_added k in
    Coq_all_elim ((c2tl gamma c (Coq_fvar x)), (c2t a c (Coq_fvar x)),
    (thm283 gamma (Coq_all a) x k p), (c2t_term t c (Coq_fvar x)))
  | Coq_all_intro (gamma, a, l, p) ->
    let c = Coq_added k in
    Coq_all_intro ((c2tl gamma c (Coq_fvar x)), (c2t a c (Coq_fvar x)), l,
    (fun x0 n -> thm283 gamma (coq_open a (Coq_fvar x0)) x k (p x0 n)))
  | Coq_weaken (gamma, a, b, p) ->
    let c = Coq_added k in
    Coq_weaken ((c2tl gamma c (Coq_fvar x)), (c2t a c (Coq_fvar x)),
    (c2t b c (Coq_fvar x)), (thm283 gamma a x k p))

  (** val ex_intro : formula list -> term -> formula -> proof **)

  let ex_intro delta t f =
    Coq_imp_intro ((Cons ((coq_open f t), delta)), (Coq_all (Coq_imp (f,
      Coq_bot))), Coq_bot, (Coq_imp_elim ((Cons ((Coq_all (Coq_imp (f,
      Coq_bot))), (Cons ((coq_open f t), delta)))), (coq_open f t), Coq_bot,
      (Coq_all_elim ((Cons ((Coq_all (Coq_imp (f, Coq_bot))), (Cons
      ((coq_open f t), delta)))), (Coq_imp (f, Coq_bot)), (Coq_hypo ((Cons
      ((Coq_all (Coq_imp (f, Coq_bot))), (Cons ((coq_open f t), delta)))),
      (Coq_all (Coq_imp (f, Coq_bot))), (Obj.magic (Inl __)))), t)),
      (Coq_weaken ((Cons ((coq_open f t), delta)), (coq_open f t), (Coq_all
      (Coq_imp (f, Coq_bot))), (Coq_hypo ((Cons ((coq_open f t), delta)),
      (coq_open f t), (Obj.magic (Inl __)))))))))

  (** val ex_elim :
      formula list -> formula -> formula -> proof -> (term -> proof) -> proof **)

  let ex_elim gamma f g x x0 =
    Coq_dneg (gamma, g, (Coq_imp_intro (gamma, (Coq_imp (g, Coq_bot)),
      Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (g, Coq_bot)), gamma)),
      (Coq_all (Coq_imp (f, Coq_bot))), Coq_bot, (Coq_weaken (gamma, (Coq_imp
      ((Coq_all (Coq_imp (f, Coq_bot))), Coq_bot)), (Coq_imp (g, Coq_bot)),
      x)), (Coq_all_intro ((Cons ((Coq_imp (g, Coq_bot)), gamma)), (Coq_imp
      (f, Coq_bot)), Nil, (fun x1 _ -> Coq_imp_intro ((Cons ((Coq_imp (g,
      Coq_bot)), gamma)), (open_rec O (Coq_fvar x1) f), Coq_bot,
      (Coq_imp_elim ((Cons ((open_rec O (Coq_fvar x1) f), (Cons ((Coq_imp (g,
      Coq_bot)), gamma)))), g, Coq_bot, (Coq_weaken ((Cons ((Coq_imp (g,
      Coq_bot)), gamma)), (Coq_imp (g, Coq_bot)),
      (open_rec O (Coq_fvar x1) f), (Coq_hypo ((Cons ((Coq_imp (g, Coq_bot)),
      gamma)), (Coq_imp (g, Coq_bot)), (Obj.magic (Inl __)))))),
      (weaken_lem1 (Cons ((coq_open f (Coq_fvar x1)), gamma)) (Cons
        ((open_rec O (Coq_fvar x1) f), (Cons ((Coq_imp (g, Coq_bot)),
        gamma)))) g (fun _ h2 ->
        match Obj.magic h2 with
        | Inl _ -> Obj.magic (Inl __)
        | Inr b -> Obj.magic (Inr (Inr b))) (x0 (Coq_fvar x1))))))))))))))

  (** val lemma_HE1 : formula list -> formula -> proof **)

  let lemma_HE1 delta h =
    Coq_imp_intro (delta, (Coq_all (Coq_imp ((Coq_imp (h, (Coq_all h))),
      Coq_bot))), (Coq_imp ((Coq_imp ((Coq_all (Coq_imp ((Coq_imp (h,
      (Coq_all h))), Coq_bot))), Coq_bot)), Coq_bot)), (Coq_imp_intro ((Cons
      ((Coq_all (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))), delta)),
      (Coq_imp ((Coq_all (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))),
      Coq_bot)), Coq_bot,
      (ex_elim (Cons ((Coq_imp ((Coq_all (Coq_imp ((Coq_imp (h, (Coq_all
        h))), Coq_bot))), Coq_bot)), (Cons ((Coq_all (Coq_imp ((Coq_imp (h,
        (Coq_all h))), Coq_bot))), delta)))) (Coq_imp (h, (Coq_all h)))
        Coq_bot (Coq_hypo ((Cons ((Coq_imp ((Coq_all (Coq_imp ((Coq_imp (h,
        (Coq_all h))), Coq_bot))), Coq_bot)), (Cons ((Coq_all (Coq_imp
        ((Coq_imp (h, (Coq_all h))), Coq_bot))), delta)))), (Coq_imp
        ((Coq_all (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))),
        Coq_bot)), (Obj.magic (Inl __)))) (fun t -> Coq_imp_elim ((Cons
        ((coq_open (Coq_imp (h, (Coq_all h))) t), (Cons ((Coq_imp ((Coq_all
        (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))), Coq_bot)), (Cons
        ((Coq_all (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))),
        delta)))))), (coq_open (Coq_imp (h, (Coq_all h))) t), Coq_bot,
        (Coq_weaken ((Cons ((Coq_imp ((Coq_all (Coq_imp ((Coq_imp (h,
        (Coq_all h))), Coq_bot))), Coq_bot)), (Cons ((Coq_all (Coq_imp
        ((Coq_imp (h, (Coq_all h))), Coq_bot))), delta)))), (Coq_imp
        ((coq_open (Coq_imp (h, (Coq_all h))) t), Coq_bot)),
        (coq_open (Coq_imp (h, (Coq_all h))) t), (Coq_weaken ((Cons ((Coq_all
        (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))), delta)), (Coq_imp
        ((coq_open (Coq_imp (h, (Coq_all h))) t), Coq_bot)), (Coq_imp
        ((Coq_all (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))),
        Coq_bot)), (Coq_all_elim ((Cons ((Coq_all (Coq_imp ((Coq_imp (h,
        (Coq_all h))), Coq_bot))), delta)), (Coq_imp ((Coq_imp (h, (Coq_all
        h))), Coq_bot)), (Coq_hypo ((Cons ((Coq_all (Coq_imp ((Coq_imp (h,
        (Coq_all h))), Coq_bot))), delta)), (Coq_all (Coq_imp ((Coq_imp (h,
        (Coq_all h))), Coq_bot))), (Obj.magic (Inl __)))), t)))))), (Coq_hypo
        ((Cons ((coq_open (Coq_imp (h, (Coq_all h))) t), (Cons ((Coq_imp
        ((Coq_all (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))),
        Coq_bot)), (Cons ((Coq_all (Coq_imp ((Coq_imp (h, (Coq_all h))),
        Coq_bot))), delta)))))), (coq_open (Coq_imp (h, (Coq_all h))) t),
        (Obj.magic (Inl __))))))))))

  (** val disj_elim :
      formula list -> formula -> formula -> formula -> proof -> proof -> proof **)

  let disj_elim gamma f g h x x0 =
    Coq_imp_intro (gamma, (Coq_imp ((Coq_imp (f, Coq_bot)), g)), h,
      (Coq_imp_elim ((Cons ((Coq_imp ((Coq_imp (f, Coq_bot)), g)), gamma)),
      (Coq_imp ((Coq_imp (h, Coq_bot)), h)), h,
      (peirce (Cons ((Coq_imp ((Coq_imp (f, Coq_bot)), g)), gamma)) h Coq_bot),
      (proof_imp_trans (Cons ((Coq_imp ((Coq_imp (f, Coq_bot)), g)), gamma))
        (Coq_imp (h, Coq_bot)) f h
        (proof_imp_trans (Cons ((Coq_imp ((Coq_imp (f, Coq_bot)), g)),
          gamma)) (Coq_imp (h, Coq_bot)) (Coq_imp (g, Coq_bot)) f
          (proof_imp_contrapos (Cons ((Coq_imp ((Coq_imp (f, Coq_bot)), g)),
            gamma)) g h (Coq_weaken (gamma, (Coq_imp (g, h)), (Coq_imp
            ((Coq_imp (f, Coq_bot)), g)), (Coq_imp_intro (gamma, g, h, x0)))))
          (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp (f, Coq_bot)), g)),
          gamma)), (Coq_imp (g, Coq_bot)), f, (Coq_dneg ((Cons ((Coq_imp (g,
          Coq_bot)), (Cons ((Coq_imp ((Coq_imp (f, Coq_bot)), g)), gamma)))),
          f, (Coq_imp_intro ((Cons ((Coq_imp (g, Coq_bot)), (Cons ((Coq_imp
          ((Coq_imp (f, Coq_bot)), g)), gamma)))), (Coq_imp (f, Coq_bot)),
          Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (f, Coq_bot)), (Cons
          ((Coq_imp (g, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (f, Coq_bot)),
          g)), gamma)))))), g, Coq_bot, (Coq_weaken ((Cons ((Coq_imp (g,
          Coq_bot)), (Cons ((Coq_imp ((Coq_imp (f, Coq_bot)), g)), gamma)))),
          (Coq_imp (g, Coq_bot)), (Coq_imp (f, Coq_bot)), (Coq_hypo ((Cons
          ((Coq_imp (g, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (f, Coq_bot)),
          g)), gamma)))), (Coq_imp (g, Coq_bot)), (Obj.magic (Inl __)))))),
          (Coq_imp_elim ((Cons ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp (g,
          Coq_bot)), (Cons ((Coq_imp ((Coq_imp (f, Coq_bot)), g)),
          gamma)))))), (Coq_imp (f, Coq_bot)), g, (Coq_weaken ((Cons
          ((Coq_imp (g, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (f, Coq_bot)),
          g)), gamma)))), (Coq_imp ((Coq_imp (f, Coq_bot)), g)), (Coq_imp (f,
          Coq_bot)), (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (f, Coq_bot)),
          g)), gamma)), (Coq_imp ((Coq_imp (f, Coq_bot)), g)), (Coq_imp (g,
          Coq_bot)), (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (f, Coq_bot)), g)),
          gamma)), (Coq_imp ((Coq_imp (f, Coq_bot)), g)),
          (Obj.magic (Inl __)))))))), (Coq_hypo ((Cons ((Coq_imp (f,
          Coq_bot)), (Cons ((Coq_imp (g, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
          (f, Coq_bot)), g)), gamma)))))), (Coq_imp (f, Coq_bot)),
          (Obj.magic (Inl __)))))))))))))))
        (Coq_weaken (gamma, (Coq_imp (f, h)), (Coq_imp ((Coq_imp (f,
        Coq_bot)), g)), (Coq_imp_intro (gamma, f, h, x))))))))

  (** val coq_LEM : formula list -> formula -> proof **)

  let coq_LEM gamma f =
    Coq_imp_intro (gamma, (Coq_imp (f, Coq_bot)), (Coq_imp (f, Coq_bot)),
      (Coq_hypo ((Cons ((Coq_imp (f, Coq_bot)), gamma)), (Coq_imp (f,
      Coq_bot)), (Obj.magic (Inl __)))))

  (** val lemma_HE2_1 : formula -> formula list -> proof **)

  let lemma_HE2_1 h delta =
    Coq_imp_elim ((Cons ((Coq_all h), delta)),
      (coq_open (Coq_imp (h, (Coq_all h))) (Coq_fvar O)), (Coq_imp ((Coq_all
      (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))), Coq_bot)),
      (Coq_imp_intro ((Cons ((Coq_all h), delta)),
      (coq_open (Coq_imp (h, (Coq_all h))) (Coq_fvar O)), (Coq_imp ((Coq_all
      (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))), Coq_bot)),
      (ex_intro (Cons ((Coq_all h), delta)) (Coq_fvar O) (Coq_imp (h,
        (Coq_all h)))))),
      (Coq_imp_intro ((Cons ((Coq_all h), delta)), (coq_open h (Coq_fvar O)),
      (Coq_all h), (Coq_weaken ((Cons ((Coq_all h), delta)), (Coq_all h),
      (coq_open h (Coq_fvar O)), (Coq_hypo ((Cons ((Coq_all h), delta)),
      (Coq_all h), (Obj.magic (Inl __)))))))))

  (** val lemma_HE2_2 : formula -> formula list -> proof **)

  let lemma_HE2_2 h delta =
    Coq_imp_intro ((Cons ((Coq_imp ((Coq_all h), Coq_bot)), delta)), (Coq_all
      (Coq_imp ((Coq_imp (h, Coq_bot)), Coq_bot))), Coq_bot, (Coq_imp_elim
      ((Cons ((Coq_all (Coq_imp ((Coq_imp (h, Coq_bot)), Coq_bot))), (Cons
      ((Coq_imp ((Coq_all h), Coq_bot)), delta)))), (Coq_all h), Coq_bot,
      (Coq_weaken ((Cons ((Coq_imp ((Coq_all h), Coq_bot)), delta)), (Coq_imp
      ((Coq_all h), Coq_bot)), (Coq_all (Coq_imp ((Coq_imp (h, Coq_bot)),
      Coq_bot))), (Coq_hypo ((Cons ((Coq_imp ((Coq_all h), Coq_bot)),
      delta)), (Coq_imp ((Coq_all h), Coq_bot)), (Obj.magic (Inl __)))))),
      (Coq_all_intro ((Cons ((Coq_all (Coq_imp ((Coq_imp (h, Coq_bot)),
      Coq_bot))), (Cons ((Coq_imp ((Coq_all h), Coq_bot)), delta)))), h, Nil,
      (fun x _ -> Coq_dneg ((Cons ((Coq_all (Coq_imp ((Coq_imp (h, Coq_bot)),
      Coq_bot))), (Cons ((Coq_imp ((Coq_all h), Coq_bot)), delta)))),
      (coq_open h (Coq_fvar x)), (Coq_all_elim ((Cons ((Coq_all (Coq_imp
      ((Coq_imp (h, Coq_bot)), Coq_bot))), (Cons ((Coq_imp ((Coq_all h),
      Coq_bot)), delta)))), (Coq_imp ((Coq_imp (h, Coq_bot)), Coq_bot)),
      (Coq_hypo ((Cons ((Coq_all (Coq_imp ((Coq_imp (h, Coq_bot)),
      Coq_bot))), (Cons ((Coq_imp ((Coq_all h), Coq_bot)), delta)))),
      (Coq_all (Coq_imp ((Coq_imp (h, Coq_bot)), Coq_bot))),
      (Obj.magic (Inl __)))), (Coq_fvar x))))))))))

  (** val lemma_HE2 : formula list -> formula -> proof **)

  let lemma_HE2 delta h =
    Coq_imp_elim (delta, (Coq_imp ((Coq_imp ((Coq_all h), Coq_bot)), (Coq_imp
      ((Coq_all h), Coq_bot)))), (Coq_imp ((Coq_all (Coq_imp ((Coq_imp (h,
      (Coq_all h))), Coq_bot))), Coq_bot)),
      (disj_elim delta (Coq_all h) (Coq_imp ((Coq_all h), Coq_bot)) (Coq_imp
        ((Coq_all (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))), Coq_bot))
        (lemma_HE2_1 h delta)
        (ex_elim (Cons ((Coq_imp ((Coq_all h), Coq_bot)), delta)) (Coq_imp
          (h, Coq_bot)) (Coq_imp ((Coq_all (Coq_imp ((Coq_imp (h, (Coq_all
          h))), Coq_bot))), Coq_bot)) (lemma_HE2_2 h delta) (fun t ->
          Coq_imp_elim ((Cons ((coq_open (Coq_imp (h, Coq_bot)) t), (Cons
          ((Coq_imp ((Coq_all h), Coq_bot)), delta)))),
          (coq_open (Coq_imp (h, (Coq_all h))) t), (Coq_imp ((Coq_all
          (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))), Coq_bot)),
          (Coq_imp_intro ((Cons ((coq_open (Coq_imp (h, Coq_bot)) t), (Cons
          ((Coq_imp ((Coq_all h), Coq_bot)), delta)))),
          (coq_open (Coq_imp (h, (Coq_all h))) t), (Coq_imp ((Coq_all
          (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot))), Coq_bot)),
          (ex_intro (Cons ((coq_open (Coq_imp (h, Coq_bot)) t), (Cons
            ((Coq_imp ((Coq_all h), Coq_bot)), delta)))) t (Coq_imp (h,
            (Coq_all h)))))),
          (Coq_imp_intro ((Cons ((coq_open (Coq_imp (h, Coq_bot)) t), (Cons
          ((Coq_imp ((Coq_all h), Coq_bot)), delta)))), (coq_open h t),
          (Coq_all h), (Coq_bot_elim ((Cons ((coq_open h t), (Cons
          ((coq_open (Coq_imp (h, Coq_bot)) t), (Cons ((Coq_imp ((Coq_all h),
          Coq_bot)), delta)))))), (Coq_imp_elim ((Cons ((coq_open h t), (Cons
          ((Coq_imp ((coq_open h t), Coq_bot)), (Cons ((Coq_imp ((Coq_all h),
          Coq_bot)), delta)))))), (coq_open h t), Coq_bot, (Coq_weaken ((Cons
          ((Coq_imp ((coq_open h t), Coq_bot)), (Cons ((Coq_imp ((Coq_all h),
          Coq_bot)), delta)))), (Coq_imp ((coq_open h t), Coq_bot)),
          (coq_open h t), (Coq_hypo ((Cons ((Coq_imp ((coq_open h t),
          Coq_bot)), (Cons ((Coq_imp ((Coq_all h), Coq_bot)), delta)))),
          (Coq_imp ((coq_open h t), Coq_bot)), (Obj.magic (Inl __)))))),
          (Coq_hypo ((Cons ((coq_open h t), (Cons ((Coq_imp ((coq_open h t),
          Coq_bot)), (Cons ((Coq_imp ((Coq_all h), Coq_bot)), delta)))))),
          (coq_open h t), (Obj.magic (Inl __)))))), (Coq_all h))))))))),
      (coq_LEM delta (Coq_all h)))

  type coq_HA = (formula, __) sigT

  module CBAproof_completion = Coq_filter_completion(CBAproof)

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

  (** val henkin_equiconsistent :
      ('a1, 'a2) theory -> ('a2, 'a1) coq_TH -> 'a2 **)

  let henkin_equiconsistent h1 = function
  | ExistT (x, p) ->
    let Pair (i, s) = p in
    let ExistT (x0, _) = s in
    let lemma1 = fun h delta _ p0 ->
      let p1 = Coq_imp_intro (delta, (Coq_imp
        ((coq_open h (Coq_cnst (Coq_added (Coq_all h)))), (Coq_all h))),
        Coq_bot, p0)
      in
      let h0 = Coq_all_intro (delta, (Coq_imp ((Coq_imp (h, (Coq_all h))),
        Coq_bot)), Nil, (fun x1 _ ->
        thm283 delta
          (coq_open (Coq_imp ((Coq_imp (h, (Coq_all h))), Coq_bot)) (Coq_cnst
            (Coq_added (Coq_all h))))
          x1 (Coq_all h) p1))
      in
      let h3 = Coq_imp_elim (delta, (Coq_all (Coq_imp ((Coq_imp (h, (Coq_all
        h))), Coq_bot))), (Coq_imp ((Coq_imp ((Coq_all (Coq_imp ((Coq_imp (h,
        (Coq_all h))), Coq_bot))), Coq_bot)), Coq_bot)), (lemma_HE1 delta h),
        h0)
      in
      Coq_imp_elim (delta, (Coq_imp ((Coq_all (Coq_imp ((Coq_imp (h, (Coq_all
      h))), Coq_bot))), Coq_bot)), Coq_bot, h3, (lemma_HE2 delta h))
    in
    let lemma6 = fun eta x1 ->
      let rec f l h =
        match l with
        | Nil ->
          ExistT (Nil, (ExistT (Nil, (Pair ((fun _ h0 -> h0), (Pair
            ((Obj.magic nil_included), (Obj.magic nil_included))))))))
        | Cons (y, l0) ->
          let h3 = fun f0 x2 -> h f0 (in_cons y f0 l0 x2) in
          let s0 = f l0 h3 in
          let ExistT (x2, s1) = s0 in
          let ExistT (x3, p0) = s1 in
          let Pair (i0, p1) = p0 in
          let Pair (i1, i2) = p1 in
          let h5 = h y (in_eq y l0) in
          (match h5 with
           | Inl a ->
             ExistT (x2, (ExistT ((Cons (y, x3)), (Pair ((fun a0 x4 ->
               match x4 with
               | Inl _ ->
                 let rec f0 = function
                 | Nil -> Inl __
                 | Cons (_, l2) -> Inr (Obj.magic f0 l2)
                 in f0 x2
               | Inr i3 ->
                 let h4 = Obj.magic i0 a0 i3 in
                 let rec f0 l1 h6 =
                   match l1 with
                   | Nil -> Inr h6
                   | Cons (_, l2) ->
                     (match h6 with
                      | Inl _ -> Inl __
                      | Inr i4 -> Inr (Obj.magic f0 l2 i4))
                 in f0 x2 h4),
               (Pair (i1, (fun f0 x4 ->
               match x4 with
               | Inl _ -> a
               | Inr i3 -> Obj.magic i2 f0 i3))))))))
           | Inr h0 ->
             ExistT ((Cons (y, x2)), (ExistT (x3, (Pair ((fun a x4 ->
               match x4 with
               | Inl _ -> Inl __
               | Inr b -> Inr (Obj.magic i0 a b)), (Pair ((fun f0 x4 ->
               match x4 with
               | Inl _ -> h0
               | Inr i3 -> Obj.magic i1 f0 i3), i2))))))))
      in f eta x1
    in
    let lemma7 = fun eta x1 x2 ->
      let h3 = lemma6 eta x1 in
      let ExistT (x3, s0) = h3 in
      let ExistT (x4, p0) = s0 in
      let Pair (i0, p1) = p0 in
      let Pair (i1, i2) = p1 in
      ExistT (x4, (Pair (i2,
      (let rec f l hE1 eta0 h0 hEta =
         match l with
         | Nil -> weaken_lem1 eta0 x4 Coq_bot (Obj.magic hEta) h0
         | Cons (y, l0) ->
           let h = hE1 y (Inl __) in
           let h4 = fun x5 hx -> hE1 x5 (Inr hx) in
           let s1 = in_dec formula_dec y l0 in
           (match s1 with
            | Inl i3 ->
              Obj.magic f l0 h4 eta0 h0
                (incl_tran eta0 (Cons (y, (app l0 x4))) (app l0 x4)
                  (Obj.magic hEta) (fun _ x5 ->
                  match Obj.magic x5 with
                  | Inl _ -> in_or_app l0 x4 y (Inl i3)
                  | Inr i4 -> i4))
            | Inr _ ->
              let ExistT (x5, _) = h in
              Obj.magic f l0 (fun x6 hx -> hE1 x6 (Inr hx)) (app l0 x4)
                (lemma1 x5 (app l0 x4) (Cons ((Coq_imp
                  ((coq_open x5 (Coq_cnst (Coq_added (Coq_all x5)))),
                  (Coq_all x5))), (app l0 x4)))
                  (weaken_lem1 eta0 (Cons ((Coq_imp
                    ((coq_open x5 (Coq_cnst (Coq_added (Coq_all x5)))),
                    (Coq_all x5))), (app l0 x4))) Coq_bot (Obj.magic hEta) h0))
                (incl_refl (app l0 x4)))
       in f x3 i1 eta x2 i0))))
    in
    let h3 = lemma7 x i x0 in
    snd (Obj.magic h1 Coq_bot)
      (let ExistT (x1, p0) = h3 in
       let Pair (i0, p1) = p0 in ExistT (x1, (Pair (i0, (ExistT (p1, Tt))))))

  (** val enrich :
      ('a2, 'a1) theory -> ((('a1, 'a2) coq_AxH, 'a2) extension, ((('a1, 'a2)
      coq_TH, 'a1) extension, ((('a1, 'a2) coq_AxH, ('a1, 'a2) coq_TH)
      theory, (('a1, 'a2) coq_TH henkin_complete, (('a1, 'a2) coq_TH, 'a1)
      equicons) prod) prod) prod) prod **)

  let enrich tAtheory =
    let extAxH = fun _ h -> Inl h in
    let extTHT = fun f tf ->
      let h1 = fst (tAtheory f) tf in
      let ExistT (x, p) = h1 in
      ExistT (x,
      (let Pair (i, s) = p in Pair ((fun f0 h -> extAxH f0 (i f0 h)), s)))
    in
    Pair (extAxH, (Pair (extTHT, (Pair ((fun _ -> Pair ((fun hT ->
    let ExistT (x, p) = hT in
    ExistT (x, (Pair ((let Pair (a, _) = p in a),
    (let Pair (_, b) = p in b))))), (fun x -> x))), (Pair ((fun f _ _ ->
    ExistT ((Cons ((Coq_imp ((coq_open f (Coq_cnst (Coq_added (Coq_all f)))),
    (Coq_all f))), Nil)), (Pair ((fun _ _ -> Inr (ExistT (f, __))),
    (let p = Coq_hypo ((Cons ((Coq_imp
       ((coq_open f (Coq_cnst (Coq_added (Coq_all f)))), (Coq_all f))),
       Nil)), (Coq_imp ((coq_open f (Coq_cnst (Coq_added (Coq_all f)))),
       (Coq_all f))), (Obj.magic (Inl __)))
     in
     ExistT (p, Tt)))))),
    (Pair ((fun x -> henkin_equiconsistent tAtheory x), (fun x ->
    extTHT Coq_bot x))))))))))

  (** val theory2filter :
      ('a2, 'a1) theory -> 'a1 CBAproof_completion.coq_Filter **)

  let theory2filter hT =
    { CBAproof_completion.nonempty = (ExistT (CBAproof.top,
      (snd (hT (Coq_imp (Coq_bot, Coq_bot))) (ExistT (Nil, (Pair
        (nil_included,
        (let h = Coq_imp_intro (Nil, Coq_bot, Coq_bot, (Coq_hypo ((Cons
           (Coq_bot, Nil)), Coq_bot, (Obj.magic (Inl __)))))
         in
         ExistT (h, Tt)))))))));
      CBAproof_completion.upwards_closed = (fun x y x0 x1 ->
      let Pair (_, p) = x1 in
      let h' = fst (hT x) x0 in
      let ExistT (x2, p0) = h' in
      let Pair (i, s) = p0 in
      let ExistT (x3, _) = s in
      let hT' = hT y in
      snd hT' (ExistT (x2, (Pair (i,
        (let h = Coq_dneg (x2, y, (Coq_imp_intro (x2, (Coq_imp (y, Coq_bot)),
           Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (y, Coq_bot)), x2)),
           (Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot, (Coq_imp_elim
           ((Cons ((Coq_imp (y, Coq_bot)), x2)), x, (Coq_imp ((Coq_imp (x,
           (Coq_imp (y, Coq_bot)))), Coq_bot)),
           (weaken_lem1 Nil (Cons ((Coq_imp (y, Coq_bot)), x2)) (Coq_imp (x,
             (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot))))
             (nil_lem1 (Cons ((Coq_imp (y, Coq_bot)), x2))) p),
           (Coq_weaken (x2, x, (Coq_imp (y, Coq_bot)), x3)))), (Coq_imp_intro
           ((Cons ((Coq_imp (y, Coq_bot)), x2)), x, (Coq_imp (y, Coq_bot)),
           (Coq_weaken ((Cons ((Coq_imp (y, Coq_bot)), x2)), (Coq_imp (y,
           Coq_bot)), x, (Coq_hypo ((Cons ((Coq_imp (y, Coq_bot)), x2)),
           (Coq_imp (y, Coq_bot)), (Obj.magic (Inl __)))))))))))))
         in
         ExistT (h, Tt)))))));
      CBAproof_completion.meet_closed = (fun x y x0 x1 ->
      let h1 = fst (hT x) x0 in
      let h2 = fst (hT y) x1 in
      let ExistT (x2, p) = h1 in
      let ExistT (x3, p0) = h2 in
      let hT' = hT (Coq_imp ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), Coq_bot))
      in
      snd hT' (ExistT ((app x2 x3), (Pair
        ((included_lem1 x2 x3 (let Pair (a, _) = p in a)
           (let Pair (a, _) = p0 in a)),
        (let Pair (_, s) = p0 in
         let Pair (_, s0) = p in
         let ExistT (x4, _) = s in
         let ExistT (x5, _) = s0 in
         let h = Coq_imp_intro ((app x2 x3), (Coq_imp (x, (Coq_imp (y,
           Coq_bot)))), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (x, (Coq_imp
           (y, Coq_bot)))), (app x2 x3))), y, Coq_bot, (Coq_imp_elim ((Cons
           ((Coq_imp (x, (Coq_imp (y, Coq_bot)))), (app x2 x3))), x, (Coq_imp
           (y, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp (x, (Coq_imp (y,
           Coq_bot)))), (app x2 x3))), (Coq_imp (x, (Coq_imp (y, Coq_bot)))),
           (Obj.magic (Inl __)))), (Coq_weaken ((app x2 x3), x, (Coq_imp (x,
           (Coq_imp (y, Coq_bot)))),
           (weaken_lem1 x2 (app x2 x3) x (incl_appl x2 x3 x2 (incl_refl x2))
             x5))))),
           (Coq_weaken ((app x2 x3), y, (Coq_imp (x, (Coq_imp (y,
           Coq_bot)))),
           (weaken_lem1 x3 (app x2 x3) y (incl_appr x3 x2 x3 (incl_refl x3))
             x4))))))
         in
         ExistT (h, Tt))))))) }

  type ('t, 'ax) coq_T1 = ('t, 'ax) coq_TH

  (** val coq_T1theory :
      ('a2, 'a1) theory -> (('a1, 'a2) coq_AxH, ('a1, 'a2) coq_TH) theory **)

  let coq_T1theory ttheory =
    fst (snd (snd (enrich ttheory)))

  (** val coq_T1filter :
      ('a2, 'a1) theory -> ('a1, 'a2) coq_T1 CBAproof_completion.coq_Filter **)

  let coq_T1filter ttheory =
    theory2filter (coq_T1theory ttheory)

  type ('t, 'ax) coq_Z' = ('t, 'ax) coq_T1 CBAproof_completion.coq_Z

  (** val lem15 :
      ('a2, 'a1) theory -> (('a1, 'a2) coq_T1 CBAproof_completion.coq_Z
      CBAproof_completion.coq_Filter, ((('a1, 'a2) coq_T1, ('a1, 'a2) coq_T1
      CBAproof_completion.coq_Z) CBAproof_completion.equiconsistent, ('a1,
      'a2) coq_T1 CBAproof_completion.coq_Z CBAproof_completion.complete)
      prod) prod **)

  let lem15 ttheory =
    CBAproof_completion.thm22 (coq_T1filter ttheory)

  (** val model_existence1 :
      ('a2, 'a1) theory -> ((('a1, 'a2) coq_Z', 'a1) extension, ('a1, ('a1,
      'a2) coq_Z') equicons) prod **)

  let model_existence1 ttheory =
    let hext = fun f x -> ExistT (O,
      (let p = ttheory f in
       let Pair (s, _) = p in
       let s0 = s x in
       let ExistT (x0, p0) = s0 in
       let Pair (i, s1) = p0 in
       ExistT (x0, (Pair ((fun f0 x1 -> Inl (i f0 x1)), s1)))))
    in
    Pair ((Obj.magic hext),
    (let hZ = lem15 ttheory in
     let Pair (_, p) = hZ in
     let Pair (e, _) = p in
     let Pair (_, b) = e in
     Pair ((fun h -> Obj.magic hext Coq_bot h), (fun h ->
     let h0 = b h in henkin_equiconsistent ttheory h0))))

  type ('t, 'ax) coq_G = ('t, 'ax) coq_T1 CBAproof_completion.coq_F_

  type ('t, 'ax) coq_GAx = __

  type ('t, 'ax) coq_ZAx = (nat, ('t, 'ax) coq_GAx) sigT

  (** val coq_GAx_monotone :
      nat -> nat -> CBAproof_completion.le -> formula -> ('a1, 'a2) coq_GAx
      -> ('a1, 'a2) coq_GAx **)

  let coq_GAx_monotone n m x _ x0 =
    CBAproof_completion.le_rec n x0 (fun _ _ iHle -> Obj.magic (Inl iHle)) m x

  (** val remove_In_neq_In :
      formula list -> formula -> formula -> formula in0 -> formula in0 **)

  let rec remove_In_neq_In l y xn x =
    match l with
    | Nil -> assert false (* absurd case *)
    | Cons (y0, l0) ->
      (match Obj.magic x with
       | Inl _ ->
         let s = CBAproof.id_B_dec xn y0 in
         (match s with
          | Left -> assert false (* absurd case *)
          | Right -> Obj.magic (Inl __))
       | Inr i ->
         let s = CBAproof.id_B_dec xn y0 in
         (match s with
          | Left -> remove_In_neq_In l0 y xn i
          | Right -> Obj.magic (Inr (remove_In_neq_In l0 y xn i))))

  (** val proof_fold_left :
      formula list -> formula -> proof -> CBAproof_completion.leq **)

  let rec proof_fold_left l f x =
    match l with
    | Nil ->
      Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp ((Coq_imp (Coq_bot,
        Coq_bot)), (Coq_imp (f, Coq_bot)))), Coq_bot)), (Coq_imp (Coq_bot,
        Coq_bot)), (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp ((Coq_imp
        (Coq_bot, Coq_bot)), (Coq_imp (f, Coq_bot)))), Coq_bot)), Nil)),
        Coq_bot, Coq_bot, (Coq_hypo ((Cons (Coq_bot, (Cons ((Coq_imp
        ((Coq_imp ((Coq_imp (Coq_bot, Coq_bot)), (Coq_imp (f, Coq_bot)))),
        Coq_bot)), Nil)))), Coq_bot, (Obj.magic (Inl __)))))))),
        (Coq_imp_intro (Nil, CBAproof.top, (Coq_imp ((Coq_imp (CBAproof.top,
        (Coq_imp (f, Coq_bot)))), Coq_bot)), (Coq_imp_intro ((Cons
        (CBAproof.top, Nil)), (Coq_imp (CBAproof.top, (Coq_imp (f,
        Coq_bot)))), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (CBAproof.top,
        (Coq_imp (f, Coq_bot)))), (Cons (CBAproof.top, Nil)))), f, Coq_bot,
        (Coq_imp_elim ((Cons ((Coq_imp (CBAproof.top, (Coq_imp (f,
        Coq_bot)))), (Cons (CBAproof.top, Nil)))), CBAproof.top, (Coq_imp (f,
        Coq_bot)), (Coq_hypo ((Cons ((Coq_imp (CBAproof.top, (Coq_imp (f,
        Coq_bot)))), (Cons (CBAproof.top, Nil)))), (Coq_imp (CBAproof.top,
        (Coq_imp (f, Coq_bot)))), (Obj.magic (Inl __)))), (Coq_weaken ((Cons
        (CBAproof.top, Nil)), CBAproof.top, (Coq_imp (CBAproof.top, (Coq_imp
        (f, Coq_bot)))), (Coq_hypo ((Cons (CBAproof.top, Nil)), CBAproof.top,
        (Obj.magic (Inl __)))))))), (Coq_weaken ((Cons (CBAproof.top, Nil)),
        f, (Coq_imp (CBAproof.top, (Coq_imp (f, Coq_bot)))), (Coq_weaken
        (Nil, f, CBAproof.top, x)))))))))))
    | Cons (y, l0) ->
      let h = Coq_imp_intro (l0, y, f, x) in
      let iH = proof_fold_left l0 (Coq_imp (y, f)) h in
      CBAproof_completion.leq_trans
        (fold_left CBAproof.meet (Cons (y, l0)) CBAproof.top)
        (CBAproof.meet y (fold_left CBAproof.meet l0 CBAproof.top)) f
        (CBAproof_completion.eq_B_leq
          (fold_left CBAproof.meet (Cons (y, l0)) CBAproof.top)
          (CBAproof.meet y (fold_left CBAproof.meet l0 CBAproof.top))
          (CBAproof_completion.fold_left_meet_cons l0 y))
        (Pair
        ((let a = CBAproof.meet y (fold_left CBAproof.meet l0 CBAproof.top) in
          Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (a, (Coq_imp (f,
          Coq_bot)))), Coq_bot)), a, (Coq_dneg ((Cons ((Coq_imp ((Coq_imp (a,
          (Coq_imp (f, Coq_bot)))), Coq_bot)), Nil)), a, (Coq_imp_intro
          ((Cons ((Coq_imp ((Coq_imp (a, (Coq_imp (f, Coq_bot)))), Coq_bot)),
          Nil)), (Coq_imp (a, Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons
          ((Coq_imp (a, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (a, (Coq_imp (f,
          Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (a, (Coq_imp (f,
          Coq_bot)))), Coq_bot, (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (a,
          (Coq_imp (f, Coq_bot)))), Coq_bot)), Nil)), (Coq_imp ((Coq_imp (a,
          (Coq_imp (f, Coq_bot)))), Coq_bot)), (Coq_imp (a, Coq_bot)),
          (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (a, (Coq_imp (f, Coq_bot)))),
          Coq_bot)), Nil)), (Coq_imp ((Coq_imp (a, (Coq_imp (f, Coq_bot)))),
          Coq_bot)), (Obj.magic (Inl __)))))), (Coq_imp_intro ((Cons
          ((Coq_imp (a, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (a, (Coq_imp (f,
          Coq_bot)))), Coq_bot)), Nil)))), a, (Coq_imp (f, Coq_bot)),
          (Coq_bot_elim ((Cons (a, (Cons ((Coq_imp (a, Coq_bot)), (Cons
          ((Coq_imp ((Coq_imp (a, (Coq_imp (f, Coq_bot)))), Coq_bot)),
          Nil)))))), (Coq_imp_elim ((Cons (a, (Cons ((Coq_imp (a, Coq_bot)),
          (Cons ((Coq_imp ((Coq_imp (a, (Coq_imp (f, Coq_bot)))), Coq_bot)),
          Nil)))))), a, Coq_bot, (Coq_weaken ((Cons ((Coq_imp (a, Coq_bot)),
          (Cons ((Coq_imp ((Coq_imp (a, (Coq_imp (f, Coq_bot)))), Coq_bot)),
          Nil)))), (Coq_imp (a, Coq_bot)), a, (Coq_hypo ((Cons ((Coq_imp (a,
          Coq_bot)), (Cons ((Coq_imp ((Coq_imp (a, (Coq_imp (f, Coq_bot)))),
          Coq_bot)), Nil)))), (Coq_imp (a, Coq_bot)),
          (Obj.magic (Inl __)))))), (Coq_hypo ((Cons (a, (Cons ((Coq_imp (a,
          Coq_bot)), (Cons ((Coq_imp ((Coq_imp (a, (Coq_imp (f, Coq_bot)))),
          Coq_bot)), Nil)))))), a, (Obj.magic (Inl __)))))), (Coq_imp (f,
          Coq_bot)))))))))))))),
        (let Pair (_, p) = iH in
         let phi = fold_left CBAproof.meet l0 CBAproof.top in
         let a = CBAproof.meet y phi in
         let delta = Nil in
         let x0 = Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (y, (Coq_imp (phi,
           Coq_bot)))), Coq_bot)), f, (Coq_dneg ((Cons ((Coq_imp ((Coq_imp
           (y, (Coq_imp (phi, Coq_bot)))), Coq_bot)), Nil)), f,
           (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (phi,
           Coq_bot)))), Coq_bot)), Nil)), (Coq_imp (f, Coq_bot)), Coq_bot,
           (Coq_imp_elim ((Cons ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp
           ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))), Coq_bot)), Nil)))),
           (Coq_imp (y, (Coq_imp (phi, Coq_bot)))), Coq_bot, (Coq_weaken
           ((Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))),
           Coq_bot)), Nil)), (Coq_imp ((Coq_imp (y, (Coq_imp (phi,
           Coq_bot)))), Coq_bot)), (Coq_imp (f, Coq_bot)), (Coq_hypo ((Cons
           ((Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))), Coq_bot)),
           Nil)), (Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))),
           Coq_bot)), (Obj.magic (Inl __)))))), (Coq_imp_intro ((Cons
           ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp
           (phi, Coq_bot)))), Coq_bot)), Nil)))), y, (Coq_imp (phi,
           Coq_bot)), (Coq_imp_intro ((Cons (y, (Cons ((Coq_imp (f,
           Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (phi,
           Coq_bot)))), Coq_bot)), Nil)))))), phi, Coq_bot, (Coq_imp_elim
           ((Cons (phi, (Cons (y, (Cons ((Coq_imp (f, Coq_bot)), (Cons
           ((Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))), Coq_bot)),
           Nil)))))))), (Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)),
           Coq_bot)))), Coq_bot,
           (weaken_lem1 (Cons (phi, Nil)) (Cons (phi, (Cons (y, (Cons
             ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp
             (phi, Coq_bot)))), Coq_bot)), Nil)))))))) (Coq_imp ((Coq_imp
             (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), Coq_bot))
             (fun _ h0 ->
             match Obj.magic h0 with
             | Inl _ -> Obj.magic (Inl __)
             | Inr _ -> assert false (* absurd case *)) (Coq_imp_elim ((Cons
             (phi, Nil)), phi, (Coq_imp ((Coq_imp (phi, (Coq_imp ((Coq_imp
             (y, f)), Coq_bot)))), Coq_bot)), (Coq_weaken (Nil, (Coq_imp
             (phi, (Coq_imp ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)),
             Coq_bot)))), Coq_bot)))), phi, p)), (Coq_hypo ((Cons (phi,
             Nil)), phi, (Obj.magic (Inl __))))))),
           (Coq_imp_intro ((Cons (phi, (Cons (y, (Cons ((Coq_imp (f,
           Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (phi,
           Coq_bot)))), Coq_bot)), Nil)))))))), phi, (Coq_imp ((Coq_imp (y,
           f)), Coq_bot)), (Coq_imp_intro ((Cons (phi, (Cons (phi, (Cons (y,
           (Cons ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y,
           (Coq_imp (phi, Coq_bot)))), Coq_bot)), Nil)))))))))), (Coq_imp (y,
           f)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (y, f)), (Cons (phi,
           (Cons (phi, (Cons (y, (Cons ((Coq_imp (f, Coq_bot)), (Cons
           ((Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))), Coq_bot)),
           Nil)))))))))))), f, Coq_bot, (Coq_weaken ((Cons (phi, (Cons (phi,
           (Cons (y, (Cons ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
           (y, (Coq_imp (phi, Coq_bot)))), Coq_bot)), Nil)))))))))), (Coq_imp
           (f, Coq_bot)), (Coq_imp (y, f)), (Coq_weaken ((Cons (phi, (Cons
           (y, (Cons ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y,
           (Coq_imp (phi, Coq_bot)))), Coq_bot)), Nil)))))))), (Coq_imp (f,
           Coq_bot)), phi, (Coq_weaken ((Cons (y, (Cons ((Coq_imp (f,
           Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (phi,
           Coq_bot)))), Coq_bot)), Nil)))))), (Coq_imp (f, Coq_bot)), phi,
           (Coq_weaken ((Cons ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp
           ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))), Coq_bot)), Nil)))),
           (Coq_imp (f, Coq_bot)), y, (Coq_hypo ((Cons ((Coq_imp (f,
           Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (phi,
           Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (f, Coq_bot)),
           (Obj.magic (Inl __)))))))))))), (Coq_imp_elim ((Cons ((Coq_imp (y,
           f)), (Cons (phi, (Cons (phi, (Cons (y, (Cons ((Coq_imp (f,
           Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (phi,
           Coq_bot)))), Coq_bot)), Nil)))))))))))), y, f, (Coq_hypo ((Cons
           ((Coq_imp (y, f)), (Cons (phi, (Cons (phi, (Cons (y, (Cons
           ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp
           (phi, Coq_bot)))), Coq_bot)), Nil)))))))))))), (Coq_imp (y, f)),
           (Obj.magic (Inl __)))), (Coq_weaken ((Cons (phi, (Cons (phi, (Cons
           (y, (Cons ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y,
           (Coq_imp (phi, Coq_bot)))), Coq_bot)), Nil)))))))))), y, (Coq_imp
           (y, f)), (Coq_weaken ((Cons (phi, (Cons (y, (Cons ((Coq_imp (f,
           Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y, (Coq_imp (phi,
           Coq_bot)))), Coq_bot)), Nil)))))))), y, phi, (Coq_weaken ((Cons
           (y, (Cons ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (y,
           (Coq_imp (phi, Coq_bot)))), Coq_bot)), Nil)))))), y, phi,
           (Coq_hypo ((Cons (y, (Cons ((Coq_imp (f, Coq_bot)), (Cons
           ((Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))), Coq_bot)),
           Nil)))))), y, (Obj.magic (Inl __)))))))))))))))))))))))))))))))
         in
         Coq_imp_intro (delta, a, (Coq_imp ((Coq_imp (a, (Coq_imp (f,
         Coq_bot)))), Coq_bot)), (Coq_imp_intro ((Cons (a, delta)), (Coq_imp
         (a, (Coq_imp (f, Coq_bot)))), Coq_bot, (Coq_imp_elim ((Cons
         ((Coq_imp (a, (Coq_imp (f, Coq_bot)))), (Cons (a, delta)))), f,
         Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (a, (Coq_imp (f,
         Coq_bot)))), (Cons (a, delta)))), a, (Coq_imp (f, Coq_bot)),
         (Coq_hypo ((Cons ((Coq_imp (a, (Coq_imp (f, Coq_bot)))), (Cons (a,
         delta)))), (Coq_imp (a, (Coq_imp (f, Coq_bot)))),
         (Obj.magic (Inl __)))), (Coq_weaken ((Cons (a, delta)), a, (Coq_imp
         (a, (Coq_imp (f, Coq_bot)))), (Coq_hypo ((Cons (a, delta)), a,
         (Obj.magic (Inl __)))))))), (Coq_imp_elim ((Cons ((Coq_imp (a,
         (Coq_imp (f, Coq_bot)))), (Cons (a, delta)))), a, f, (Coq_weaken
         ((Cons (a, delta)), (Coq_imp (a, f)), (Coq_imp (a, (Coq_imp (f,
         Coq_bot)))), (Coq_weaken (delta, (Coq_imp (a, f)), a, x0)))),
         (Coq_weaken ((Cons (a, delta)), a, (Coq_imp (a, (Coq_imp (f,
         Coq_bot)))), (Coq_hypo ((Cons (a, delta)), a,
         (Obj.magic (Inl __))))))))))))))))

  (** val fold_left_proof :
      formula list -> formula -> CBAproof_completion.leq -> proof **)

  let rec fold_left_proof l f h =
    match l with
    | Nil ->
      let Pair (_, p) = h in
      Coq_dneg (Nil, f, (Coq_imp_intro (Nil, (Coq_imp (f, Coq_bot)), Coq_bot,
      (Coq_imp_elim ((Cons ((Coq_imp (f, Coq_bot)), Nil)), (Coq_imp
      (CBAproof.top, (Coq_imp (f, Coq_bot)))), Coq_bot, (Coq_imp_elim ((Cons
      ((Coq_imp (f, Coq_bot)), Nil)), CBAproof.top, (Coq_imp ((Coq_imp
      (CBAproof.top, (Coq_imp (f, Coq_bot)))), Coq_bot)), (Coq_weaken (Nil,
      (Coq_imp (CBAproof.top, (Coq_imp ((Coq_imp (CBAproof.top, (Coq_imp (f,
      Coq_bot)))), Coq_bot)))), (Coq_imp (f, Coq_bot)), p)), (Coq_imp_intro
      ((Cons ((Coq_imp (f, Coq_bot)), Nil)), Coq_bot, Coq_bot, (Coq_hypo
      ((Cons (Coq_bot, (Cons ((Coq_imp (f, Coq_bot)), Nil)))), Coq_bot,
      (Obj.magic (Inl __)))))))), (Coq_imp_intro ((Cons ((Coq_imp (f,
      Coq_bot)), Nil)), CBAproof.top, (Coq_imp (f, Coq_bot)), (Coq_weaken
      ((Cons ((Coq_imp (f, Coq_bot)), Nil)), (Coq_imp (f, Coq_bot)),
      CBAproof.top, (Coq_hypo ((Cons ((Coq_imp (f, Coq_bot)), Nil)), (Coq_imp
      (f, Coq_bot)), (Obj.magic (Inl __)))))))))))))
    | Cons (y, l0) ->
      let h' =
        CBAproof_completion.leq_trans
          (CBAproof.meet y (fold_left CBAproof.meet l0 CBAproof.top))
          (fold_left CBAproof.meet (Cons (y, l0)) CBAproof.top) f
          (CBAproof_completion.eq_B_leq
            (CBAproof.meet y (fold_left CBAproof.meet l0 CBAproof.top))
            (fold_left CBAproof.meet (Cons (y, l0)) CBAproof.top)
            (CBAproof.eq_B_symm
              (fold_left CBAproof.meet (Cons (y, l0)) CBAproof.top)
              (CBAproof.meet y (fold_left CBAproof.meet l0 CBAproof.top))
              (CBAproof_completion.fold_left_meet_cons l0 y)))
          h
      in
      let iH = fold_left_proof l0 (Coq_imp (y, f)) in
      Coq_imp_elim ((Cons (y, l0)), y, f, (Coq_weaken (l0, (Coq_imp (y, f)),
      y,
      (iH
        (let phi = fold_left CBAproof.meet l0 CBAproof.top in
         let Pair (_, p) = h' in
         Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (phi, (Coq_imp
         ((Coq_imp (y, f)), Coq_bot)))), Coq_bot)), phi, (Coq_dneg ((Cons
         ((Coq_imp ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))),
         Coq_bot)), Nil)), phi, (Coq_imp_intro ((Cons ((Coq_imp ((Coq_imp
         (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), Coq_bot)), Nil)),
         (Coq_imp (phi, Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp
         (phi, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (phi, (Coq_imp ((Coq_imp
         (y, f)), Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (phi, (Coq_imp
         ((Coq_imp (y, f)), Coq_bot)))), Coq_bot, (Coq_weaken ((Cons
         ((Coq_imp ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))),
         Coq_bot)), Nil)), (Coq_imp ((Coq_imp (phi, (Coq_imp ((Coq_imp (y,
         f)), Coq_bot)))), Coq_bot)), (Coq_imp (phi, Coq_bot)), (Coq_hypo
         ((Cons ((Coq_imp ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)),
         Coq_bot)))), Coq_bot)), Nil)), (Coq_imp ((Coq_imp (phi, (Coq_imp
         ((Coq_imp (y, f)), Coq_bot)))), Coq_bot)), (Obj.magic (Inl __)))))),
         (Coq_imp_intro ((Cons ((Coq_imp (phi, Coq_bot)), (Cons ((Coq_imp
         ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), Coq_bot)),
         Nil)))), phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)), (Coq_bot_elim
         ((Cons (phi, (Cons ((Coq_imp (phi, Coq_bot)), (Cons ((Coq_imp
         ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), Coq_bot)),
         Nil)))))), (Coq_imp_elim ((Cons (phi, (Cons ((Coq_imp (phi,
         Coq_bot)), (Cons ((Coq_imp ((Coq_imp (phi, (Coq_imp ((Coq_imp (y,
         f)), Coq_bot)))), Coq_bot)), Nil)))))), phi, Coq_bot, (Coq_weaken
         ((Cons ((Coq_imp (phi, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (phi,
         (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), Coq_bot)), Nil)))),
         (Coq_imp (phi, Coq_bot)), phi, (Coq_hypo ((Cons ((Coq_imp (phi,
         Coq_bot)), (Cons ((Coq_imp ((Coq_imp (phi, (Coq_imp ((Coq_imp (y,
         f)), Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (phi, Coq_bot)),
         (Obj.magic (Inl __)))))), (Coq_hypo ((Cons (phi, (Cons ((Coq_imp
         (phi, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (phi, (Coq_imp ((Coq_imp
         (y, f)), Coq_bot)))), Coq_bot)), Nil)))))), phi,
         (Obj.magic (Inl __)))))), (Coq_imp ((Coq_imp (y, f)),
         Coq_bot)))))))))))))), (Coq_imp_intro (Nil, phi,
         (CBAproof.meet phi (Coq_imp (y, f))), (Coq_imp_intro ((Cons (phi,
         Nil)), (Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))),
         Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y,
         f)), Coq_bot)))), (Cons (phi, Nil)))), (Coq_imp (y, f)), Coq_bot,
         (Coq_imp_elim ((Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)),
         Coq_bot)))), (Cons (phi, Nil)))), phi, (Coq_imp ((Coq_imp (y, f)),
         Coq_bot)), (Coq_hypo ((Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y,
         f)), Coq_bot)))), (Cons (phi, Nil)))), (Coq_imp (phi, (Coq_imp
         ((Coq_imp (y, f)), Coq_bot)))), (Obj.magic (Inl __)))), (Coq_weaken
         ((Cons (phi, Nil)), phi, (Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)),
         Coq_bot)))), (Coq_hypo ((Cons (phi, Nil)), phi,
         (Obj.magic (Inl __)))))))), (Coq_imp_intro ((Cons ((Coq_imp (phi,
         (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), (Cons (phi, Nil)))), y, f,
         (Coq_imp_elim ((Cons (y, (Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp
         (y, f)), Coq_bot)))), (Cons (phi, Nil)))))),
         (CBAproof.meet (CBAproof.meet y phi) f), f, (Coq_imp_intro ((Cons
         (y, (Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))),
         (Cons (phi, Nil)))))), (CBAproof.meet (CBAproof.meet y phi) f), f,
         (Coq_dneg ((Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (y,
         (Coq_imp (phi, Coq_bot)))), Coq_bot)), (Coq_imp (f, Coq_bot)))),
         Coq_bot)), (Cons (y, (Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y,
         f)), Coq_bot)))), (Cons (phi, Nil)))))))), f, (Coq_imp_intro ((Cons
         ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (phi,
         Coq_bot)))), Coq_bot)), (Coq_imp (f, Coq_bot)))), Coq_bot)), (Cons
         (y, (Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))),
         (Cons (phi, Nil)))))))), (Coq_imp (f, Coq_bot)), Coq_bot,
         (Coq_imp_elim ((Cons ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp
         ((Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))),
         Coq_bot)), (Coq_imp (f, Coq_bot)))), Coq_bot)), (Cons (y, (Cons
         ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), (Cons (phi,
         Nil)))))))))), (Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (phi,
         Coq_bot)))), Coq_bot)), (Coq_imp (f, Coq_bot)))), Coq_bot,
         (Coq_weaken ((Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (y,
         (Coq_imp (phi, Coq_bot)))), Coq_bot)), (Coq_imp (f, Coq_bot)))),
         Coq_bot)), (Cons (y, (Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y,
         f)), Coq_bot)))), (Cons (phi, Nil)))))))), (Coq_imp ((Coq_imp
         ((Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))), Coq_bot)),
         (Coq_imp (f, Coq_bot)))), Coq_bot)), (Coq_imp (f, Coq_bot)),
         (Coq_hypo ((Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (y,
         (Coq_imp (phi, Coq_bot)))), Coq_bot)), (Coq_imp (f, Coq_bot)))),
         Coq_bot)), (Cons (y, (Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y,
         f)), Coq_bot)))), (Cons (phi, Nil)))))))), (Coq_imp ((Coq_imp
         ((Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))), Coq_bot)),
         (Coq_imp (f, Coq_bot)))), Coq_bot)), (Obj.magic (Inl __)))))),
         (Coq_imp_intro ((Cons ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp
         ((Coq_imp ((Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))),
         Coq_bot)), (Coq_imp (f, Coq_bot)))), Coq_bot)), (Cons (y, (Cons
         ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), (Cons (phi,
         Nil)))))))))), (Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))),
         Coq_bot)), (Coq_imp (f, Coq_bot)), (Coq_weaken ((Cons ((Coq_imp (f,
         Coq_bot)), (Cons ((Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (y,
         (Coq_imp (phi, Coq_bot)))), Coq_bot)), (Coq_imp (f, Coq_bot)))),
         Coq_bot)), (Cons (y, (Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y,
         f)), Coq_bot)))), (Cons (phi, Nil)))))))))), (Coq_imp (f, Coq_bot)),
         (Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))), Coq_bot)),
         (Coq_hypo ((Cons ((Coq_imp (f, Coq_bot)), (Cons ((Coq_imp ((Coq_imp
         ((Coq_imp ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))), Coq_bot)),
         (Coq_imp (f, Coq_bot)))), Coq_bot)), (Cons (y, (Cons ((Coq_imp (phi,
         (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), (Cons (phi, Nil)))))))))),
         (Coq_imp (f, Coq_bot)), (Obj.magic (Inl __)))))))))))))))),
         (Coq_imp_elim ((Cons (y, (Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp
         (y, f)), Coq_bot)))), (Cons (phi, Nil)))))), (CBAproof.meet y phi),
         (CBAproof.meet (CBAproof.meet y phi) f), (Coq_weaken ((Cons
         ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), (Cons (phi,
         Nil)))), (Coq_imp ((CBAproof.meet y phi),
         (CBAproof.meet (CBAproof.meet y phi) f))), y, (Coq_weaken ((Cons
         (phi, Nil)), (Coq_imp ((CBAproof.meet y phi),
         (CBAproof.meet (CBAproof.meet y phi) f))), (Coq_imp (phi, (Coq_imp
         ((Coq_imp (y, f)), Coq_bot)))), (Coq_weaken (Nil, (Coq_imp
         ((CBAproof.meet y phi), (CBAproof.meet (CBAproof.meet y phi) f))),
         phi, p)))))), (Coq_imp_intro ((Cons (y, (Cons ((Coq_imp (phi,
         (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), (Cons (phi, Nil)))))),
         (Coq_imp (y, (Coq_imp (phi, Coq_bot)))), Coq_bot, (Coq_imp_elim
         ((Cons ((Coq_imp (y, (Coq_imp (phi, Coq_bot)))), (Cons (y, (Cons
         ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), (Cons (phi,
         Nil)))))))), phi, Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (y,
         (Coq_imp (phi, Coq_bot)))), (Cons (y, (Cons ((Coq_imp (phi, (Coq_imp
         ((Coq_imp (y, f)), Coq_bot)))), (Cons (phi, Nil)))))))), y, (Coq_imp
         (phi, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp (y, (Coq_imp (phi,
         Coq_bot)))), (Cons (y, (Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y,
         f)), Coq_bot)))), (Cons (phi, Nil)))))))), (Coq_imp (y, (Coq_imp
         (phi, Coq_bot)))), (Obj.magic (Inl __)))), (Coq_weaken ((Cons (y,
         (Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), (Cons
         (phi, Nil)))))), y, (Coq_imp (y, (Coq_imp (phi, Coq_bot)))),
         (Coq_hypo ((Cons (y, (Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y,
         f)), Coq_bot)))), (Cons (phi, Nil)))))), y,
         (Obj.magic (Inl __)))))))), (Coq_weaken ((Cons (y, (Cons ((Coq_imp
         (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), (Cons (phi,
         Nil)))))), phi, (Coq_imp (y, (Coq_imp (phi, Coq_bot)))), (Coq_weaken
         ((Cons ((Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))),
         (Cons (phi, Nil)))), phi, y, (Coq_weaken ((Cons (phi, Nil)), phi,
         (Coq_imp (phi, (Coq_imp ((Coq_imp (y, f)), Coq_bot)))), (Coq_hypo
         ((Cons (phi, Nil)), phi,
         (Obj.magic (Inl __))))))))))))))))))))))))))))))),
      (Coq_hypo ((Cons (y, l0)), y, (Obj.magic (Inl __)))))

  (** val coq_F_n_theory :
      ('a2, 'a1) theory -> nat -> (('a1, 'a2) coq_GAx, ('a1, 'a2) coq_G)
      theory **)

  let rec coq_F_n_theory ttheory = function
  | O ->
    (fun f -> Pair ((fun x -> Obj.magic x), (fun x ->
      let h2 = snd (coq_T1theory ttheory f) in Obj.magic h2 x)))
  | S n0 ->
    let iHn = coq_F_n_theory ttheory n0 in
    (fun f -> Pair ((fun h ->
    let h0 =
      let ExistT (_, s) = Obj.magic h in
      let ExistT (x, p) = s in
      let Pair (_, p0) = p in
      let Pair (f0, l) = p0 in
      let h0 = fun y yys ->
        let h0 =
          let h4 = CBAproof_completion.lemma5 x n0 f0 in
          (match h4 with
           | Inl f1 ->
             Inl
               (let rec f2 l0 yys0 case1 =
                  match l0 with
                  | Nil -> assert false (* absurd case *)
                  | Cons (_, l1) ->
                    let case2 = CBAproof_completion.lemma61 l1 case1 in
                    (match yys0 with
                     | Inl _ -> let Pair (_, b) = case2 in b
                     | Inr i ->
                       let Pair (f3, _) = case2 in Obj.magic f2 l1 i f3)
                in f2 x yys f1)
           | Inr s0 ->
             let ExistT (x0, p1) = s0 in
             let Pair (_, p2) = p1 in
             let Pair (_, p3) = p2 in
             let Pair (f1, e) = p3 in
             (match formula_dec y x0 with
              | Left -> Inr (Inr (Pair (__, e)))
              | Right ->
                Inl
                  (let ys' = remove CBAproof.id_B_dec x0 x in
                   let yys' = remove_In_neq_In x y x0 (Obj.magic yys) in
                   let rec f2 l0 hfold yys'0 =
                     match l0 with
                     | Nil -> assert false (* absurd case *)
                     | Cons (_, l1) ->
                       let hfold0 = CBAproof_completion.lemma61 l1 hfold in
                       (match Obj.magic yys'0 with
                        | Inl _ -> let Pair (_, b) = hfold0 in b
                        | Inr i -> let Pair (a, _) = hfold0 in f2 l1 a i)
                   in f2 ys' f1 yys')))
        in
        (match h0 with
         | Inl g ->
           let hth = fst (iHn y) g in
           let ExistT (x0, p1) = hth in
           let Pair (i, s0) = p1 in
           let ExistT (x1, _) = s0 in
           ExistT (x0, (Pair ((fun f1 h1 -> Inl (i f1 h1)),
           (proof_fold_left x0 y x1))))
         | Inr g ->
           ExistT ((Cons (y, Nil)), (Pair ((fun _ hr ->
             match Obj.magic hr with
             | Inl _ -> g
             | Inr _ -> assert false (* absurd case *)),
             (CBAproof_completion.eq_B_leq (CBAproof.meet CBAproof.top y) y
               (CBAproof.meet_top y))))))
      in
      let h1 =
        let rec f1 l0 h1 =
          match l0 with
          | Nil ->
            ExistT (Nil, (Pair (nil_included,
              (CBAproof_completion.leq_refl CBAproof.top))))
          | Cons (y, l1) ->
            let h2 = fun y0 x0 -> h1 y0 (Inr x0) in
            let h3 = h1 y (Inl __) in
            let iH = Obj.magic f1 l1 h2 in
            let ExistT (x0, p1) = h3 in
            let Pair (i, l2) = p1 in
            let ExistT (x1, p2) = iH in
            let Pair (i0, l3) = p2 in
            ExistT ((app x0 x1), (Pair ((included_lem1 x0 x1 i i0),
            (CBAproof_completion.leq_trans
              (fold_left CBAproof.meet (app x0 x1) CBAproof.top)
              (CBAproof.meet y (fold_left CBAproof.meet l1 CBAproof.top))
              (fold_left CBAproof.meet (Cons (y, l1)) CBAproof.top)
              (CBAproof_completion.leq_trans
                (fold_left CBAproof.meet (app x0 x1) CBAproof.top)
                (CBAproof.meet (fold_left CBAproof.meet x0 CBAproof.top)
                  (fold_left CBAproof.meet x1 CBAproof.top))
                (CBAproof.meet y (fold_left CBAproof.meet l1 CBAproof.top))
                (CBAproof_completion.eq_B_leq
                  (fold_left CBAproof.meet (app x0 x1) CBAproof.top)
                  (CBAproof.meet (fold_left CBAproof.meet x0 CBAproof.top)
                    (fold_left CBAproof.meet x1 CBAproof.top))
                  (CBAproof_completion.fold_left_app_lem x0 x1))
                (CBAproof_completion.meet_leq_compat
                  (fold_left CBAproof.meet x0 CBAproof.top) y
                  (fold_left CBAproof.meet x1 CBAproof.top)
                  (fold_left CBAproof.meet l1 CBAproof.top) l2 l3))
              (CBAproof_completion.eq_B_leq
                (CBAproof.meet y (fold_left CBAproof.meet l1 CBAproof.top))
                (fold_left CBAproof.meet (Cons (y, l1)) CBAproof.top)
                (CBAproof.eq_B_symm
                  (fold_left CBAproof.meet (Cons (y, l1)) CBAproof.top)
                  (CBAproof.meet y (fold_left CBAproof.meet l1 CBAproof.top))
                  (CBAproof_completion.fold_left_meet_cons l1 y)))))))
        in f1 x h0
      in
      let ExistT (x0, p1) = h1 in
      let Pair (i, l0) = p1 in
      ExistT (x0, (Pair (i,
      (CBAproof_completion.leq_trans
        (fold_left CBAproof.meet x0 CBAproof.top)
        (fold_left CBAproof.meet x CBAproof.top) f l0 l))))
    in
    let ExistT (x, p) = h0 in
    let Pair (i, l) = p in
    ExistT (x, (Pair ((Obj.magic i),
    (let p0 = fold_left_proof x f l in ExistT (p0, Tt)))))), (fun h ->
    let ExistT (x, p) = h in
    let Pair (i, s) = p in
    let ExistT (x0, _) = s in
    Obj.magic (ExistT ((length x), (ExistT (x, (Pair (__, (Pair
      ((let rec f0 l h01 =
          match l with
          | Nil -> Obj.magic Tt
          | Cons (y, l0) ->
            CBAproof_completion.lemma62 l0 (Pair
              ((f0 l0 (fun f1 h0 -> Obj.magic h01 f1 (Inr h0))),
              (let s0 = Obj.magic h01 y (Inl __) in
               match s0 with
               | Inl g ->
                 Inl
                   (snd (Obj.magic iHn y) (ExistT ((Cons (y, Nil)), (Pair
                     ((fun _ x1 ->
                     match x1 with
                     | Inl _ -> g
                     | Inr _ -> assert false (* absurd case *)),
                     (let p0 = Coq_hypo ((Cons (y, Nil)), y,
                        (Obj.magic (Inl __)))
                      in
                      ExistT (p0, Tt)))))))
               | Inr p0 -> Inr p0)))
        in f0 x i),
      (proof_fold_left x f x0))))))))))))

  (** val coq_Z'theory :
      ('a2, 'a1) theory -> (('a1, 'a2) coq_ZAx, ('a1, 'a2) coq_Z') theory **)

  let coq_Z'theory ttheory f =
    Pair ((fun h0 ->
      let ExistT (x, f0) = h0 in
      let h1 = fst (coq_F_n_theory ttheory x f) in
      let h3 = h1 f0 in
      let ExistT (x0, p) = h3 in
      let Pair (i, s) = p in
      ExistT (x0, (Pair ((fun f1 x1 -> ExistT (x, (i f1 x1))), s)))),
      (fun h ->
      let ExistT (x, p) = h in
      let Pair (i, s) = p in
      let ExistT (x0, _) = s in
      let h0 =
        let rec f0 l h1 =
          match l with
          | Nil -> ExistT (O, (fun _ _ -> assert false (* absurd case *)))
          | Cons (y, l0) ->
            let h0 = fun f1 x1 -> Obj.magic h1 f1 (Inr x1) in
            let iH = f0 l0 h0 in
            let ExistT (x1, g) = iH in
            let h1' = h1 y in
            let h2 = Obj.magic h1' (Inl __) in
            let ExistT (x2, g0) = h2 in
            let s0 = CBAproof_completion.le_lt_dec x2 x1 in
            (match s0 with
             | Inl l1 ->
               let h3 = coq_GAx_monotone x2 x1 l1 in
               ExistT (x1, (fun f1 h4 ->
               match h4 with
               | Inl _ -> h3 y g0
               | Inr b -> Obj.magic g f1 b))
             | Inr l1 ->
               let h3 = CBAproof_completion.lt_le_incl x1 x2 l1 in
               let h4 = coq_GAx_monotone x1 x2 h3 in
               ExistT (x2, (fun f1 h5 ->
               match h5 with
               | Inl _ -> g0
               | Inr b -> h4 f1 (Obj.magic g f1 b))))
        in f0 x i
      in
      let ExistT (x1, i0) = h0 in
      ExistT (x1,
      (let h3 = snd (coq_F_n_theory ttheory x1 f) in
       Obj.magic h3 (ExistT (x, (Pair (i0, (ExistT (x0, Tt))))))))))

  type 'x metaDN = formula -> ('x -> 'x) -> 'x

  (** val metaDNZ' : ('a2, 'a1) theory -> ('a1, 'a2) coq_Z' metaDN **)

  let metaDNZ' ttheory =
    let p = lem15 ttheory in
    (fun f x ->
    let Pair (_, p0) = p in
    let Pair (_, c) = p0 in
    c f (Pair ((fun h ->
      CBAproof_completion.lem223 CBAproof.bott (Inleft h)), (fun h ->
      x
        (let ExistT (_, s) = h in
         let ExistT (x0, p1) = s in
         let Pair (_, p2) = p1 in
         let Pair (f0, l) = p2 in
         let h6 = CBAproof_completion.lemma8 f x0 f0 in
         (match h6 with
          | Inl f1 ->
            let h0 = CBAproof_completion.leq_bott (Coq_imp (f, Coq_bot)) in
            CBAproof_completion.upwards_closed (fst (lem15 ttheory))
              CBAproof.bott (Coq_imp (f, Coq_bot))
              (CBAproof_completion.upwards_closed (fst (lem15 ttheory))
                (fold_left CBAproof.meet x0 CBAproof.top) CBAproof.bott
                (CBAproof_completion.lemma4 x0 (fst (lem15 ttheory)) f1) l)
              h0
          | Inr f1 ->
            let z' = remove CBAproof.id_B_dec f x0 in
            let z = fold_left CBAproof.meet z' CBAproof.top in
            let h0 =
              CBAproof_completion.leq_trans (CBAproof.meet f z)
                (fold_left CBAproof.meet x0 CBAproof.top) CBAproof.bott
                (CBAproof_completion.leq_trans (CBAproof.meet f z)
                  (fold_left CBAproof.meet (Cons (f, z')) CBAproof.top)
                  (fold_left CBAproof.meet x0 CBAproof.top)
                  (CBAproof_completion.eq_B_leq (CBAproof.meet f z)
                    (fold_left CBAproof.meet (Cons (f, z')) CBAproof.top)
                    (CBAproof.eq_B_symm
                      (fold_left CBAproof.meet z'
                        (CBAproof.meet CBAproof.top f))
                      (CBAproof.meet f z)
                      (CBAproof_completion.fold_left_meet_cons z' f)))
                  (CBAproof_completion.lemma2 x0 (Cons (f, z'))
                    (CBAproof_completion.lemma3 CBAproof.id_B_dec f x0)))
                l
            in
            let h1 =
              let Pair (_, p3) = h0 in
              Pair ((Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (z, (Coq_imp
              ((Coq_imp (f, Coq_bot)), Coq_bot)))), Coq_bot)), z, (Coq_dneg
              ((Cons ((Coq_imp ((Coq_imp (z, (Coq_imp ((Coq_imp (f,
              Coq_bot)), Coq_bot)))), Coq_bot)), Nil)), z, (Coq_imp_intro
              ((Cons ((Coq_imp ((Coq_imp (z, (Coq_imp ((Coq_imp (f,
              Coq_bot)), Coq_bot)))), Coq_bot)), Nil)), (Coq_imp (z,
              Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (z,
              Coq_bot)), (Cons ((Coq_imp ((Coq_imp (z, (Coq_imp ((Coq_imp (f,
              Coq_bot)), Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (z,
              (Coq_imp ((Coq_imp (f, Coq_bot)), Coq_bot)))), Coq_bot,
              (Coq_weaken ((Cons ((Coq_imp ((Coq_imp (z, (Coq_imp ((Coq_imp
              (f, Coq_bot)), Coq_bot)))), Coq_bot)), Nil)), (Coq_imp
              ((Coq_imp (z, (Coq_imp ((Coq_imp (f, Coq_bot)), Coq_bot)))),
              Coq_bot)), (Coq_imp (z, Coq_bot)), (Coq_hypo ((Cons ((Coq_imp
              ((Coq_imp (z, (Coq_imp ((Coq_imp (f, Coq_bot)), Coq_bot)))),
              Coq_bot)), Nil)), (Coq_imp ((Coq_imp (z, (Coq_imp ((Coq_imp (f,
              Coq_bot)), Coq_bot)))), Coq_bot)), (Obj.magic (Inl __)))))),
              (Coq_imp_intro ((Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
              ((Coq_imp (z, (Coq_imp ((Coq_imp (f, Coq_bot)), Coq_bot)))),
              Coq_bot)), Nil)))), z, (Coq_imp ((Coq_imp (f, Coq_bot)),
              Coq_bot)), (Coq_bot_elim ((Cons (z, (Cons ((Coq_imp (z,
              Coq_bot)), (Cons ((Coq_imp ((Coq_imp (z, (Coq_imp ((Coq_imp (f,
              Coq_bot)), Coq_bot)))), Coq_bot)), Nil)))))), (Coq_imp_elim
              ((Cons (z, (Cons ((Coq_imp (z, Coq_bot)), (Cons ((Coq_imp
              ((Coq_imp (z, (Coq_imp ((Coq_imp (f, Coq_bot)), Coq_bot)))),
              Coq_bot)), Nil)))))), z, Coq_bot, (Coq_weaken ((Cons ((Coq_imp
              (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (z, (Coq_imp ((Coq_imp
              (f, Coq_bot)), Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (z,
              Coq_bot)), z, (Coq_hypo ((Cons ((Coq_imp (z, Coq_bot)), (Cons
              ((Coq_imp ((Coq_imp (z, (Coq_imp ((Coq_imp (f, Coq_bot)),
              Coq_bot)))), Coq_bot)), Nil)))), (Coq_imp (z, Coq_bot)),
              (Obj.magic (Inl __)))))), (Coq_hypo ((Cons (z, (Cons ((Coq_imp
              (z, Coq_bot)), (Cons ((Coq_imp ((Coq_imp (z, (Coq_imp ((Coq_imp
              (f, Coq_bot)), Coq_bot)))), Coq_bot)), Nil)))))), z,
              (Obj.magic (Inl __)))))), (Coq_imp ((Coq_imp (f, Coq_bot)),
              Coq_bot)))))))))))))), (Coq_imp_intro (Nil, z, (Coq_imp
              ((Coq_imp (z, (Coq_imp ((Coq_imp (f, Coq_bot)), Coq_bot)))),
              Coq_bot)), (Coq_imp_intro ((Cons (z, Nil)), (Coq_imp (z,
              (Coq_imp ((Coq_imp (f, Coq_bot)), Coq_bot)))), Coq_bot,
              (Coq_imp_elim ((Cons ((Coq_imp (z, (Coq_imp ((Coq_imp (f,
              Coq_bot)), Coq_bot)))), (Cons (z, Nil)))), (Coq_imp (f,
              Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (z, (Coq_imp
              ((Coq_imp (f, Coq_bot)), Coq_bot)))), (Cons (z, Nil)))), z,
              (Coq_imp ((Coq_imp (f, Coq_bot)), Coq_bot)), (Coq_hypo ((Cons
              ((Coq_imp (z, (Coq_imp ((Coq_imp (f, Coq_bot)), Coq_bot)))),
              (Cons (z, Nil)))), (Coq_imp (z, (Coq_imp ((Coq_imp (f,
              Coq_bot)), Coq_bot)))), (Obj.magic (Inl __)))), (Coq_weaken
              ((Cons (z, Nil)), z, (Coq_imp (z, (Coq_imp ((Coq_imp (f,
              Coq_bot)), Coq_bot)))), (Coq_hypo ((Cons (z, Nil)), z,
              (Obj.magic (Inl __)))))))), (Coq_weaken ((Cons (z, Nil)),
              (Coq_imp (f, Coq_bot)), (Coq_imp (z, (Coq_imp ((Coq_imp (f,
              Coq_bot)), Coq_bot)))), (Coq_imp_intro ((Cons (z, Nil)), f,
              Coq_bot, (Coq_imp_elim ((Cons (f, (Cons (z, Nil)))), (Coq_imp
              ((Coq_imp ((Coq_imp (f, (Coq_imp (z, Coq_bot)))), Coq_bot)),
              (Coq_imp (CBAproof.bott, Coq_bot)))), Coq_bot, (Coq_imp_elim
              ((Cons (f, (Cons (z, Nil)))), (Coq_imp ((Coq_imp (f, (Coq_imp
              (z, Coq_bot)))), Coq_bot)), (Coq_imp ((Coq_imp ((Coq_imp
              ((Coq_imp (f, (Coq_imp (z, Coq_bot)))), Coq_bot)), (Coq_imp
              (CBAproof.bott, Coq_bot)))), Coq_bot)), (Coq_weaken ((Cons (z,
              Nil)), (Coq_imp ((Coq_imp ((Coq_imp (f, (Coq_imp (z,
              Coq_bot)))), Coq_bot)), (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp
              (f, (Coq_imp (z, Coq_bot)))), Coq_bot)), (Coq_imp
              (CBAproof.bott, Coq_bot)))), Coq_bot)))), f, (Coq_weaken (Nil,
              (Coq_imp ((Coq_imp ((Coq_imp (f, (Coq_imp (z, Coq_bot)))),
              Coq_bot)), (Coq_imp ((Coq_imp ((Coq_imp ((Coq_imp (f, (Coq_imp
              (z, Coq_bot)))), Coq_bot)), (Coq_imp (CBAproof.bott,
              Coq_bot)))), Coq_bot)))), z, p3)))), (Coq_imp_intro ((Cons (f,
              (Cons (z, Nil)))), (Coq_imp (f, (Coq_imp (z, Coq_bot)))),
              Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (f, (Coq_imp (z,
              Coq_bot)))), (Cons (f, (Cons (z, Nil)))))), z, Coq_bot,
              (Coq_imp_elim ((Cons ((Coq_imp (f, (Coq_imp (z, Coq_bot)))),
              (Cons (f, (Cons (z, Nil)))))), f, (Coq_imp (z, Coq_bot)),
              (Coq_hypo ((Cons ((Coq_imp (f, (Coq_imp (z, Coq_bot)))), (Cons
              (f, (Cons (z, Nil)))))), (Coq_imp (f, (Coq_imp (z, Coq_bot)))),
              (Obj.magic (Inl __)))), (Coq_weaken ((Cons (f, (Cons (z,
              Nil)))), f, (Coq_imp (f, (Coq_imp (z, Coq_bot)))), (Coq_hypo
              ((Cons (f, (Cons (z, Nil)))), f, (Obj.magic (Inl __)))))))),
              (Coq_weaken ((Cons (f, (Cons (z, Nil)))), z, (Coq_imp (f,
              (Coq_imp (z, Coq_bot)))), (Coq_weaken ((Cons (z, Nil)), z, f,
              (Coq_hypo ((Cons (z, Nil)), z,
              (Obj.magic (Inl __)))))))))))))), (Coq_imp_intro ((Cons (f,
              (Cons (z, Nil)))), (Coq_imp ((Coq_imp (f, (Coq_imp (z,
              Coq_bot)))), Coq_bot)), (Coq_imp (CBAproof.bott, Coq_bot)),
              (Coq_weaken ((Cons (f, (Cons (z, Nil)))), (Coq_imp
              (CBAproof.bott, Coq_bot)), (Coq_imp ((Coq_imp (f, (Coq_imp (z,
              Coq_bot)))), Coq_bot)), (Coq_weaken ((Cons (z, Nil)), (Coq_imp
              (CBAproof.bott, Coq_bot)), f, (Coq_weaken (Nil, (Coq_imp
              (CBAproof.bott, Coq_bot)), z, (Coq_imp_intro (Nil,
              CBAproof.bott, Coq_bot, (Coq_hypo ((Cons (CBAproof.bott, Nil)),
              Coq_bot, (Obj.magic (Inl __)))))))))))))))))))))))))))
            in
            CBAproof_completion.upwards_closed (fst (lem15 ttheory)) z
              (Coq_imp (f, Coq_bot))
              (CBAproof_completion.lemma4 z' (fst (lem15 ttheory)) f1) h1))))))

  (** val model_existence2 :
      ('a2, 'a1) theory -> (formula -> formula -> ('a1, 'a2) coq_Z' -> ('a1,
      'a2) coq_Z' -> ('a1, 'a2) coq_Z', formula -> formula -> (('a1, 'a2)
      coq_Z' -> ('a1, 'a2) coq_Z') -> ('a1, 'a2) coq_Z') prod **)

  let model_existence2 ttheory =
    let dir1 = fun a b0 x x0 ->
      snd (coq_Z'theory ttheory b0)
        (let h1' = fst (coq_Z'theory ttheory (Coq_imp (a, b0))) x in
         let h2' = fst (coq_Z'theory ttheory a) x0 in
         let ExistT (x1, p) = h1' in
         let Pair (i, s) = p in
         let ExistT (x2, p0) = h2' in
         let Pair (i0, s0) = p0 in
         ExistT ((app x1 x2), (Pair ((fun f x3 ->
         let s1 = in_app_or x1 x2 f x3 in
         (match s1 with
          | Inl i1 -> i f i1
          | Inr i1 -> i0 f i1)),
         (let h =
            let ExistT (x3, _) = s in
            let ExistT (x4, _) = s0 in
            Coq_imp_elim ((app x1 x2), a, b0,
            (weaken_lem1 x1 (app x1 x2) (Coq_imp (a, b0))
              (incl_appl x1 x2 x1 (incl_refl x1)) x3),
            (weaken_lem1 x2 (app x1 x2) a (incl_appr x2 x1 x2 (incl_refl x2))
              x4))
          in
          ExistT (h, Tt))))))
    in
    Pair (dir1, (fun a b x ->
    metaDNZ' ttheory (Coq_imp (a, b)) (fun h0 ->
      dir1 b Coq_bot
        (let h2' =
           fst (coq_Z'theory ttheory (Coq_imp ((Coq_imp (a, b)), Coq_bot))) h0
         in
         let ExistT (x0, p) = h2' in
         let Pair (i, s) = p in
         let ExistT (x1, _) = s in
         let h1 = Coq_imp_intro (x0, b, Coq_bot, (Coq_imp_elim ((Cons (b,
           x0)), (Coq_imp (a, b)), Coq_bot, (Coq_weaken (x0, (Coq_imp
           ((Coq_imp (a, b)), Coq_bot)), b, x1)), (Coq_imp_intro ((Cons (b,
           x0)), a, b, (Coq_weaken ((Cons (b, x0)), b, a, (Coq_hypo ((Cons
           (b, x0)), b, (Obj.magic (Inl __)))))))))))
         in
         snd (coq_Z'theory ttheory (Coq_imp (b, Coq_bot))) (ExistT (x0, (Pair
           (i, (ExistT (h1, Tt)))))))
        (x
          (let h2' =
             fst (coq_Z'theory ttheory (Coq_imp ((Coq_imp (a, b)), Coq_bot)))
               h0
           in
           let ExistT (x0, p) = h2' in
           let Pair (i, s) = p in
           let ExistT (x1, _) = s in
           let h1 = Coq_dneg (x0, a, (Coq_imp_intro (x0, (Coq_imp (a,
             Coq_bot)), Coq_bot, (Coq_imp_elim ((Cons ((Coq_imp (a,
             Coq_bot)), x0)), (Coq_imp (a, b)), Coq_bot, (Coq_weaken (x0,
             (Coq_imp ((Coq_imp (a, b)), Coq_bot)), (Coq_imp (a, Coq_bot)),
             x1)), (Coq_imp_intro ((Cons ((Coq_imp (a, Coq_bot)), x0)), a, b,
             (Coq_bot_elim ((Cons (a, (Cons ((Coq_imp (a, Coq_bot)), x0)))),
             (Coq_imp_elim ((Cons (a, (Cons ((Coq_imp (a, Coq_bot)), x0)))),
             a, Coq_bot, (Coq_weaken ((Cons ((Coq_imp (a, Coq_bot)), x0)),
             (Coq_imp (a, Coq_bot)), a, (Coq_hypo ((Cons ((Coq_imp (a,
             Coq_bot)), x0)), (Coq_imp (a, Coq_bot)),
             (Obj.magic (Inl __)))))), (Coq_hypo ((Cons (a, (Cons ((Coq_imp
             (a, Coq_bot)), x0)))), a, (Obj.magic (Inl __)))))), b)))))))))
           in
           snd (coq_Z'theory ttheory a) (ExistT (x0, (Pair (i, (ExistT (h1,
             Tt)))))))))))

  (** val model_existence3' : formula -> ('a1, 'a2) coq_Z' **)

  let model_existence3' f =
    let h1 = ExistT ((Cons ((Coq_imp
      ((coq_open f (Coq_cnst (Coq_added (Coq_all f)))), (Coq_all f))), Nil)),
      (Pair ((fun _ x -> Inr
      (match x with
       | Inl _ -> ExistT (f, __)
       | Inr _ -> assert false (* absurd case *))),
      (let p = Coq_hypo ((Cons ((Coq_imp
         ((coq_open f (Coq_cnst (Coq_added (Coq_all f)))), (Coq_all f))),
         Nil)), (Coq_imp ((coq_open f (Coq_cnst (Coq_added (Coq_all f)))),
         (Coq_all f))), (Obj.magic (Inl __)))
       in
       ExistT (p, Tt)))))
    in
    ExistT (O, (Obj.magic h1))

  (** val model_existence3 :
      ('a2, 'a1) theory -> (formula -> ('a1, 'a2) coq_Z' -> term -> ('a1,
      'a2) coq_Z', formula -> __ -> __ -> (term -> __ -> ('a1, 'a2) coq_Z')
      -> ('a1, 'a2) coq_Z') prod **)

  let model_existence3 ttheory =
    let z'imp = fst (model_existence2 ttheory) in
    Pair ((fun a x t ->
    snd (coq_Z'theory ttheory (coq_open a t))
      (let h0' = fst (coq_Z'theory ttheory (Coq_all a)) x in
       let ExistT (x0, p) = h0' in
       let Pair (i, s) = p in
       let ExistT (x1, _) = s in
       let h = Coq_all_elim (x0, a, x1, t) in
       ExistT (x0, (Pair (i, (ExistT (h, Tt))))))),
    (fun a _ _ x ->
    z'imp (coq_open a (Coq_cnst (Coq_added (Coq_all a)))) (Coq_all a)
      (model_existence3' a) (x (Coq_cnst (Coq_added (Coq_all a))) __)))

  (** val model_existence :
      ('a2, 'a1) theory -> ((('a1, 'a2) coq_Z', 'a1) extension, (('a1, 'a2)
      coq_Z' model, ('a1, ('a1, 'a2) coq_Z') equicons) prod) prod **)

  let model_existence ttheory =
    let h1 = model_existence1 ttheory in
    let Pair (a, b) = h1 in
    Pair (a, (Pair ({ model_dneg = (fun a0 ->
    snd
      (coq_Z'theory ttheory (Coq_imp ((Coq_imp ((Coq_imp (a0, Coq_bot)),
        Coq_bot)), a0)))
      (ExistT (Nil, (Pair (nil_included,
      (let h = Coq_imp_intro (Nil, (Coq_imp ((Coq_imp (a0, Coq_bot)),
         Coq_bot)), a0, (Coq_dneg ((Cons ((Coq_imp ((Coq_imp (a0, Coq_bot)),
         Coq_bot)), Nil)), a0, (Coq_hypo ((Cons ((Coq_imp ((Coq_imp (a0,
         Coq_bot)), Coq_bot)), Nil)), (Coq_imp ((Coq_imp (a0, Coq_bot)),
         Coq_bot)), (Obj.magic (Inl __)))))))
       in
       ExistT (h, Tt)))))));
    model_imp_faithful1 = (fst (model_existence2 ttheory));
    model_imp_faithful2 = (snd (model_existence2 ttheory));
    model_all_faithful1 = (fst (model_existence3 ttheory));
    model_all_faithful2 = (snd (model_existence3 ttheory)) }, b)))

  (** val completeness : formula list -> formula -> valid -> proof **)

  let completeness gamma a h =
    let ttheory = fun _ -> Pair ((fun h0 -> h0), (fun h0 -> h0)) in
    let h1 = model_existence ttheory in
    let Pair (e, p) = h1 in
    let Pair (m, e0) = p in
    Coq_dneg (gamma, a, (Coq_imp_intro (gamma, (Coq_imp (a, Coq_bot)),
    Coq_bot,
    (let h0 =
       let h0 =
         m.model_imp_faithful1 a Coq_bot
           (let h0 = ExistT ((Cons ((Coq_imp (a, Coq_bot)), Nil)), (Pair
              ((fun _ _ -> Inr __),
              (let h0 = Coq_hypo ((Cons ((Coq_imp (a, Coq_bot)), Nil)),
                 (Coq_imp (a, Coq_bot)), (Obj.magic (Inl __)))
               in
               ExistT (h0, Tt)))))
            in
            e (Coq_imp (a, Coq_bot)) h0)
           (Obj.magic h __ m (fun f x ->
             let h2 = ExistT (gamma, (Pair ((fun _ h2 -> Inl h2),
               (let h2 = Coq_hypo (gamma, f, x) in ExistT (h2, Tt)))))
             in
             e f h2))
       in
       let Pair (_, b) = e0 in b h0
     in
     let ExistT (x, p0) = h0 in
     let Pair (i, s) = p0 in
     let ExistT (x0, _) = s in
     weaken_lem1 x (Cons ((Coq_imp (a, Coq_bot)), gamma)) Coq_bot
       (fun a0 x1 ->
       match i a0 x1 with
       | Inl i0 -> Obj.magic (Inr i0)
       | Inr _ -> Obj.magic (Inl __)) x0))))
 end
