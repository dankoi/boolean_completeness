
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

type 'a in0 = __

type 'a incl = 'a -> 'a in0 -> 'a in0

(** val in_eq : 'a1 -> 'a1 list -> 'a1 in0 **)

let in_eq _ _ =
  Obj.magic (Inl __)

(** val in_cons : 'a1 -> 'a1 -> 'a1 list -> 'a1 in0 -> 'a1 in0 **)

let in_cons _ _ _ h =
  Obj.magic (Inr h)

(** val incl_tran :
    'a1 list -> 'a1 list -> 'a1 list -> 'a1 incl -> 'a1 incl -> 'a1 incl **)

let incl_tran _ _ _ h h0 a h1 =
  h0 a (h a h1)

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
 end
