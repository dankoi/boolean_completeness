
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

module Coq_filter_completion =
 functor (Coq_cba:CBA) ->
 struct
  type 'f coq_Filter = { nonempty : (Coq_cba.coq_B, 'f) sigT;
                         upwards_closed : (Coq_cba.coq_B -> Coq_cba.coq_B ->
                                          'f -> __ -> 'f);
                         meet_closed : (Coq_cba.coq_B -> Coq_cba.coq_B -> 'f
                                       -> 'f -> 'f) }

  (** val nonempty : 'a1 coq_Filter -> (Coq_cba.coq_B, 'a1) sigT **)

  let nonempty f =
    f.nonempty

  (** val upwards_closed :
      'a1 coq_Filter -> Coq_cba.coq_B -> Coq_cba.coq_B -> 'a1 -> 'a1 **)

  let upwards_closed f x y x0 =
    f.upwards_closed x y x0 __

  (** val meet_closed :
      'a1 coq_Filter -> Coq_cba.coq_B -> Coq_cba.coq_B -> 'a1 -> 'a1 -> 'a1 **)

  let meet_closed f =
    f.meet_closed

  type 'x up = (nat, (Coq_cba.coq_B list, (__, (__, __) prod) prod) sigT) sigT

  type 'f union_singl = 'f sumor

  type 'f inconsistent = 'f

  type ('f, 'g) equiconsistent =
    ('f inconsistent -> 'g inconsistent, 'g inconsistent -> 'f inconsistent)
    prod

  type 'f element_complete = ('f, 'f union_singl up) equiconsistent -> 'f

  type 'f complete = Coq_cba.coq_B -> 'f element_complete

  (** val fold_left_impl : Coq_cba.coq_B list -> ('a2 -> 'a3) -> __ -> __ **)

  let rec fold_left_impl l h =
    match l with
    | Nil -> Obj.magic h
    | Cons (_, l0) ->
      (fun x ->
        Obj.magic fold_left_impl l0 (fun h1 ->
          let Pair (a, b) = h1 in let h2 = h a in Pair (h2, b)) x)

  (** val up_filter : 'a1 up coq_Filter **)

  let up_filter =
    { nonempty = (ExistT (Coq_cba.top, (ExistT (O, (ExistT (Nil, (Pair (__,
      (Pair ((Obj.magic Tt), __)))))))))); upwards_closed = (fun _ _ x _ ->
      let ExistT (x0, s) = x in
      let ExistT (x1, p) = s in
      let Pair (_, p0) = p in
      let Pair (f, _) = p0 in
      ExistT (x0, (ExistT (x1, (Pair (__, (Pair (f, __)))))))); meet_closed =
      (fun _ _ x x0 ->
      let ExistT (x1, s) = x in
      let ExistT (x2, p) = s in
      let Pair (_, p0) = p in
      let Pair (f, _) = p0 in
      let ExistT (x3, s0) = x0 in
      let ExistT (x4, p1) = s0 in
      let Pair (_, p2) = p1 in
      let Pair (f0, _) = p2 in
      ExistT ((add x1 x3), (ExistT ((app x2 x4), (Pair (__, (Pair
      ((fold_left_impl x4 (fun _ -> f) f0), __)))))))) }

  (** val filter_top : 'a1 coq_Filter -> 'a1 **)

  let filter_top x =
    let s = x.nonempty in
    let ExistT (x0, f) = s in upwards_closed x x0 Coq_cba.top f

  (** val filter_memb_morph :
      'a1 coq_Filter -> Coq_cba.coq_B -> Coq_cba.coq_B -> 'a1 -> 'a1 **)

  let filter_memb_morph =
    upwards_closed

  (** val lemma4 : Coq_cba.coq_B list -> 'a1 coq_Filter -> __ -> 'a1 **)

  let rec lemma4 xs x x0 =
    match xs with
    | Nil -> filter_top x
    | Cons (y, l) ->
      let iHxs = fun x1 -> lemma4 l x x1 in
      filter_memb_morph x
        (Coq_cba.meet y (fold_left Coq_cba.meet l Coq_cba.top))
        (fold_left Coq_cba.meet (Cons (y, l)) Coq_cba.top)
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
                 upwards_closed x
                   (Coq_cba.meet y0 (fold_left Coq_cba.meet l1 Coq_cba.top))
                   (fold_left Coq_cba.meet l1 Coq_cba.top)
                   (filter_memb_morph x
                     (fold_left Coq_cba.meet (Cons (y0, l1)) Coq_cba.top)
                     (Coq_cba.meet y0 (fold_left Coq_cba.meet l1 Coq_cba.top))
                     (iHxs0 (fold_left_impl (Cons (y0, l1)) (fun _ -> Tt) h0))))
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
      Coq_cba.coq_B list -> nat -> __ -> (__, (Coq_cba.coq_B, (__, (__, (__,
      ('a1, 'a1 union_singl up) equiconsistent) prod) prod) prod) sigT) sum **)

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
            Inr (ExistT (y, (Pair (__, (Pair (__, (Pair
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
         let Pair (_, p0) = p in
         let Pair (_, p1) = p0 in
         let Pair (f0, e) = p1 in
         (match s with
          | Inl x0 ->
            Inr (ExistT (x, (Pair (__, (Pair (__, (Pair
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
            Inr (ExistT (y, (Pair (__, (Pair (__,
              (let s1 = Coq_cba.id_B_dec y y in
               match s1 with
               | Left -> Pair (f0, e)
               | Right -> assert false (* absurd case *))))))))))

  type 'f coq_F_ = __

  type 'f coq_Z = (nat, 'f coq_F_) sigT

  (** val lem223 : Coq_cba.coq_B -> 'a2 -> 'a2 up **)

  let lem223 x x0 =
    ExistT ((S O), (ExistT ((Cons (x, Nil)), (Pair (__, (Pair
      ((Obj.magic (Pair (Tt, x0))), __)))))))

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
    upwards_closed = (fun x0 y x1 _ ->
    let ExistT (x2, f) = x1 in
    ExistT (x2, (upwards_closed (Obj.magic lem221 x2) x0 y f)));
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
         let Pair (f0, _) = p0 in
         let Pair (i, _) = iHn in
         Obj.magic i
           (let caseAnalysis = lemma5 x0 n1 f0 in
            match caseAnalysis with
            | Inl f1 ->
              upwards_closed (lem221 n1)
                (fold_left Coq_cba.meet x0 Coq_cba.top) Coq_cba.bott
                (lemma4 x0 (fn_filter n1) f1)
            | Inr s0 ->
              let ExistT (x1, p1) = s0 in
              let Pair (_, p2) = p1 in
              let Pair (_, p3) = p2 in
              let Pair (f1, e) = p3 in
              let y = remove Coq_cba.id_B_dec x1 x0 in
              let a2 = lemma4 y (lem221 n1) f1 in
              let a3 =
                upwards_closed (lem221 n1)
                  (fold_left Coq_cba.meet y Coq_cba.top) (Coq_cba.compl x1) a2
              in
              let Pair (_, i0) = e in
              i0
                (let a4 = lem223 (Coq_cba.compl x1) (Inleft a3) in
                 let a5 = lem223 x1 Inright in
                 filter_memb_morph up_filter
                   (Coq_cba.meet x1 (Coq_cba.compl x1)) Coq_cba.bott
                   (up_filter.meet_closed x1 (Coq_cba.compl x1) a5 a4)))),
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
        let Pair (f, _) = p0 in
        ExistT (x2, (ExistT (x3, (Pair (__, (Pair
        ((let rec f0 l h2 =
            match l with
            | Nil -> h2
            | Cons (y, l0) ->
              let h2' = lemma61 l0 h2 in
              lemma62 l0 (Pair ((f0 l0 (let Pair (a, _) = h2' in a)),
                (x0 y (let Pair (_, b) = h2' in b))))
          in f0 x3 f),
        __)))))))
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
          let Pair (a, _) = b0 in
          let h = fun x4 x5 -> b (ExistT (x4, x5)) in
          let h3 = h x2 in
          let h4 = fun x4 x5 -> h3 (ExistT (x4, x5)) in
          let h5 = h4 x3 in let x4 = Pair (a, __) in h5 (Pair (__, x4))
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
 end

type 'a in0 = __

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

(** val included_lem1 :
    'a1 list -> 'a1 list -> ('a1, 'a2) included -> ('a1, 'a2) included ->
    ('a1, 'a2) included **)

let included_lem1 l1 l2 x x0 f x1 =
  let s = in_app_or l1 l2 f x1 in
  (match s with
   | Inl i -> x f i
   | Inr i -> x0 f i)

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

  type 'm model = { model_dneg : (formula -> 'm);
                    model_imp_faithful1 : (formula -> formula -> 'm -> 'm ->
                                          'm);
                    model_imp_faithful2 : (formula -> formula -> ('m -> 'm)
                                          -> 'm);
                    model_all_faithful1 : (formula -> 'm -> term -> 'm);
                    model_all_faithful2 : (formula -> __ -> __ -> (term -> __
                                          -> 'm) -> 'm) }

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

    (** val id_B_dec : formula -> formula -> sumbool **)

    let id_B_dec =
      formula_dec

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

    (** val bott : formula **)

    let bott =
      Coq_bot

    type coq_B = formula
   end

  module CBAproof_completion = Coq_filter_completion(CBAproof)

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

  (** val henkin_equiconsistent :
      ('a1, 'a2) theory -> ('a2, 'a1) coq_TH -> 'a2 **)

  let henkin_equiconsistent h1 = function
  | ExistT (x, p) ->
    let Pair (i, _) = p in
    let lemma3 = fun eta x0 ->
      let rec f l h =
        match l with
        | Nil ->
          ExistT (Nil, (ExistT (Nil, (Pair ((fun _ h0 -> h0), (Pair (__,
            (Obj.magic nil_included))))))))
        | Cons (y, l0) ->
          let h3 = fun f0 x1 -> h f0 (in_cons y f0 l0 x1) in
          let s = f l0 h3 in
          let ExistT (x1, s0) = s in
          let ExistT (x2, p0) = s0 in
          let Pair (i0, p1) = p0 in
          let Pair (_, i1) = p1 in
          let h5 = h y (in_eq y l0) in
          (match h5 with
           | Inl a ->
             ExistT (x1, (ExistT ((Cons (y, x2)), (Pair ((fun a0 x3 ->
               match x3 with
               | Inl _ ->
                 let rec f0 = function
                 | Nil -> Inl __
                 | Cons (_, l2) -> Inr (Obj.magic f0 l2)
                 in f0 x1
               | Inr i2 ->
                 let h4 = Obj.magic i0 a0 i2 in
                 let rec f0 l1 h6 =
                   match l1 with
                   | Nil -> Inr h6
                   | Cons (_, l2) ->
                     (match h6 with
                      | Inl _ -> Inl __
                      | Inr i3 -> Inr (Obj.magic f0 l2 i3))
                 in f0 x1 h4),
               (Pair (__, (fun f0 x3 ->
               match x3 with
               | Inl _ -> a
               | Inr i2 -> Obj.magic i1 f0 i2))))))))
           | Inr _ ->
             ExistT ((Cons (y, x1)), (ExistT (x2, (Pair ((fun a x3 ->
               match x3 with
               | Inl _ -> Inl __
               | Inr b -> Inr (Obj.magic i0 a b)), (Pair (__, i1))))))))
      in f eta x0
    in
    let lemma2 = fun eta x0 ->
      let h3 = lemma3 eta x0 in
      let ExistT (_, s) = h3 in
      let ExistT (x1, p0) = s in
      let Pair (_, p1) = p0 in
      let Pair (_, i0) = p1 in ExistT (x1, (Pair (i0, __)))
    in
    let h3 = lemma2 x i in
    snd (Obj.magic h1 Coq_bot)
      (let ExistT (x0, p0) = h3 in
       let Pair (i0, _) = p0 in ExistT (x0, (Pair (i0, (ExistT (__, Tt))))))

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
    (Coq_all f))), Nil)), (Pair ((fun _ _ -> Inr __), (ExistT (__, Tt)))))),
    (Pair ((fun x -> henkin_equiconsistent tAtheory x), (fun x ->
    extTHT Coq_bot x))))))))))

  (** val theory2filter :
      ('a2, 'a1) theory -> 'a1 CBAproof_completion.coq_Filter **)

  let theory2filter hT =
    { CBAproof_completion.nonempty = (ExistT (CBAproof.top,
      (snd (hT (Coq_imp (Coq_bot, Coq_bot))) (ExistT (Nil, (Pair
        (nil_included, (ExistT (__, Tt)))))))));
      CBAproof_completion.upwards_closed = (fun x y x0 _ ->
      let h' = fst (hT x) x0 in
      let ExistT (x1, p) = h' in
      let Pair (i, _) = p in
      let hT' = hT y in snd hT' (ExistT (x1, (Pair (i, (ExistT (__, Tt)))))));
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
        (ExistT (__, Tt))))))) }

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

  (** val coq_F_n_theory :
      ('a2, 'a1) theory -> nat -> (('a1, 'a2) coq_GAx, ('a1, 'a2) coq_G)
      theory **)

  let rec coq_F_n_theory ttheory = function
  | O ->
    (fun f -> Pair ((fun x -> Obj.magic x), (fun x ->
      let h2 = snd (coq_T1theory ttheory f) in Obj.magic h2 x)))
  | S n0 ->
    let iHn = coq_F_n_theory ttheory n0 in
    (fun _ -> Pair ((fun h ->
    let h0 =
      let ExistT (_, s) = Obj.magic h in
      let ExistT (x, p) = s in
      let Pair (_, p0) = p in
      let Pair (f, _) = p0 in
      let h0 = fun y yys ->
        let h0 =
          let h4 = CBAproof_completion.lemma5 x n0 f in
          (match h4 with
           | Inl f0 ->
             Inl
               (let rec f1 l yys0 case1 =
                  match l with
                  | Nil -> assert false (* absurd case *)
                  | Cons (_, l0) ->
                    let case2 = CBAproof_completion.lemma61 l0 case1 in
                    (match yys0 with
                     | Inl _ -> let Pair (_, b) = case2 in b
                     | Inr i ->
                       let Pair (f2, _) = case2 in Obj.magic f1 l0 i f2)
                in f1 x yys f0)
           | Inr s0 ->
             let ExistT (x0, p1) = s0 in
             let Pair (_, p2) = p1 in
             let Pair (_, p3) = p2 in
             let Pair (f0, e) = p3 in
             (match formula_dec y x0 with
              | Left -> Inr (Inr (Pair (__, e)))
              | Right ->
                Inl
                  (let ys' = remove CBAproof.id_B_dec x0 x in
                   let yys' = remove_In_neq_In x y x0 (Obj.magic yys) in
                   let rec f1 l hfold yys'0 =
                     match l with
                     | Nil -> assert false (* absurd case *)
                     | Cons (_, l0) ->
                       let hfold0 = CBAproof_completion.lemma61 l0 hfold in
                       (match Obj.magic yys'0 with
                        | Inl _ -> let Pair (_, b) = hfold0 in b
                        | Inr i -> let Pair (a, _) = hfold0 in f1 l0 a i)
                   in f1 ys' f0 yys')))
        in
        (match h0 with
         | Inl g ->
           let hth = fst (iHn y) g in
           let ExistT (x0, p1) = hth in
           let Pair (i, _) = p1 in
           ExistT (x0, (Pair ((fun f0 h1 -> Inl (i f0 h1)), __)))
         | Inr g ->
           ExistT ((Cons (y, Nil)), (Pair ((fun _ hr ->
             match Obj.magic hr with
             | Inl _ -> g
             | Inr _ -> assert false (* absurd case *)), __))))
      in
      let h1 =
        let rec f0 l h1 =
          match l with
          | Nil -> ExistT (Nil, (Pair (nil_included, __)))
          | Cons (y, l0) ->
            let h2 = fun y0 x0 -> h1 y0 (Inr x0) in
            let h3 = h1 y (Inl __) in
            let iH = Obj.magic f0 l0 h2 in
            let ExistT (x0, p1) = h3 in
            let Pair (i, _) = p1 in
            let ExistT (x1, p2) = iH in
            let Pair (i0, _) = p2 in
            ExistT ((app x0 x1), (Pair ((included_lem1 x0 x1 i i0), __)))
        in f0 x h0
      in
      let ExistT (x0, p1) = h1 in
      let Pair (i, _) = p1 in ExistT (x0, (Pair (i, __)))
    in
    let ExistT (x, p) = h0 in
    let Pair (i, _) = p in
    ExistT (x, (Pair ((Obj.magic i), (ExistT (__, Tt)))))), (fun h ->
    let ExistT (x, p) = h in
    let Pair (i, _) = p in
    Obj.magic (ExistT ((length x), (ExistT (x, (Pair (__, (Pair
      ((let rec f l h01 =
          match l with
          | Nil -> Obj.magic Tt
          | Cons (y, l0) ->
            CBAproof_completion.lemma62 l0 (Pair
              ((f l0 (fun f0 h0 -> Obj.magic h01 f0 (Inr h0))),
              (let s = Obj.magic h01 y (Inl __) in
               match s with
               | Inl g ->
                 Inl
                   (snd (Obj.magic iHn y) (ExistT ((Cons (y, Nil)), (Pair
                     ((fun _ x0 ->
                     match x0 with
                     | Inl _ -> g
                     | Inr _ -> assert false (* absurd case *)), (ExistT (__,
                     Tt)))))))
               | Inr p0 -> Inr p0)))
        in f x i),
      __)))))))))))

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
      let Pair (i, _) = p in
      let h0 =
        let rec f0 l h1 =
          match l with
          | Nil -> ExistT (O, (fun _ _ -> assert false (* absurd case *)))
          | Cons (y, l0) ->
            let h0 = fun f1 x0 -> Obj.magic h1 f1 (Inr x0) in
            let iH = f0 l0 h0 in
            let ExistT (x0, g) = iH in
            let h1' = h1 y in
            let h2 = Obj.magic h1' (Inl __) in
            let ExistT (x1, g0) = h2 in
            let s = CBAproof_completion.le_lt_dec x1 x0 in
            (match s with
             | Inl l1 ->
               let h3 = coq_GAx_monotone x1 x0 l1 in
               ExistT (x0, (fun f1 h4 ->
               match h4 with
               | Inl _ -> h3 y g0
               | Inr b -> Obj.magic g f1 b))
             | Inr l1 ->
               let h3 = CBAproof_completion.lt_le_incl x0 x1 l1 in
               let h4 = coq_GAx_monotone x0 x1 h3 in
               ExistT (x1, (fun f1 h5 ->
               match h5 with
               | Inl _ -> g0
               | Inr b -> h4 f1 (Obj.magic g f1 b))))
        in f0 x i
      in
      let ExistT (x0, i0) = h0 in
      ExistT (x0,
      (let h3 = snd (coq_F_n_theory ttheory x0 f) in
       Obj.magic h3 (ExistT (x, (Pair (i0, (ExistT (__, Tt))))))))))

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
         let Pair (f0, _) = p2 in
         let h6 = CBAproof_completion.lemma8 f x0 f0 in
         (match h6 with
          | Inl f1 ->
            CBAproof_completion.upwards_closed (fst (lem15 ttheory))
              CBAproof.bott (Coq_imp (f, Coq_bot))
              (CBAproof_completion.upwards_closed (fst (lem15 ttheory))
                (fold_left CBAproof.meet x0 CBAproof.top) CBAproof.bott
                (CBAproof_completion.lemma4 x0 (fst (lem15 ttheory)) f1))
          | Inr f1 ->
            let z' = remove CBAproof.id_B_dec f x0 in
            let z = fold_left CBAproof.meet z' CBAproof.top in
            CBAproof_completion.upwards_closed (fst (lem15 ttheory)) z
              (Coq_imp (f, Coq_bot))
              (CBAproof_completion.lemma4 z' (fst (lem15 ttheory)) f1)))))))

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
         let Pair (i, _) = p in
         let ExistT (x2, p0) = h2' in
         let Pair (i0, _) = p0 in
         ExistT ((app x1 x2), (Pair ((fun f x3 ->
         let s = in_app_or x1 x2 f x3 in
         (match s with
          | Inl i1 -> i f i1
          | Inr i1 -> i0 f i1)),
         (ExistT (__, Tt))))))
    in
    Pair (dir1, (fun a b x ->
    metaDNZ' ttheory (Coq_imp (a, b)) (fun h0 ->
      dir1 b Coq_bot
        (let h2' =
           fst (coq_Z'theory ttheory (Coq_imp ((Coq_imp (a, b)), Coq_bot))) h0
         in
         let ExistT (x0, p) = h2' in
         let Pair (i, _) = p in
         snd (coq_Z'theory ttheory (Coq_imp (b, Coq_bot))) (ExistT (x0, (Pair
           (i, (ExistT (__, Tt)))))))
        (x
          (let h2' =
             fst (coq_Z'theory ttheory (Coq_imp ((Coq_imp (a, b)), Coq_bot)))
               h0
           in
           let ExistT (x0, p) = h2' in
           let Pair (i, _) = p in
           snd (coq_Z'theory ttheory a) (ExistT (x0, (Pair (i, (ExistT (__,
             Tt)))))))))))

  (** val model_existence3' : formula -> ('a1, 'a2) coq_Z' **)

  let model_existence3' f =
    let h1 = ExistT ((Cons ((Coq_imp
      ((coq_open f (Coq_cnst (Coq_added (Coq_all f)))), (Coq_all f))), Nil)),
      (Pair ((fun _ _ -> Inr __), (ExistT (__, Tt)))))
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
       let Pair (i, _) = p in ExistT (x0, (Pair (i, (ExistT (__, Tt))))))),
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
      (ExistT (Nil, (Pair (nil_included, (ExistT (__, Tt)))))));
    model_imp_faithful1 = (fst (model_existence2 ttheory));
    model_imp_faithful2 = (snd (model_existence2 ttheory));
    model_all_faithful1 = (fst (model_existence3 ttheory));
    model_all_faithful2 = (snd (model_existence3 ttheory)) }, b)))
 end
