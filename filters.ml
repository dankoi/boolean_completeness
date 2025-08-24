
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
 end
