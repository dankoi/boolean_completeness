
(** List [In] in Set *)
Fixpoint In {A:Set}(a:A) (l:list A) : Set :=
  match l with
  | nil => Empty_set
  | cons b m => (b = a) + In a m
  end.

Definition incl {A:Set} l m := forall a:A, In a l -> In a m.
Hint Unfold incl : core.

(* a finite list of formulas is included in a set of formulas *)
Definition included {A:Set}(Gamma:list A)(T:A->Set) :=
  forall f, In f Gamma -> T f.

Theorem in_eq {A:Set} : forall (a:A) l, In a (a :: l).
Proof.
  simpl; auto.
Qed.

Theorem in_cons {A:Set} : forall (a b:A) l, In b l -> In b (a :: l).
Proof.
  simpl; auto.
Qed.

Lemma nil_included {A:Set} : forall (Ax:A->Set), included nil Ax.
Proof.
  red.
  simpl.
  intros.
  elim H.
Qed.

Lemma nil_lem1 {A:Set} : forall l:list A, incl nil l.
Proof.
  red.
  simpl.
  intros.
  elim H.
Qed.

Lemma in_app_or {A:Set} : forall l m (a:A), In a (l ++ m) -> In a l + In a m.
Proof.
  intros l m a.
  elim l; simpl; auto.
  intros a0 y H H0.
  elim H0; auto.
  intro H1.
  elim (H H1); auto.
Qed.

Lemma in_or_app {A:Set} : forall l m (a:A), In a l + In a m -> In a (l ++ m).
Proof.
  intros l m a.
  elim l; simpl; intro H.
  now_show (In a m).
  elim H; auto; intro H0.
  now_show (In a m).
  elim H0.
  intros y H0 H1.
  now_show ((H = a) + In a (y ++ m))%type.
  elim H1; auto 4.
  intro H2.
  now_show ((H = a) + In a (y ++ m))%type.
  elim H2; auto.
Qed.

Lemma included_lem1 {A:Set} : forall l1 l2:list A, forall Ax:A->Set,
    included l1 Ax -> included l2 Ax -> included (l1++l2) Ax.
Proof.
  unfold included.
  intros.
  destruct (in_app_or l1 l2 f H1); auto.
Qed.

Lemma incl_tran {A:Set} : forall l m n:list A, incl l m -> incl m n -> incl l n.
Proof.
  auto.
Qed.

Lemma incl_refl {A:Set} : forall l:list A, incl l l.
Proof.
  auto.
Qed.
Hint Resolve incl_refl : core.

Theorem in_dec {A:Set} :
  (forall x y:A, {x = y} + {x <> y}) ->
  forall (a:A) (l:list A), In a l + (In a l -> Empty_set).
Proof.
  intro H; induction l as [| a0 l IHl].
  right; auto.
  destruct (H a0 a); simpl; auto.
  destruct IHl; simpl; auto.
  right; unfold not; intros [Hc1| Hc2]; auto.
  congruence.
Defined.

Lemma incl_appl {A:Set} : forall l m n:list A, incl l n -> incl l (n ++ m).
Proof.
  auto using in_or_app.
Qed.
Hint Immediate incl_appl : core.

Lemma incl_appr {A:Set} : forall l m n:list A, incl l n -> incl l (m ++ n).
Proof.
  auto using in_or_app.
Qed.
Hint Immediate incl_appr : core.

