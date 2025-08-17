(** A constructive proof of completeness for classical first-order
   logic, globally following the paper of Berardi and Valentini,
   itself unwinding Krivine's proof, itself unwinding the classical
   proof.

   Danko Ilik, October 2008, revisited August 2025 *)

From Stdlib Require Export List.
From Stdlib Require Import Setoid.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Cantor.
From Stdlib Require Import Sorting.Mergesort.
From Stdlib Require Import Orders.

(** This imports the proof of the constructive Ultra-filter Theorem *)
Require Import filters.

Set Implicit Arguments.

(** printing ==> $\Rightarrow$ #⇒# *)

(** To build the syntax of formulas, we start with decidable countable
    sets of constant, function, and predicate symbols. *)
Module Type classical_completeness_signature.
  Parameters function predicate constant0 : Set.
  Parameter function_dec : forall f1 f2:function, {f1 = f2} + {f1 <> f2}.
  Parameter predicate_dec : forall f1 f2:predicate, {f1 = f2} + {f1 <> f2}.
  Parameter constant0_dec : forall f1 f2:constant0, {f1 = f2} + {f1 <> f2}.
  Parameter enum_function : function -> nat.
  Parameter enum_predicate : predicate -> nat.
  Parameter enum_constant0 : constant0 -> nat.
  Parameter enum_function_inj : 
    forall p q, enum_function p = enum_function q -> p = q.
  Parameter enum_predicate_inj : 
    forall p q, enum_predicate p = enum_predicate q -> p = q.
  Parameter enum_constant0_inj : 
    forall p q, enum_constant0 p = enum_constant0 q -> p = q.
End classical_completeness_signature.

Module classical_completeness (ccsig:classical_completeness_signature).
  Export ccsig.

(** A formula is then defined using the above. There is a special
   [added] constructor for constants, these are the Henkin
   constants. There are separate constructors for variables bound by
   quantifiers [bvar], and free variables [fvar].  *)
Inductive formula : Set :=
| bot : formula
| imp : formula -> formula -> formula
| all : formula -> formula
| atom : predicate -> term -> formula
with term : Set :=
| bvar : nat -> term
| fvar : nat -> term
| cnst : constant -> term
| func : function -> term -> term
with constant : Set := 
| original : constant0 -> constant
| added : formula -> constant.

(** 'Opening up' quantifiers, i.e. replacing a quantifier-bound de
    Bruijn variable, by a term. *)
Fixpoint open_rec_term (k : nat) (u : term) (t : term) {struct t} : term :=
  match t with
    | bvar i    => if Nat.eqb k i then u else (bvar i)
    | fvar x    => fvar x
    | cnst c    => cnst c
    | func f t1 => func f (open_rec_term k u t1)
  end.

Fixpoint
  open_rec (k : nat) (u : term) (t : formula) {struct t} : formula :=
  match t with
    | bot       => bot
    | imp t1 t2 => imp (open_rec k u t1) (open_rec k u t2)
    | all t1    => all (open_rec (S k) u t1)
    | atom p t1 => atom p (open_rec_term k u t1)
  end.

(** Substituting the first variable in the term u, the one that would
    be first captured by a surrounding quantifier, by the term t. *)
Definition open t u := open_rec 0 u t.
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (fvar x)).

(** A formula is [locl] (locally closed) when all [bvar]-s are bound
    by quantifiers, although there might well be [fvar]-s around. *)
Definition locl (f:formula) := forall n t, (open_rec n t f) = f.

(** A term is locally-closed if it simply does not have bound
    variables, but let us define it analogously to locl. *)
Definition loclt (t:term) := forall n t', (open_rec_term n t' t) = t.

Definition locll (Gamma:list formula) := forall B, In B Gamma -> locl B.

Definition notin (x:nat) (L:list nat) := not (In x L).
Notation "x \notin L" := (notin x L) (at level 69).

(** Natural deduction system for classical predicate logic with
    cofinite quantification *)
Inductive proof : list formula -> formula -> Prop :=
| bot_elim  : forall Gamma, 
  proof Gamma bot -> forall A, proof Gamma A
| imp_elim  : forall Gamma A B, 
  proof Gamma (imp A B) -> proof Gamma A -> proof Gamma B
| imp_intro : forall Gamma A B, 
  proof (A::Gamma) B -> proof Gamma (imp A B)
| dneg      : forall Gamma A, 
  proof Gamma (imp (imp A bot) bot) -> proof Gamma A
| hypo      : forall Gamma A, 
  In A Gamma -> proof Gamma A
| all_elim  : forall Gamma A, 
  proof Gamma (all A) -> forall t:term, proof Gamma (A^^t)
| all_intro : forall Gamma A L, locl (all A) ->
  (forall x, x \notin L -> proof Gamma (A^x)) -> 
    proof Gamma (all A)
| weaken : forall Gamma A B, proof Gamma A -> proof (B::Gamma) A.

Notation "A ==> B" := (imp A B) (at level 55, right associativity).
Notation "'neg' A" := (imp A bot) (at level 53, right associativity).


Fixpoint added_cnsts (t:term) : bool :=
  match t with
  | (func f t') => added_cnsts t'
  | (cnst c) => 
      match c with
      | (added k) => true
      | (original k) => false
      end
  | (fvar x) => false
  | (bvar x) => false
  end.

Fixpoint added_cnsts_f (f:formula) : bool :=
  match f with
  | (atom p t) => added_cnsts t
  | (all g) => added_cnsts_f g
  | (imp g h) => added_cnsts_f g || added_cnsts_f h
  | bot => false
  end.

(** A general set of formulas *)
Definition formula_set := formula -> Prop.

(** Definition of a "minimal model", one without standard
    interpretation of absurdity *)
Record model (M:formula_set) : Prop := {

  model_dneg : forall A, M (neg neg A ==> A);
  
  model_imp_faithful1 : forall A B, 
    M (A ==> B) -> (M A -> M B);
  
  model_imp_faithful2 : forall A B, 
    (M A -> M B) -> M (A ==> B);
  
  model_all_faithful1 : forall A, 
    M (all A) -> 
    forall t:term, M (A^^t);
  
  model_all_faithful2 : forall A, locl (all A) -> added_cnsts_f A = false -> 
    (forall t:term, loclt t -> M (A^^t)) ->  
    M (all A)
}.

(** The definition of a "classical" as opposed to a "minimal" model is
   given, but not used. *)
Definition model_bot_faithful (M:formula_set) := not (M bot).
Definition classical_model (M:formula_set) : Prop :=
  model M /\ model_bot_faithful M.

(** A set of formulas interprets a sequent Gamma|-A if the inclusion
    of Gamma implies the membership of A *)
Definition interprets (M:formula_set)(Gamma:list formula)(A:formula) :=
  (forall f, In f Gamma -> M f) -> M A.

(** A sequent is valid if it is true in all models *)
Definition valid (Gamma:list formula)(A:formula) := 
  forall M, model M -> interprets M Gamma A.

Section natural_deduction_lemmas.
  Lemma peirce : forall Gamma P Q, proof Gamma (((P ==> Q) ==> P) ==> P).
  Proof with (simpl;auto).
    intros.
    apply imp_intro...
    apply dneg...
    apply imp_intro...
    apply imp_elim with P...
    apply hypo...
    apply imp_elim with (P  ==>  Q)...
    apply hypo...
    apply imp_intro...
    apply bot_elim...
    apply imp_elim with P...
    apply hypo...
    apply hypo...
  Defined.
  
  Lemma proof_imp_trans : forall Gamma x y z, 
    proof Gamma (x ==> y) -> proof Gamma (y ==> z) -> proof Gamma (x ==> z).
  Proof.
    intros Gamma x y z Hxy Hyz.
    apply imp_intro.
    apply imp_elim with y.
    apply weaken.
    assumption.
    apply imp_elim with x.
    apply weaken.
    assumption.
    apply hypo; simpl; auto.
  Defined.
  
  Lemma proof_imp_contrapos : forall Gamma x y, 
    proof Gamma (x ==> y) -> proof Gamma (neg y ==> neg x).
  Proof.
    intros.
    apply imp_intro.
    apply imp_intro.
    apply imp_elim with y.
    apply weaken.
    apply hypo; simpl; auto.
    apply imp_elim with x.
    apply weaken.
    apply weaken.
    assumption.
    apply hypo; simpl; auto.
  Defined.
End natural_deduction_lemmas.

(** Some tactics used for building the Lindenbaum algebra below *)
Ltac impi := apply imp_intro.
Ltac impe := fun x => apply imp_elim with x.
Ltac dneg := apply dneg.
Ltac hypo := apply hypo; simpl; auto.
Ltac weak := apply weaken.
Ltac tran := fun x => apply proof_imp_trans with x.
Ltac contra := apply proof_imp_contrapos.

Lemma formula_dec : forall x y:formula, {x = y}+{x <> y}.
Proof.
  fix formula_dec 1.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
  apply constant0_dec.
  apply function_dec.
  apply predicate_dec.
Defined.

Lemma constant_dec : forall f1 f2:constant, {f1 = f2} + {f1 <> f2}.
Proof.
  fix constant_dec 1.
  decide equality.
  apply constant0_dec.
  apply formula_dec.
Defined.

Module Export CBAproof <: CBA.

(** The Lindenbaum Boolean algebra which will be used in the model
    existence lemma to build a maximal consistent extension of a set
    of formulas. (the "Universal model") *)
Section boolean_algebra.

  Let B := formula.

  Definition compl : B -> B.
    intro x.
    exact (neg x).
  Defined.

  Definition meet : B -> B -> B.
    intros x y.
    exact (neg (x ==> (neg y))).
  Defined.

  Definition join : B -> B -> B.
    intros x y.
    exact ((neg x) ==> y).
  Defined.

  Definition top : B.
    exact (bot ==> bot).
  Defined.

  (* equality has to be in prop for practical reasons - defining a
     Coq-setoid *)
  Definition eq_B (x y:B): Prop := 
    (exists p:proof nil (x ==> y), True) 
    /\ (exists p:proof nil (y ==> x), True).

  Theorem eq_B_refl : reflexive B eq_B.
  Proof.
    red.
    unfold eq_B.
    intros.
    assert (proof nil (x ==> x)).
    apply imp_intro.
    apply hypo.
    simpl.
    left.
    reflexivity.
    firstorder.
  Defined.

  Theorem eq_B_symm : symmetric B eq_B.
  Proof.
    red.
    unfold eq_B.
    intros.
    firstorder.
  Defined.

  Theorem eq_B_trans : transitive B eq_B.
  Proof.
    red.
    unfold eq_B.
    intros.
    set (X:=x) in *.
    set (Y:=y) in *.
    set (Z:=z) in *.
    destruct H as [[pXY _] [pYX _]].
    destruct H0 as [[pYZ _] [pZY _]].
    assert (pXZ:=proof_imp_trans pXY pYZ).
    assert (pZX:=proof_imp_trans pZY pYX).
    firstorder.
  Defined.

  Notation "x == y" := (eq_B x y) (at level 70, no associativity).

  Add Relation B eq_B
    reflexivity proved by eq_B_refl
    symmetry proved by eq_B_symm
    transitivity proved by eq_B_trans
  as eq_B_relation.

  Add Morphism join with signature eq_B ==> eq_B ==> eq_B as join_morphism. 
  Proof.
    unfold eq_B; try red.
    intros x y H x0 y0 H0.
    generalize dependent (x0).
    generalize dependent (x).
    generalize dependent (y).
    generalize dependent (y0).
    clear.
    intros W X Y H1 Z H2.
    destruct H1 as [[pYX _] [pXY _]].
    destruct H2 as [[pZW _] [pWZ _]].
    split.
    assert (proof nil ((neg Y ==> Z) ==> (neg X ==> W))).
    apply proof_imp_trans with (neg Y ==> W).
      apply imp_intro.
      apply imp_intro.
      apply imp_elim with Z.
      apply weaken.
      apply weaken.
      assumption.
      apply imp_elim with (neg Y).
      apply weaken.
      apply hypo.
      simpl; auto.
      apply hypo.
      simpl; auto.
      apply imp_intro.
      apply imp_intro.
      apply imp_elim with (neg Y).
      apply weaken.
      apply hypo.
      simpl; auto.
      apply imp_elim with (neg X).
      apply weaken.
      apply weaken.
      apply proof_imp_contrapos.
      assumption.
      apply hypo.
      simpl; auto.
      exists H.
      auto.
    (* completelly the same as the above proof *)
    assert (proof nil ((neg X ==> W) ==> (neg Y ==> Z))).
    apply proof_imp_trans with (neg X ==> Z).
      apply imp_intro.
      apply imp_intro.
      apply imp_elim with W.
      apply weaken.
      apply weaken.
      assumption.
      apply imp_elim with (neg X).
      apply weaken.
      apply hypo.
      simpl; auto.
      apply hypo.
      simpl; auto.
      apply imp_intro.
      apply imp_intro.
      apply imp_elim with (neg X).
      apply weaken.
      apply hypo.
      simpl; auto.
      apply imp_elim with (neg Y).
      apply weaken.
      apply weaken.
      apply proof_imp_contrapos.
      assumption.
      apply hypo.
      simpl; auto.
      exists H.
      auto.
  Defined.
    
  Add Morphism meet with signature eq_B ==> eq_B ==> eq_B as meet_morphism. 
  Proof.
    unfold eq_B.
    intros x y H x0 y0 H0.
    generalize dependent (x0).
    generalize dependent (x).
    generalize dependent (y).
    generalize dependent (y0).
    clear.
    intros W X Y H1 Z H2.
    destruct H1 as [[pYX _] [pXY _]].
    destruct H2 as [[pZW _] [pWZ _]].
    split.
    assert (proof nil (neg (Y ==> neg Z) ==> neg (X ==> neg W))).
    impi.
    impi.
    impe (Y ==> neg Z).
    weak;hypo.
    impi.
    impe (neg W).
    apply proof_imp_contrapos.
    weak;weak;weak;assumption.
    impe X.
    hypo;weak.
    impe Y.
    weak;weak;weak;assumption.
    hypo.
    exists H; auto.
    assert (proof nil (neg (X ==> neg W) ==> neg (Y ==> neg Z))).
    apply proof_imp_contrapos.
    impi.
    tran (neg Z).
    tran Y.
    weak;assumption.
    hypo.
    contra.
    weak;assumption.
    exists H; auto.
  Defined.

  Lemma id_B_dec : forall x y : B, {x = y}+{x <> y}.
    intros.
    apply formula_dec.
  Defined.

  Lemma id_B_dec_right : forall (x y:B), x<>y -> 
    exists H:x<>y, id_B_dec x y = right (x=y) H.
  Proof.
    intros.
    unfold id_B_dec.
    case (formula_dec x y).
    (* case 1 *)
    intros eqxy.
    congruence.
    (* case 2 *)
    intro.
    exists n.
    reflexivity.
  Defined.

  Lemma id_B_dec_left : forall x:B, exists H:x=x, 
    id_B_dec x x = left (x<>x) H.
  Proof.
    intros.
    unfold id_B_dec.
    case (formula_dec x x).
    (* case 1 *)
    intro.
    exists e.
    reflexivity.
    (* case 2 *)
    intros neqxy.
    congruence.
  Defined.

  Lemma join_idem : forall x, join x x == x.
    intro x.
    unfold eq_B.
    generalize dependent (x).
    clear.
    intro f.
    split.
    assert (proof nil ((neg f ==> f) ==> f)).
    impi.
    dneg.
    impi.
    impe f.
    hypo.
    impe (neg f).
    weak.
    hypo.
    hypo.
    firstorder.
    assert (proof nil (f ==> (neg f ==> f))).
    impi.
    impi.
    weak.
    hypo.
    firstorder.
  Defined.

  Lemma meet_idem : forall x, meet x x == x.
  Proof.
    intro.
    unfold eq_B.
    simpl proj1_sig.
    generalize dependent (x).
    intro f.
    clear.
    split.
    (* this all should be done by one Ltac command *)
    assert (proof nil (neg (f ==> neg f) ==> f)).
    impi.
    dneg.
    impi.
    impe (f==>neg f).
    weak; hypo.
    impi.
    weak; hypo.
    exists H; auto.
    assert (proof nil (f ==> neg (f ==> neg f))).
    impi.
    impi.
    impe f.
    impe f.
    hypo.
    weak; hypo.
    weak; hypo.
    exists H; auto.
  Defined.

  Lemma join_comm : forall x y, join x y == join y x.
  Proof.
    intros.
    unfold eq_B.
    generalize dependent (x).
    generalize dependent (y).
    intros X Y.
    clear.
    split.
    (* this all should be done by one Ltac command *)
    assert (proof nil ((neg Y ==> X) ==> (neg X ==> Y))).
    impi.
    impi.
    dneg.
    impi.
    impe X.
    weak; hypo.
    impe (neg Y).
    weak; weak; hypo.
    hypo.
    exists H; auto.
    assert (proof nil ((neg X ==> Y) ==> (neg Y ==> X))).
    impi.
    impi.
    dneg.
    impi.
    impe Y.
    weak; hypo.
    impe (neg X).
    weak; weak; hypo.
    hypo.
    exists H; auto.
  Defined.

  Lemma meet_comm : forall x y, meet x y == meet y x.
  Proof.
    intros.
    unfold eq_B.
    generalize dependent (x).
    generalize dependent (y).
    intros X Y.
    clear.
    split.
    (* this all should be done by one Ltac command *)
    assert (proof nil (neg (Y ==> neg X) ==> neg (X ==> neg Y))).
    impi.
    impi.
    impe (Y ==> neg X).
    weak; hypo.
    impi.
    impi.
    impe Y.
    impe X.
    weak; weak; hypo.
    hypo.
    weak; hypo.
    exists H; auto.
    assert (proof nil (neg (X ==> neg Y) ==> neg (Y ==> neg X))).
    impi; impi.
    impe (X ==> neg Y).
    hypo; weak.
    impi;impi.
    impe X.
    impe Y.
    weak; weak; hypo.
    hypo.
    weak; hypo.
    exists H; auto.
  Defined.

  Lemma join_assoc : forall x y z, join x (join y z) == join (join x y) z.
  Proof.
    intros.
    unfold eq_B.
    generalize dependent (x).
    generalize dependent (y).
    generalize dependent (z).
    intros X Y Z.
    clear.
    split.
    (* this all should be done by one Ltac command *)
    assert (proof nil ((neg Z ==> (neg Y ==> X)) ==> (neg (neg Z ==> Y) ==> X))).
    impi.
    impi.
    impe (neg Y).
    impe (neg Z).
    weak; hypo.
    impi.
    impe (neg Z ==> Y).
    weak; hypo.
    impi.
    apply bot_elim.
    impe Z.
    hypo.
    weak; hypo.
    impi.
    impe (neg Z ==> Y).
    weak; hypo.
    impi.
    weak; hypo.
    exists H; auto.
    assert (proof nil ((neg (neg Z ==> Y) ==> X) ==> (neg Z ==> (neg Y ==> X)))).
    impi;impi;impi.
    impe (neg (neg Z ==> Y)).
    weak; weak; hypo.
    impi.
    impe Y.
    weak; hypo.
    impe (neg Z).
    hypo.
    weak;weak;hypo.
    exists H; auto.
  Defined.

  Lemma meet_assoc : forall x y z, meet x (meet y z) == meet (meet x y) z.
  Proof.
    intros.
    unfold eq_B.
    generalize dependent (x).
    generalize dependent (y).
    generalize dependent (z).
    intros X Y Z.
    clear.
    split.
    (* this all should be done by one Ltac command *)
    assert (
      proof nil
      (neg (Z ==> neg neg (Y ==> neg X)) ==>
        neg (neg (Z ==> neg Y) ==> neg X))
    ).
    contra.
    impi;impi.
    impi.
    impe (Y ==> neg X).
    hypo.
    impi.
    impe (neg (Z ==> neg Y)).
    weak;weak;weak;hypo.
    impi.
    impe Y.
    impe Z.
    hypo.
    weak;weak;weak;hypo.
    weak;hypo.
    exists H; auto.
    assert (
      proof nil
      (neg (neg (Z ==> neg Y) ==> neg X) ==>
        neg (Z ==> neg neg (Y ==> neg X)))
    ).
    contra.
    impi.
    contra.
    impi.
    impi.
    impi.
    impe (neg (Y ==> neg X)).
    impe Z.
    weak;weak;weak;hypo.
    weak;hypo.
    impi.
    impe X.
    impe Y.
    hypo.
    weak;hypo.
    weak;weak;weak;hypo.
    exists H; auto.
  Defined.

  Lemma meet_absorb : forall x y, meet x (join x y) == x.
  Proof.
    intros.
    unfold eq_B.
    simpl proj1_sig.
    generalize dependent (x).
    generalize dependent (y).
    intros X Y.
    clear.
    split.
    (* this all should be done by one Ltac command *)
    assert (proof nil (neg (Y ==> neg (neg Y ==> X)) ==> Y)).
    impi.
    dneg.
    impi.
    impe (Y ==> neg (neg Y ==> X)).
    weak; hypo.
    impi.
    apply bot_elim.
    impe Y.
    weak; hypo.
    hypo.
    exists H; auto.
    assert (proof nil (Y ==> neg (Y ==> neg (neg Y ==> X)))).
    impi;impi.
    impe (neg Y ==> X).
    impe Y.
    hypo.
    weak; hypo.
    impi.
    apply bot_elim.
    impe Y.
    hypo.
    weak; weak; hypo.
    exists H; auto.
  Defined.

  Lemma join_absorb : forall x y, join x (meet x y) == x.
  Proof.
    intros.
    unfold eq_B.
    simpl proj1_sig.
    generalize dependent (x).
    generalize dependent (y).
    intros X Y.
    clear.
    split.
    (* this all should be done by one Ltac command *)
    assert (proof nil ((neg Y ==> neg (Y ==> neg X)) ==> Y)).
    impi.
    dneg.
    impi.
    impe (Y ==> neg X).
    impe (neg Y).
    weak; hypo.
    hypo.
    impi.
    apply bot_elim.
    impe Y.
    weak; hypo.
    hypo.
    exists H; auto.
    assert (proof nil (Y ==> (neg Y ==> neg (Y ==> neg X)))).
    impi; impi.
    apply bot_elim.
    impe Y.
    hypo.
    weak; hypo.
    exists H; auto.
  Defined.

  Lemma join_distrib : forall x y z, join (meet x y) z == meet (join x z) (join y z).
  Proof.
    intros.
    unfold eq_B.
    simpl proj1_sig.
    generalize dependent (x).
    generalize dependent (y).
    generalize dependent (z).
    intros X Y Z.
    clear.
    split.
    (* this all should be done by one Ltac command *)
    assert (proof nil
              ((neg neg (Z ==> neg Y) ==> X) ==>
               neg ((neg Z ==> X) ==> neg (neg Y ==> X)))).
    impi;impi.
    impe (neg Y ==> X).
    impe (neg Z ==> X).
    hypo.
    impi.
    impe (neg neg (Z ==> neg Y)).
    weak;weak;hypo.
    impi.
    impe (Z ==> neg Y).
    hypo.
    impi.
    apply bot_elim.
    impe Z.
    weak;weak;hypo.
    hypo.
    impi.
    impe (neg neg (Z ==> neg Y)).
    weak;weak;hypo.
    impi.
    impe (Z ==> neg Y).
    hypo.
    impi.
    weak;weak;hypo.
    exists H; auto.
    assert (proof nil
              (neg ((neg Z ==> X) ==> neg (neg Y ==> X)) ==>
               (neg neg (Z ==> neg Y) ==> X))).
    impi.
    impi.
    dneg.
    impi.
    impe ((neg Z ==> X) ==> neg (neg Y ==> X)).
    weak;hypo.
    impi.
    impi.
    impe X.
    weak;weak;hypo.
    dneg.
    impi.
    impe (neg (Z ==> neg Y)).
    weak;weak;weak;hypo.
    impi.
    impe Z.
    impi.
    impe (X).
    weak;weak;hypo.
    impe  (neg Y).
    weak;weak;weak;hypo.
    impe Z.
    weak;hypo.
    hypo.
    (* the second subgoal by LEM, Z or not Z*)
    dneg.
    impi.
    impe X.
    weak;weak;hypo.
    impe (neg Z).
    weak;weak;weak;hypo.
    hypo.
    exists H; auto.
  Defined.

  Lemma meet_bott : forall x, meet bot x == bot.
  Proof.
   intros.
   unfold eq_B.
   generalize dependent (x).
   intros X  .
   clear.
   split.
   (* this all should be done by one Ltac command *)
   assert (proof nil (neg neg (bot ==> neg X))).
   impi.
   impe (bot ==> neg X).
   hypo.
   impi.
   impi.
   weak;hypo.
   exists H;auto.
   assert (proof nil (bot ==> neg (bot ==> neg X))).
   impi.
   impi.
   weak;hypo.
   exists H;auto.
  Defined.

  Lemma join_bott : forall x, join bot x == x.
  Proof.
   intros.
   unfold eq_B.
   generalize dependent (x).
   intros X  .
   clear.
   split.
   (* this all should be done by one Ltac command *)
   assert (proof nil ((neg bot ==> X) ==> X)).
   impi.
   impe (neg bot).
   hypo.
   impi.
   hypo.
   exists H;auto.
   assert (proof nil (X ==> (neg bot ==> X))).
   impi.
   impi.
   weak;hypo.
   exists H;auto.
  Defined.

  Lemma meet_top : forall x, meet top x == x.
  Proof.
   intros.
   unfold eq_B.
   generalize dependent (x).
   intros X  .
   clear.
   split.
   (* this all should be done by one Ltac command *)
   assert (proof nil (neg (neg bot ==> neg X) ==> X)).
   impi.
   dneg.
   impi.
   impe (neg bot ==> neg X).
   weak;hypo.
   impi.
   weak; hypo.
   exists H;auto.
   assert (proof nil (X ==> neg (neg bot ==> neg X))).
   impi.
   impi.
   impe (neg bot).
   impi.
   impe X.
   impe (neg bot).
   weak;hypo.
   hypo.
   weak;weak;hypo.
   impi.
   hypo.
   exists H;auto.
  Defined.

  Lemma join_top : forall x, join top x == top.
  Proof.
   intros.
   unfold eq_B.
   generalize dependent (x).
   intros X  .
   clear.
   split.
   (* this all should be done by one Ltac command *)
   assert (proof nil ((neg neg bot ==> X) ==> neg bot)).
   impi.
   impi.
   hypo.
   exists H;auto.
   assert (proof nil (neg bot ==> (neg neg bot ==> X))).
   impi.
   impi.
   dneg.
   impi.
   impe (neg bot).
   weak;hypo.
   weak;weak;hypo.
   exists H;auto.
  Defined.

  Lemma meet_compl : forall x, meet x (compl x) == bot.
  Proof.
   intros.
   unfold eq_B.
   generalize dependent (x).
   intros X  .
   clear.
   split.
   (* this all should be done by one Ltac command *)
   assert (proof nil (neg neg (X ==> neg neg X))).
   impi.
   impe (X ==> neg neg X).
   hypo.
   impi.
   impi.
   impe X.
   hypo.
   weak;hypo.
   exists H;auto.
   assert (proof nil (bot ==> neg (X ==> neg neg X))).
   impi.
   impi.
   weak; hypo.
   exists H;auto.
  Defined.

  Lemma join_compl : forall x, join x (compl x) == top.
  Proof.
   intros.
   unfold eq_B.
   generalize dependent (x).
   intros X  .
   clear.
   split.
   (* this all should be done by one Ltac command *)
   assert (proof nil ((neg X ==> neg X) ==> neg bot)).
   impi.
   impi.
   hypo.
   exists H;auto.
   assert (proof nil (neg bot ==> (neg X ==> neg X))).
   impi.
   impi.
   hypo.
   exists H;auto.
  Defined.

  Lemma meet_distrib : forall x y z, meet (join x y) z == join (meet x z) (meet y z).
  Proof.
  (* one distributive law can be derived from the other one - no need
     to make a natural deduction derivation *)
    intros b c a.
    rewrite (meet_comm (join b c) a).
    rewrite (meet_comm b a).
    rewrite (meet_comm c a).
    rewrite join_distrib.
    rewrite join_absorb.
    rewrite (join_comm b (meet a c)).
    rewrite join_distrib.
    rewrite meet_assoc.
    rewrite meet_absorb.
    rewrite join_comm.
    reflexivity.
  Defined.
End boolean_algebra.

(** To use the completion of filters from filters.v, we also need an
    enumeration of the elements of the Boolean algebra, which is
    achieved by using the Cantor pairing function from the Coq
    standard library (formerly we used the one from Russell O'Connor's
    formalization of the incompleteness theorem) *)
Section Enumeration.
  Definition enump := fun p => to_nat (11, enum_predicate p).
  Definition enumc0 := fun c => to_nat (12, enum_constant0 c).
  Definition enumfunc := fun f => to_nat (13, enum_function f).
  
  Fixpoint enumf (f:formula) : nat :=
    match f with
      | (atom p t) => to_nat (1, to_nat (enump p, enumt t))
      | (all g) => to_nat (2, enumf g)
      | (imp g h) => to_nat (3, to_nat (enumf g, enumf h))
      | bot => to_nat (4, 0)
    end
  with enumt (t:term) : nat :=
    match t with
      | (func phi t') => to_nat (5, to_nat (enumfunc phi, enumt t'))
      | (cnst c) => to_nat (6, enumc c)
      | (fvar x) => to_nat (7, x)
      | (bvar x) => to_nat (8, x)
    end
  with enumc (c:constant) : nat :=
    match c with
      | (added x) => to_nat (9, enumf x)
      | (original x) => to_nat (10, enumc0 x)
    end.
  
  (* Eval compute in (enumf (imp bot bot)). *)

  Scheme Induction for formula Sort Prop
  with Induction for term Sort Prop
  with Induction for constant Sort Prop.
  
  Combined Scheme ftc_ind from formula_ind, term_ind, constant_ind.

  Theorem countable_ftc : 
    (forall f g, enumf f = enumf g -> f = g)
    /\ (forall t s, enumt t = enumt s -> t = s)
    /\ (forall c k, enumc c = enumc k -> c = k).
  Proof.
    Opaque to_nat.
    apply ftc_ind.

    intros g Hg.
    destruct g;
      (try reflexivity; 
        apply to_nat_inj in Hg;
        fold enumf in Hg;
        discriminate).

    intros f1 Hf1 f2 Hf2 g Hg.
    destruct g;
      (try reflexivity; 
        try (apply to_nat_inj in Hg;
             fold enumf in Hg;
             discriminate)).
    unfold enumf in Hg.
    apply to_nat_inj in Hg.
    fold enumf in Hg.
    injection Hg.
    intros Hg'.
    apply to_nat_inj in Hg'.
    injection Hg'.
    intros.
    f_equal.
    apply Hf1; assumption.
    apply Hf2; assumption.

    intros f Hf g Hg.
    destruct g;
      (try reflexivity; 
        try (apply to_nat_inj in Hg;
             fold enumf in Hg;
             discriminate)).
    unfold enumf in Hg.
    apply to_nat_inj in Hg.
    fold enumf in Hg.
    injection Hg.
    intros Hg'.
    f_equal.
    apply Hf; assumption.

    intros p t Ht g Hg.
    destruct g;
      (try reflexivity; 
        try (apply to_nat_inj in Hg;
             fold enumf in Hg;
             discriminate)).
    apply to_nat_inj in Hg.
    injection Hg.
    clear Hg.
    intros Hg'.
    fold enumt in Hg'.
    apply to_nat_inj in Hg'.
    injection Hg'.
    intros H1 H2.
    f_equal.
    2 : { apply Ht; assumption. }
    unfold enump in H2.
    apply to_nat_inj in H2.
    injection H2.
    intro H2'.
    apply enum_predicate_inj.
    assumption.

    intros n s Hs.
    destruct s;
      (try reflexivity; 
        try (apply to_nat_inj in Hs;
             fold enumt in Hs;
             discriminate)).
    simpl in Hs.
    apply to_nat_inj in Hs.
    injection Hs.
    intro H.
    rewrite H.
    reflexivity.

    intros n s Hs.
    destruct s;
      (try reflexivity; 
        try (apply to_nat_inj in Hs;
             fold enumt in Hs;
             discriminate)).
    simpl in Hs.
    apply to_nat_inj in Hs.
    injection Hs.
    intro H.
    rewrite H.
    reflexivity.

    intros c Hc s Hs.
    destruct s;
      (try reflexivity; 
        try (apply to_nat_inj in Hs;
             fold enumt in Hs;
             discriminate)).
    simpl in Hs.
    apply to_nat_inj in Hs.
    injection Hs.
    intro H.
    f_equal.
    apply Hc; assumption.

    intros f t Ht s Hs.
    destruct s;
      (try reflexivity; 
        try (apply to_nat_inj in Hs;
             fold enumt in Hs;
             discriminate)).
    simpl in Hs.
    apply to_nat_inj in Hs.
    injection Hs.
    intro Hs'.
    apply to_nat_inj in Hs'.
    injection Hs'.
    intros H1 H2.
    f_equal.
    unfold enumfunc in H2.
    apply to_nat_inj in H2.
    injection H2.
    intro H2'.
    apply enum_function_inj; assumption.    
    apply Ht; assumption.
    
    intros c k Hk.
    destruct k;
      (try reflexivity; 
        try (apply to_nat_inj in Hk;
             fold enumt in Hk;
             discriminate)).
    f_equal.
    unfold enumc in Hk.
    apply to_nat_inj in Hk.
    injection Hk.    
    intro Hk'.
    unfold enumc0 in Hk'.
    apply to_nat_inj in Hk'.
    injection Hk'.    
    intro Hk''.
    apply enum_constant0_inj; assumption.

    intros f Hf k Hk.
    destruct k;
      (try reflexivity; 
        try (apply to_nat_inj in Hk;
             fold enumt in Hk;
             discriminate)).
    f_equal.
    unfold enumc in Hk.
    fold enumf in Hk.
    apply to_nat_inj in Hk.
    injection Hk.    
    intro Hk'.
    apply Hf; assumption.
  Qed.

  Definition enum := enumf.

  Definition countable : forall x y, enum x = enum y -> x = y
    := proj1 countable_ftc.

End Enumeration.

Definition eq_B_join_morph := join_morphism_Proper.
Definition eq_B_meet_morph := meet_morphism_Proper.
Definition bott := bot.
Definition B := formula.

End CBAproof.

(** Various lemmas that have to do with general lists or their
   interaction with proofs *)
Section list_proof_lemmas.
  
  (* a finite list of formulas is included in a set of formulas *)
  Definition included (Gamma:list formula)(T:formula_set) := 
    forall f, In f Gamma -> T f.

  Lemma nil_included : forall Ax, included nil Ax.
  Proof.
    red.
    simpl.
    intros.
    absurd (False); auto.
  Qed.

  Lemma nil_lem1 : forall l:list formula, incl nil l.
  Proof.
    red.
    simpl.
    intros.
    absurd (False); auto.
  Qed.

  Lemma included_lem1 : forall l1 l2:list formula, forall Ax:formula_set,
    included l1 Ax -> included l2 Ax -> included (l1++l2) Ax.
  Proof.
    unfold included.
    intros.
    destruct (in_app_or l1 l2 f H1); auto.
  Qed.

  Lemma weaken_lem1 : forall Gamma Delta A, incl Gamma Delta ->
    proof Gamma A -> proof Delta A.
  Proof.
    intros.
    generalize dependent Delta.
    induction H0.

    intros.
    apply bot_elim;auto.

    intros.
    apply imp_elim with A; auto.

    intros.
    apply imp_intro; auto.
    apply IHproof.
    clear -H.
    unfold incl in *.
    simpl.
    intros; intuition.

    auto using dneg.

    auto using hypo.

    auto using all_elim.

    eauto using all_intro.

    intros.
    assert (incl Gamma Delta).
    clear -H.
    unfold incl in *.
    simpl in *.
    intros; intuition.
    auto.
  Qed.

End list_proof_lemmas.

(** A couple of lemmas about locally closed formulas *)
Section locl_lemmas.
  Lemma locl_all_neg : forall A, locl (all A) -> locl (all (neg A)).
  Proof.
    unfold locl.
    simpl.
    intros A H.
    assert (H' : forall (n : nat) (t : term), (open_rec (S n) t A) = A).
    intros.
    assert (H1 := H n t).
    congruence.
    intros.
    rewrite H'.
    reflexivity.
  Qed.
  
  Lemma locl_henkin : forall A, 
    locl (all A) -> locl (all (A ==> all A)).
  Proof.
    unfold locl.
    simpl.
    intros A H.
    assert (H' : forall (n : nat) (t : term), (open_rec (S n) t A) = A).
    intros.
    assert (H1 := H n t).
    congruence.
    intros.
    rewrite H'.
    rewrite H'.
    reflexivity.
  Qed.
  
  Lemma locl_henkin_neg : forall A, 
    locl (all A) -> locl (all (neg (A ==> all A))).
  Proof.
    unfold locl.
    simpl.
    intros A H.
    assert (H' : forall (n : nat) (t : term), (open_rec (S n) t A) = A).
    intros.
    assert (H1 := H n t).
    congruence.
    intros.
    rewrite H'.
    rewrite H'.
    reflexivity.
  Qed.
End locl_lemmas.

(** This section defines a fixpoint [c_appears] which determines if a
    given constant appears in the formula and then goes on to prove
    that [c_appears f (added (all f)) = false], i.e. that a formula
    cannot contain an added (Henkin) constant indexed by itself. This
    is obvious, but the formal proof proceeds by induction on the
    depth of the formula.

    Another fixpoint [added_cnsts] is also defined, to check if a
    formula contains _any_ added constants and is connected to
    [c_appears].  *)
Section constants_in_formulas.
  Fixpoint c_appears_term (t:term)(c:constant) {struct t} : bool :=
    match t with
      | bvar i    => false
      | fvar x    => false
      | cnst k    => if (constant_dec k c) then true else false
      | func f t1 => c_appears_term t1 c
    end.

  Fixpoint c_appears (t:formula)(c:constant) {struct t} : bool :=
    match t with
      | bot       => false
      | imp t1 t2 => orb (c_appears t1 c) (c_appears t2 c)
      | all t1    => c_appears t1 c
      | atom p t1 => c_appears_term t1 c
    end.
  
  (** c_appears applied to a list *)
  Fixpoint c_appears_l (l:list formula)(c:constant) {struct l} : bool := 
    match l with
      | (cons x x0) => orb (c_appears x c) (c_appears_l x0 c)
      | nil => false
    end.
  
  Fixpoint depth (f:formula) : nat :=
    match f with
      | (atom p t) => depth_term t
      | (all g) => S (depth g)
      | (imp g h) => S (max (depth g) (depth h))
      | bot => 1
    end
  with
    depth_term (t:term) : nat :=
    match t with
      | (func f t') => S (depth_term t')
      | (cnst c) => 
        match c with
          | original k => 1
          | added f => S (depth f)
        end
      | (fvar x) => 1
      | (bvar x) => 1
    end.
  
  Lemma bb''' : forall f g, depth f <= depth g -> c_appears f (added g) = false.
  Proof.
    intros f g H.
    induction f.
    simpl.
    reflexivity.
    simpl.
    simpl in H.
    rewrite Nat.succ_max_distr in H.
    assert (depth f1 <= depth g).
    apply Nat.le_trans with (S (depth f1)).
    auto.
    eapply Nat.le_trans.
    apply Nat.le_max_l.
    apply H.
    assert (depth f2 <= depth g).
    apply Nat.le_trans with (S (depth f2)).
    auto.
    eapply Nat.le_trans.
    apply Nat.le_max_r.
    apply H.
    rewrite IHf1; auto.
    simpl in H.
    simpl.
    rewrite IHf.
    reflexivity.
    apply Nat.le_trans with (S (depth f)).
    auto.
    assumption.
    induction t.
    simpl in *.
    auto.
    simpl in *.
    auto.
    simpl.
    destruct (constant_dec c (added g)).
    rewrite e in H.
    simpl in H.
    contradict H.
    auto with arith.
    reflexivity.
    simpl.
    simpl in IHt.
    rewrite IHt.
    reflexivity.
    simpl in H.
    apply Nat.le_trans with (S (depth_term t)).
    auto.
    assumption.
  Qed.

  Theorem c_appears_thm : forall f, c_appears f (added (all f)) = false.
  Proof.
    intro f.
    apply bb'''.
    simpl.
    auto.
  Qed.

  Lemma c_appears_l_app : forall l1 l2 c, 
    c_appears_l l1 c = false /\ c_appears_l l2 c = false ->
    c_appears_l (l1++l2) c = false.
  Proof.
    induction l1;
      intros l2 c [H1 H2].

    simpl.
    assumption.

    simpl.
    rewrite IHl1.
    simpl in H1.
    apply orb_false_elim in H1.
    destruct H1 as [H11 _].
    rewrite H11.
    auto.
    rewrite H2.
    simpl in H1.
    apply orb_false_elim in H1.
    destruct H1 as [_ H12].
    rewrite H12.
    auto.
  Qed.

  Lemma added_cnsts_c_appears : forall t k,
    added_cnsts t = false -> c_appears_term t (added k) = false.
  Proof.
    induction t; simpl in *; auto.
    intros k H.
    destruct c.
    simpl.
    auto.
    congruence.
  Qed.
  
  (* the formula counterpart to added_cnsts_c_appears (which works
     only on terms) *)
  Lemma added_cnsts_c_appears' : forall f g,
    added_cnsts_f f = false -> c_appears f (added g) = false.
  Proof.
    induction f; simpl.
    
    auto.
    
    intros.
    apply orb_false_elim in H.
    destruct H.
    rewrite IHf1; auto.
    rewrite IHf2; auto.
    
    auto.
    
    apply added_cnsts_c_appears.
  Qed.
End constants_in_formulas.

(** This section provides that if there is a derivation Gamma |- A,
    then there is a derivation Gamma{x/c} |- A{x/c}, where {x/c} is a
    substitution of the constant c by the free variable x. This lemma
    is needed in [henkin_equiconsistent].  *)
Section vanDalen_thm283.
  (* Substituting a constant by a term *)
  Fixpoint c2t_term (t:term)(c:constant)(x:term) {struct t} : term :=
    match t with
      | bvar i    => (bvar i)
      | fvar x    => fvar x
      | cnst k   => if (constant_dec k c) then x else (cnst k)
      | func f t1 => func f (c2t_term t1 c x)
    end.

  Fixpoint
    c2t (t:formula)(c:constant)(x:term)  {struct t} : formula :=
    match t with
      | bot       => bot
      | imp t1 t2 => imp (c2t t1 c x) (c2t t2 c x)
      | all t1    => all (c2t t1 c x)
      | atom p t1 => atom p (c2t_term t1 c x)
    end.
  
  (* c2t applied to a list *)
  Fixpoint c2tl (l:list formula)(c:constant)(v:term) {struct l} := 
    match l with
      | (cons x x0) => (c2t x c v) :: (c2tl x0 c v)
      | nil => nil
    end.
  
  Lemma c2t_idem : forall (f:formula)(c:constant)(x:term),
    c_appears f c = false -> c2t f c x = f.
  Proof.
    induction f.
    simpl.
    auto.
    simpl.
    intros.
    apply orb_false_elim in H.
    destruct H as [H1 H2].
    rewrite IHf1; auto.
    rewrite IHf2; auto.
    simpl.
    intros.
    rewrite IHf; auto.
    induction t.
    simpl.
    auto.
    simpl.
    auto.
    simpl.
    intros.
    destruct (constant_dec c c0).
    congruence.
    auto.
    simpl in *.
    intros.
    assert (c2t_term t c x = t).
    assert (IH := IHt c x H).
    clear IHt.
    congruence.
    rewrite H0.
    reflexivity.
  Qed.
  
  Lemma c2tl_idem : forall (Gamma:list formula)(c:constant)(x:term),
    c_appears_l Gamma c = false ->
    c2tl Gamma c x = Gamma.
  Proof.
    induction Gamma.
    simpl.
    auto.
    simpl.
    intros.
    apply orb_false_elim in H.
    destruct H as [H1 H2].
    rewrite IHGamma;auto.
    rewrite c2t_idem; auto.
  Qed.
  
  Lemma c2t_lem2 : forall (A:formula)(c:constant)(s:term)(t:term),
    c_appears_term t c = false -> loclt s ->
    (c2t A c s) ^^ t = c2t (A ^^ t) c s.
  Proof.
    unfold open.
    generalize 0.
    fix c2t_lem2 2.
    intros.
    destruct A.
    simpl.
    auto.
    simpl.
    rewrite c2t_lem2; auto.
    rewrite c2t_lem2; auto.
    simpl.
    rewrite c2t_lem2; auto.
    idtac.
    induction t0. (* ili treba da bide t? *)
    rewrite c2t_idem; auto.
    rewrite c2t_idem; auto.
    simpl.
    destruct (Nat.eqb n n0).
    assumption.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    unfold loclt in H0.
    destruct (constant_dec c0 c).
    rewrite H0.
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    simpl in IHt0.
    assert (Hr : 
      (open_rec_term n t (c2t_term t0 c s)) = 
      (c2t_term (open_rec_term n t t0) c s)).
    congruence.
    rewrite Hr.
    reflexivity.
  Qed.
  
  Lemma c2t_lem3 : forall (n : nat) (A : formula) (c : constant) (s t : term),
    loclt s ->
    open_rec n (c2t_term t c s) (c2t A c s) = c2t (open_rec n t A) c s.
  Proof.
    fix c2t_lem3 2.
    intros.
    destruct A.
    simpl.
    auto.
    simpl.
    rewrite c2t_lem3.
    rewrite c2t_lem3.
    reflexivity.
    assumption.
    assumption.
    simpl.
    rewrite c2t_lem3; auto.
    induction t0.
    simpl.
    destruct (Nat.eqb n n0).
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    destruct (constant_dec c0 c).
    unfold loclt in H.
    rewrite H.
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    assert ((open_rec_term n (c2t_term t c s) (c2t_term t0 c s))
      = (c2t_term (open_rec_term n t t0) c s)).
    simpl in IHt0.
    congruence.
    rewrite H0.
    reflexivity.
  Qed.
  
  Lemma openrec_lem1 : forall A n t x, 
    open_rec n t (open_rec n (fvar x) A) = 
    open_rec n (fvar x) A.
  Proof.
    induction A; simpl; intros.
    
    reflexivity.
    
    rewrite IHA1.
    rewrite IHA2.
    reflexivity.
    
    rewrite IHA.
    reflexivity.
    
    induction t.
    
    simpl.
    destruct (eq_nat_dec n n0).
    rewrite <- e.
    rewrite Nat.eqb_refl.
    simpl.
    reflexivity.
    destruct Nat.eqb.
    simpl; reflexivity.
    simpl.
    assert (Nat.eqb n n0 = false).
    apply not_true_is_false.
    intro H.
    apply Nat.eqb_eq in H.
    congruence.
    rewrite H.
    reflexivity.
    
    simpl.
    reflexivity.
    
    simpl.
    reflexivity.
    
    simpl.
    congruence.
  Qed.
  
  Lemma locl_all_c2t : forall A, 
    locl A -> 
    forall c x, locl (c2t A c (fvar x)).
  Proof.
    unfold locl.
    intros.
    rewrite <- (H n (fvar x)) at 1.
    rewrite <- c2t_lem3.
    simpl c2t_term.
    rewrite openrec_lem1.
    rewrite <- (H n (fvar x)) at 2.
    clear H.
    generalize dependent n.
    induction A; simpl; intros.
    
    reflexivity.
    
    rewrite IHA1.
    rewrite IHA2.
    reflexivity.
    
    rewrite IHA.
    reflexivity.
    
    induction t0.
    
    simpl.
    destruct Nat.eqb.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    
    simpl.
    reflexivity.
    
    simpl.
    destruct constant_dec.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    
    simpl.
    congruence.
    
    red.
    simpl.
    auto.
  Qed.
  
  Lemma thm283 : forall Gamma f x k,
    proof Gamma f ->
    proof (c2tl Gamma (added k) (fvar x)) (c2t f (added k) (fvar x)).
  Proof.
    intros Gamma f x k H.
    induction H; set (c:=(added k)) in *; simpl; intros.
    
    apply bot_elim.
    simpl c2t in IHproof.
    auto.
    
    simpl c2t in IHproof1.
    apply imp_elim with (c2t A c (fvar x)).
    apply IHproof1.
    auto.
    
    simpl.
    apply imp_intro.
    simpl in IHproof.
    auto.
    
    simpl in IHproof.
    apply dneg.
    auto.
    
    apply hypo.
    induction Gamma.
    simpl in *.
    auto.
    simpl in *.
    destruct H.
    rewrite H.
    left; auto.
    right; auto.
    
    simpl in *.
    unfold open.
    rewrite <- c2t_lem3.
    apply all_elim.
    auto.
    red.
    reflexivity.
    
    apply all_intro with L.
    replace (all (c2t A c (fvar x))) with (c2t (all A) c (fvar x)).
    apply locl_all_c2t; assumption.
    reflexivity.
    intros y yL.
    rewrite c2t_lem2.
    auto.
    simpl.
    reflexivity.
    red; reflexivity.
    
    apply weaken.
    assumption.
  Qed.
  
  Lemma c2t_term_idem : forall c t, c2t_term (cnst c) c t = t.
    intros.
    simpl.
    destruct constant_dec.
    auto.
    congruence.
  Qed.
End vanDalen_thm283.

(** A section implementing the drinker paradox and another lemma, both
   needed in henkin_equiconsistent. *)
Section drinker.

  (** some things are more naturally stated in terms of the
     existential quantifier *)
  Notation "'ex' x" := (neg (all (neg x))) (at level 0).
  
  Lemma ex_intro : forall Delta t f, proof ((f^^t)::Delta) (ex f).
  Proof.
    intros.
    impi.
    impe (f^^t).
    replace (neg (f^^t)) with ((neg f)^^t).
    apply all_elim.
    hypo.
    reflexivity.
    weak; hypo.
  Qed.
  
  Lemma ex_elim : forall Gamma f g, locl (all f) ->
    proof Gamma (neg (all (neg f))) ->
    (forall t, proof ((f^^t)::Gamma) g) -> 
    proof Gamma g.
  Proof.
    intros.
    apply dneg.
    apply imp_intro.
    apply imp_elim with (all (neg f)).
    weak.
    assumption.
    apply all_intro with nil.
    apply locl_all_neg; assumption.
    intros x xL.
    unfold open.
    simpl.
    impi.
    impe g.
    weak; hypo.
    apply weaken_lem1 with ((f^x)::Gamma).
    red; simpl; intuition.
    auto.
  Qed.
  
  Lemma lemma_HE1 : forall Delta h, locl (all (h ==> all h)) ->
    proof Delta ((all (neg (h ==> all h))) ==> (neg ex (h ==> all h))).
  Proof.
    intros.
    impi.
    impi.
    apply ex_elim with (h ==> all h).
    assumption.
    hypo.
    intros.
    impe ((h==>all h)^^t).
    weak; weak.
    replace (neg ((h ==> all h) ^^ t)) with ((neg (h ==> all h)) ^^ t).
    apply all_elim.
    hypo.
    reflexivity.
    hypo.
  Qed.

  (** and we also introduce disjunction *)
  Notation "x \/ y" := ((neg x) ==> y).
    
  Lemma disj_intro1 : forall Gamma f g, proof (f::Gamma) (f \/ g).
  Proof.
    intros.
    impi.
    apply bot_elim.
    impe f.
    hypo.
    weak; hypo.
  Qed.
  
  Lemma disj_intro2 : forall Gamma f g, proof (g::Gamma) (f \/ g).
  Proof.
    intros.
    impi.
    weak; hypo.
  Qed.
  
  Lemma disj_elim : forall Gamma f g h, 
    proof (f::Gamma) h -> proof (g::Gamma) h -> proof Gamma ((f \/ g) ==> h).
  Proof.
    intros.
    impi.
    impe ((neg h ==> h)).
    apply peirce.
    apply proof_imp_trans with f.
    apply proof_imp_trans with (neg g).
    apply proof_imp_contrapos.
    weak; impi; assumption.
    impi.
    dneg.
    impi.
    impe g.
    weak; hypo.
    impe (neg f).
    weak; weak; hypo.
    hypo.
    weak; impi; assumption.
  Qed.
  
  Lemma LEM : forall Gamma f, proof Gamma (f \/ neg f).
  Proof.
    intros.
    impi.
    hypo.
  Qed.
    
  Lemma lemma_HE2_1 : forall h Delta, locl (all h) -> 
    proof (all h::Delta) ex (h ==> all h).
  Proof.
    intros.
    eapply imp_elim.
    impi.
    apply ex_intro.
    assert (Hr:forall t, ((h==>all h)^^t)=((h^^t)==>all h)).
    unfold locl in H.
    unfold open.
    simpl in *.
    intro t.
    rewrite H.
    reflexivity.
    rewrite Hr.
    instantiate (1:=(fvar 0)). (* this has nothing to do with the proof *)
    impi; weak; hypo.
  Qed.
  
  Lemma lemma_HE2_2 : forall h Delta, locl (all h) ->
    proof (neg all h :: Delta) ex (neg h).
  Proof.
    intros.
    impi.
    impe (all h).
    weak; hypo.
    apply all_intro with nil.
    assumption.
    intros x xL.
    dneg.
    replace (neg neg (h^x)) with ((neg neg h)^x).
    apply all_elim.
    hypo.
    reflexivity.
  Qed.
  
  (** Drinker paradox *)
  Lemma lemma_HE2 : forall Delta h, locl (all h) -> 
    proof Delta (ex (h ==> all h)).
  Proof.
    intros.
    eapply imp_elim.
    2 : apply (LEM Delta (all h)).
    apply disj_elim.
    apply lemma_HE2_1.
    assumption.
    apply ex_elim with (neg h).
    apply locl_all_neg; assumption.
    apply lemma_HE2_2.
    assumption.
    intro t.
    impe ((h==>all h)^^t).
    impi.
    apply ex_intro.
    assert (Hr : forall t, ((h==>all h)^^t)=((h^^t)==>all h)).
    intros.
    replace ((h ==> all h) ^^ t0) with ((h^^t0) ==> ((all h)^^t0)).
    unfold locl in H.
    unfold open.
    rewrite H.
    reflexivity.
    auto.
    
    rewrite Hr.
    impi.
    apply bot_elim.
    assert (Hr' : forall t, ((h==>bot)^^t)=((h^^t)==>bot)).
    reflexivity.
    rewrite Hr'.
    impe (h^^t).
    weak; hypo.
    hypo.
  Qed.
End drinker.

(** A predicate for distinguishing Henkin axioms *)
Definition HA := fun f:formula => 
  exists g:formula, f = ((g^^(cnst (added (all g)))) ==> all g)
    /\ locl (all g) /\ added_cnsts_f g = false.

Module DepthOrder <: TotalLeBool.
  Local Coercion is_true : bool >-> Sortclass.

  Definition t := formula.

  (** an order of deeper-than for the indexes of the Henkin
     constants of Henkin axioms; for non-Henkin axioms, no
     behaviour is specified intentionally, but that's not a problem
     because we use this order only for comparing Henkin axioms *)
  (* (depth ((h ^^ cnst (added (all h))) ==> all h) <= depth (all g))%na *)

  Definition leb (a b : formula) : bool := Nat.leb (depth b) (depth a).

  Infix "<=?" := leb (at level 70, no associativity).

  Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
  Proof.
    intros.
    unfold leb.
    destruct (NatOrder.leb_total (depth a2) (depth a1)).
    left; assumption.
    right; assumption.
  Qed.
End DepthOrder.

Module Import DepthSort := Sort DepthOrder.

Section DepthOrder_lemmas.
    Local Coercion is_true : bool >-> Sortclass.

    Lemma leb_transitive : Transitive (fun x y => is_true (DepthOrder.leb x y)).
    Proof.
      unfold Transitive.
      intros.
      unfold DepthOrder.leb in *.
      apply leb_complete in H, H0.
      apply leb_correct.
      eauto using Nat.le_trans.
    Qed.
End DepthOrder_lemmas.

Module CBAproof_completion := filter_completion CBAproof.
Export CBAproof_completion.

Section Completeness.

  (** T1 is an extension of T2, both sets of formulas *)
  Definition extension (T1 T2:formula_set) := forall f, T2 f -> T1 f.

  (** A classical theory is a set of formulas T closed under
      derivation over a set of Axioms *)
  Definition theory (Axioms:formula_set)(T:formula_set) := 
    forall f:formula, 
      (T f <->
        exists Gamma:list formula, 
          (included Gamma Axioms /\ exists p:proof Gamma f, True)).
  
  (** A set of formulas is Henkin-complete if it contains a Henkin
      axiom for every possible locally closed formula in the language
      (regardless whether the formula itself or its universal closure
      is in T or not). *)
  Definition henkin_complete (T:formula_set) := 
    forall f:formula, 
      locl (all f) -> added_cnsts_f f = false ->
      T ((f^^(cnst (added (all f)))) ==> all f).
  
  (** Two sets of formulas being equiconsistent *)
  Definition equicons (X Y:formula_set) := X bot <-> Y bot.

  (** An axiom set is extended with Henkin axioms *)
  Definition AxH (T A:formula_set) := fun f:formula => A f \/ HA f.

  (** A theory that closes the extended axiom set under derivation *)
  Definition TH (T A:formula_set) := fun f:formula =>
    exists Gamma:list formula,
      included Gamma (AxH T A) /\ exists p:proof Gamma f, True.

  (** When an axiom set contains no added constants *)
  Definition noHC (A:formula_set) := forall f, A f -> added_cnsts_f f = false.

  Notation "'ex' x" := (neg (all (neg x))) (at level 0).
  Open Scope type_scope.

  (** If T is a theory over an axiom set which contains no Henkin
      constants, then (TH T) is equiconsistent with T. *)
  Lemma henkin_equiconsistent : forall A T:formula_set, noHC A -> theory A T ->
    (TH T A) bot -> T bot.
  Proof.
    intros A T HcleanA H1 H2.
    destruct H2 as [Gamma H3].
    destruct H3.
    destruct H0 as [p _].
    (* We want to show that if Eta contains a henkin axiom, it can
       be eliminated from the proof. *)
    assert (lemma1:forall h Delta Eta, locl (all h) ->
      c_appears_l Delta (added (all h)) = false ->
      Eta = ((h ^^ cnst (added (all h))) ==> all h)::Delta ->
      proof Eta bot ->
      proof Delta bot
    ).
    { clear.
      intros h Delta Eta closed_h Hc_Delta Hr p.
      rewrite Hr in p.
      clear Hr.
      apply imp_intro in p.
      assert (H : proof Delta (all (neg (h ==> all h)))).
      apply all_intro with nil.
      apply locl_henkin_neg; assumption.
      intros x xL.
      replace (neg ((h ^^ cnst (added (all h))) ==> all h)) 
        with ((neg (h ==> all h)) ^^ cnst (added (all h))) in p.
      assert (p' := thm283 x (all h) p).
      rewrite c2tl_idem in p'; auto.
      unfold open in p'.
      rewrite <- c2t_lem3 in p'; auto.
      rewrite c2t_term_idem in p'.
      rewrite c2t_idem in p'.
      assumption.
      clear.
      simpl.
      rewrite c_appears_thm.
      auto.
      red; reflexivity.
      transitivity (neg ((h ^^ cnst (added (all h))) ==> ((all h) ^^ cnst (added (all h))))).
      reflexivity.
      unfold locl in closed_h.
      unfold open.
      rewrite closed_h.
      reflexivity.
      assert (H0 : proof Delta ((neg (ex (h ==> all h))))).
      eapply imp_elim.
      apply lemma_HE1.
      apply locl_henkin; assumption.
      assumption.
      eapply imp_elim.
      apply H0.
      clear H.
      apply lemma_HE2.
      assumption. }
    (* end of proof of lemma1 *)
    assert (lemma3 : forall Eta, included Eta (AxH T A) ->
      exists E1, exists E2, incl Eta (E1++E2) /\
        included E1 HA /\ included E2 A).
    { clear.
      intros.
      induction Eta.
      exists nil.
      exists nil.
      simpl.
      unfold incl.
      auto using nil_included.
      assert (H1 : included Eta (AxH T A)).
      clear -H.
      unfold included in *.
      intros.
      auto using in_cons.
      destruct (IHEta H1) as [E1 [E2 [H2 [H3 H4]]]].
      assert (H5 : (AxH T A) a).
      red in H.
      apply H.
      apply in_eq.
      unfold AxH in H5.
      destruct H5.
      exists E1.
      exists (a::E2).
      intuition.
      clear -H2.
      red in H2 |- *.
      intros.
      simpl in H.
      destruct H.
      rewrite <- H.
      clear.
      induction E1.
      simpl.
      auto.
      simpl.
      auto.
      assert (H3 := H2 _ H).
      clear -H3.
      induction E1.
      simpl in *; auto.
      simpl in *.
      destruct H3; auto.
      clear - H4 H0.
      red.
      intros.
      simpl in H.
      destruct H.
      rewrite <- H.
      assumption.
      red in H4.
      auto.
      exists (a::E1).
      exists E2.
      intuition.
      simpl.
      clear H5.
      red.
      simpl.
      intros.
      intuition.
      clear -H3 H0.
      red.
      red in H3.
      intros.
      simpl in H.
      destruct H.
      rewrite <- H.
      assumption.
      apply H3.
      assumption. }
    (* end of proof of lemma3 *)
    assert (lemma2 : forall Eta, included Eta (AxH T A) ->
                                 proof Eta bot -> exists Delta, included Delta A * proof Delta bot).
    clear - lemma1 lemma3 HcleanA.
    intros.
    assert (H3 := lemma3 Eta H).
    clear lemma3 H.
    destruct H3 as [E1 [E2 [HEta [HE1 HE2]]]].
    exists E2.
    intuition.
    {
      generalize dependent Eta.
      induction E1.
      - intros.
        simpl in *.
        apply weaken_lem1 with Eta; auto.
      - intros.
        rewrite <- app_comm_cons in HEta.
        assert (HA a).
        { apply HE1.
          left; reflexivity. }
        assert (included E1 HA).
        { intros x Hx.
          apply HE1.
          right; assumption. }
        destruct (in_dec formula_dec a E1).
        {
          eapply IHE1.
          assumption.
          exact H0.
          eapply incl_tran.
          exact HEta.
          unfold incl.
          intros.
          simpl in H2.
          destruct H2.
          - rewrite <- H2.
            eapply in_or_app.
            left; assumption.
          - assumption.
        }
        {
          unfold HA in H.
          destruct H as [h [Hh1 [Hh2 Hh3]]].
          eapply IHE1.
          + clear - HE1.
            intros x Hx.
            apply HE1.
            right; assumption.
          + eapply (lemma1 h (E1++E2)).
            * assumption.
            * clear dependent Eta.
              clear lemma1 IHE1.
              apply c_appears_l_app.
              split.
              { induction E1.
                simpl in *.
                reflexivity.
                simpl in *.
                rewrite IHE1.
                apply orb_false_intro; try reflexivity.
                assert (HA a0).
                apply HE1.
                right; left; reflexivity.
                destruct H as [g [Hg1 [Hg2 Hg3]]].
                rewrite Hg1.
                {
                  clear - Hh1 n Hg1 Hg2 Hg3.
                  assert (~ (a0 = a)); intuition.
                  rewrite Hh1, Hg1 in H.
                  clear H0 H1 Hh1 Hg1.
                  assert (~ (g = h)).
                  { clear - H.
                    intro H1.
                    rewrite H1 in H.
                    auto.
                  }
                  clear H.
                  simpl.
                  apply orb_false_intro.
                  2 : {
                    apply added_cnsts_c_appears'.
                    assumption.
                  }
                  {
                    apply (added_cnsts_c_appears' g (all h)) in Hg3.
                    assert ((added (all g)) <> (added (all h))).
                    { intro H.
                      injection H.
                      assumption.
                    }
                    clear H0.
                    remember (added (all h)) as ch.
                    remember (added (all g)) as cg.
                    clear Heqcg Heqch.
                    clear Hg2.
                    unfold open.
                    generalize dependent 0.
                    induction g.
                    - simpl in *.
                      reflexivity.
                    - simpl in *.
                      intro n.
                      rewrite IHg1.
                      rewrite IHg2.
                      reflexivity.
                      apply orb_false_elim in Hg3.
                      apply Hg3.
                      apply orb_false_elim in Hg3.
                      apply Hg3.
                    - simpl in *.
                      intro n.
                      apply IHg.
                      assumption.
                    - simpl in *.
                      intro n.
                      induction t.
                      + simpl in *.
                        destruct (n =? n0).
                        * simpl in *.
                          remember (constant_dec cg ch) as d.
                          destruct d.
                          congruence.
                          reflexivity.
                        * simpl in *.
                          reflexivity.
                      + simpl in *.
                        reflexivity.
                      + simpl in *.
                        assumption.
                      + simpl in *.
                        auto.
                  }
                }
                intros x Hx.
                apply HE1.
                destruct Hx.
                rewrite H; left; reflexivity.
                right; right; assumption.
                intros x Hx.
                apply H1.
                right; assumption.
                clear - n.
                intuition.
              }
              {
                clear - HcleanA HE2.
                unfold noHC in HcleanA.
                induction E2.
                - simpl.
                  reflexivity.
                - simpl.
                  rewrite IHE2.
                  apply orb_false_intro; try reflexivity.
                  apply added_cnsts_c_appears'.
                  apply HcleanA.
                  apply HE2.
                  left; reflexivity.
                  intros x Hx.
                  apply HE2.
                  right; assumption.
              }
            * reflexivity.
            * eapply weaken_lem1.
              rewrite <- Hh1.
              exact HEta.
              assumption.
          + apply incl_refl.
        }
    }
    assert (H2 := lemma2 Gamma H p).
    clear lemma2.
    apply (proj2 (H1 bot)).
    destruct H2 as [Delta [H2 H3]].
    exists Delta.
    intuition.
    exists H3.
    constructor.
  Qed.

  (** If T is a theory whose axiom set has no Henkin constants, then
     (TH T) is a theory which is Henkin-complete and equiconsistent
     with T. *)
  Theorem enrich : forall T A:formula_set, noHC A -> theory A T -> 
    extension (AxH T A) A /\ extension (TH T A) T /\
    theory (AxH T A) (TH T A) /\ henkin_complete (TH T A) /\ equicons (TH T A) T.
  Proof.
    intros T A AnoHC TAtheory.
    (* (TH T A) is an extension of T *)
    assert (extAxH : extension (AxH T A) A).
      unfold extension.
      red.
      intuition.
    assert (extTHT : extension (TH T A) T).
    unfold extension.
    red.
    intros f Tf.
    unfold theory in TAtheory.
    assert (H1 := proj1 (TAtheory f) Tf).
    destruct H1 as [Gamma HGamma].
    exists Gamma.
    destruct HGamma as [HG1 HG2].
    split.
    unfold included in HG1 |- *.
    unfold extension in extAxH.
    auto.
    exact HG2.
    intuition.
    (* (TH T A) is a theory with axiom set (AxH T A) *)
    unfold theory.
    intros f.
    split.
    intro HT.
    destruct HT as [Gamma HGamma].
    exists Gamma.
    split.
    intuition.
    intuition.
    intros.
    unfold TH.
    exact H.
    (* (TH T A) is henkin_complete *)
    unfold henkin_complete.
    intros f.
    exists (((f ^^ cnst (added (all f))) ==> all f)::nil).
    split.
    red.
    unfold AxH.
    intros.
    right.
    unfold HA.
    exists f.
    simpl in H1.
    intuition.
    assert (p : proof (((f ^^ cnst (added (all f))) ==> all f) :: nil)
      ((f ^^ cnst (added (all f))) ==> all f)).
    hypo.
    exists p.
    auto.
    (* (TH T A) and T are equiconsistent *)
    red.
    split; intros.
    apply (@henkin_equiconsistent A T AnoHC TAtheory).
    assumption.
    intuition.
  Qed.

  (** A theory is also a filter *)
  Theorem theory2filter : forall T Ax, theory Ax T -> Filter T.
  Proof.
    simpl.
    intros T Ax HT.
    unfold formula_set in *.
    unfold theory in *.
    constructor.
    (* a theory is nonempty, it contains top *)
    exists top.
    simpl.
    assert (H := proj2 (HT (neg bot))).
    apply H.
    clear HT H.
    exists (@nil formula).
    split.
    apply nil_included.
    assert (proof nil (neg bot)).
    apply imp_intro.
    apply hypo.
    simpl.
    auto.
    exists H; auto.
    (* a theory is closed under the ordering induced by the boolean algebra *)
    intros.
    red in H0.
    destruct H0.
    clear H0.
    destruct H1.
    assert (H' := proj1 (HT (x)) H).
    destruct H'.
    destruct H1.
    destruct H2.
    generalize dependent (x).
    generalize dependent (y).
    clear -HT H1.
    intros Y X FX H2 H3.
    assert (HT' := HT Y).
    assert (HT'' := proj2 HT').
    clear HT HT'.
    apply HT''.
    clear HT''.
    exists x1.
    split.
    assumption.
    assert (proof x1 Y).
    dneg.
    impi.
    impe (X ==> neg Y).
    impe X.
    apply weaken_lem1 with (@nil formula).
    apply nil_lem1.
    assumption.
    weak;assumption.
    impi.
    weak;hypo.
    exists H;auto.
    (* a theory is closed under finite meets *)
    intros.
    assert (H1 := proj1 (HT (x)) H).
    assert (H2 := proj1 (HT (y)) H0).
    destruct H1.
    destruct H2.
    simpl.
    generalize dependent (x).
    generalize dependent (y).
    clear -HT.
    intros Y FY H1 X FX H2.
    assert (HT' := HT (neg (X ==> neg Y))).
    assert (HT'' := proj2 HT').
    apply HT''.
    clear HT HT' HT''.
    exists (x0++x1).
    split.
    firstorder using included_lem1 || (* 8.1 *) firstorder with included_lem1.
    destruct H1 as [H21 H22].
    destruct H2 as [H51 H52].
    destruct H22 as [p1 _].
    destruct H52 as [p2 _].
    assert (proof (x0++x1) (neg (X ==> neg Y))).
    clear -p1 p2.
    impi.
    impe Y.
    impe X.
    hypo.
    weak.
    apply weaken_lem1 with x0.
    apply incl_appl.
    apply incl_refl.
    assumption.
    weak.
    apply weaken_lem1 with x1.
    apply incl_appr.
    apply incl_refl.
    assumption.
    exists H; auto.
  Qed.

  (** A subsection which implements the model existence lemma by using
     [enrich] and the ultrafilter Z from filters.v *)
  Section model_existence.
    Variables (T Ax:formula_set)(AxnoHC:noHC Ax)(Ttheory:theory Ax T).

    (** A Henkin extension of T *)
    Definition T1 : formula -> Prop := TH T Ax.
    Definition Ax1 : formula -> Prop := AxH T Ax.
    Definition T1theory := (proj1 (proj2 (proj2 (enrich AxnoHC Ttheory)))).
    Definition T1filter : Filter T1 := theory2filter T1theory.

    (** Extend T1 to a meta-dn filter using the Z defined in filters.v *)
    Definition Z' := Z T1.
    
    (** The properties of Z, proved in thm22 in filters.v *)
    Definition lem15 := thm22 T1filter.
    
    Lemma model_existence1 : extension Z' T /\ equicons T Z'.
    Proof.
      intros.
      assert (Hext : extension Z' T).
      unfold Z', Z in *.
      unfold extension.
      intros.
      exists 0.
      simpl.
      unfold T1.
      simpl.
      unfold TH.
      destruct (Ttheory f).
      clear H1.
      destruct (H0 H).
      destruct H1.
      exists x.
      intuition.
      clear -H1.
      unfold AxH.
      unfold included in *.
      intros.
      left.
      auto.
      intuition.
      (* equiconsistency: *)
      red.
      set (HT1 := enrich AxnoHC Ttheory).
      destruct HT1.
      destruct H0.
      destruct H1.
      destruct H2.
      assert (HZ:=lem15).
      destruct HZ.
      destruct H5.
      red in H5.
      unfold inconsistent in H5.
      intuition.
      apply (@henkin_equiconsistent Ax T).
      assumption.
      assumption.
      unfold T1 in *.
      assumption.
    Qed.

    (** An abbreviation for F_n which lives in formula->Prop *)
    Definition G := F_ T1.

    (** The accompanying axioms *)
    Fixpoint GAx (n':nat) : formula -> Prop :=
      match n' with
        | O => Ax1
        | S n => 
          let Fn := F_ T1 n
            in fun f:formula => 
                GAx n f \/ 
                enum f = n /\
                equiconsistent Fn (up (union_singl Fn f))
      end.

    (* The system of axioms for the complete filter Z *)
    Definition ZAx := fun f:formula => exists n:nat, GAx n f.

    Lemma GAx_monotone : forall n m:nat, le n m -> 
      forall f, GAx n f -> GAx m f.
    Proof.
      intros.
      induction H.
      assumption.
      simpl.
      left.
      assumption.
    Qed.

    Lemma remove_In_neq_In : forall ys y xn, 
      In y ys -> y <> xn -> In y (remove id_B_dec xn ys).
    Proof.
      induction ys; intros.
      simpl in *.
      contradiction.
      simpl in *.
      destruct H.
      destruct id_B_dec.
      congruence.
      simpl.
      intuition.
      destruct id_B_dec.
      auto.
      simpl.
      right.
      auto.
    Qed.

    Lemma proof_fold_left : forall Gamma f,
      proof Gamma f -> fold_left meet Gamma top <= f.
    Proof.
      intro Gamma.
      induction Gamma.
      simpl.
      intros.
      unfold leq.
      unfold eq_B.
      split.
      assert (p: proof nil (top && f ==> top)).
      unfold meet.
      unfold top.
      impi.
      impi.
      hypo.
      exists p;constructor.
      assert (p:proof nil (top ==> top&&f)).
      unfold meet.
      impi.
      impi.
      impe f.
      impe top.
      hypo.
      weak;hypo.
      weak;weak;assumption.
      exists p;constructor.
      intros.
      apply imp_intro in H.
      assert (IH := IHGamma _ H).
      clear -IH.
      rewrite fold_left_meet_cons.
      set (phi := fold_left meet Gamma top) in *.
      unfold leq in *.
      unfold eq_B in *.
      split.
      assert (forall a b, proof nil (meet a b ==> a)).
      clear.
      intros.
      unfold meet.
      impi.
      dneg.
      impi.
      impe (a ==> neg b).
      weak; hypo.
      impi.
      apply bot_elim.
      impe a.
      weak;hypo.
      hypo.
      assert (p : proof nil (a && phi && f ==> a && phi)).
      apply H.
      exists p.
      constructor.
      destruct IH as [[H1 _] [H2 _]].
      assert (proof nil (a && phi ==> a && phi && f)).
      assert (forall a b Delta, proof Delta (a ==> b) -> proof Delta (a ==> meet a b)).
      intros.
      unfold meet.
      impi.
      impi.
      impe b.
      impe a0.
      hypo.
      weak;hypo.
      impe a0.
      weak;weak;assumption.
      weak;hypo.
      apply H.
      clear -H2.
      unfold meet in *.
      impi.
      dneg.
      impi.
      impe (a ==> neg phi).
      weak; hypo.
      impi.
      impi.
      impe (phi ==> neg (a ==> f)).
      apply weaken_lem1 with (phi::nil).
      red.
      simpl.
      intuition.
      impe phi.
      weak; assumption.
      hypo.
      impi.
      impi.
      impe f.
      weak;weak;weak;weak;hypo.
      impe a.
      hypo.
      weak;weak;weak;hypo.
      exists H.
      constructor.
    Qed.

    Lemma fold_left_proof : forall Gamma f,
      fold_left meet Gamma top <= f -> proof Gamma f.
    Proof.
      intro Gamma.
      induction Gamma.
      simpl.
      intros f H.
      unfold leq,eq_B in H.
      destruct H as [[p1 _] [p2 _]].
      clear -p2.
      unfold meet in *.
      dneg.
      impi.
      impe (top ==> neg f).
      impe top.
      weak; assumption.
      impi; hypo.
      impi;weak;hypo.
      intros f H.
      rewrite fold_left_meet_cons in H.
      assert (IH:=IHGamma (imp a f)).
      impe a.
      2 : hypo.
      weak.
      apply IH.
      clear -H.
      set (phi := fold_left meet Gamma top) in *.
      unfold leq,eq_B in H |- *.
      destruct H as [[p1 _] [p2 _]].
      split.
      clear.
      assert (p:proof nil (phi && (a ==> f) ==> phi)).
      unfold meet.
      impi.
      dneg.
      impi.
      impe (phi==>neg(a==>f)).
      weak;hypo.
      impi.
      apply bot_elim.
      impe phi.
      weak;hypo.
      hypo.
      exists p;constructor.
      assert (p:proof nil (phi ==> phi && (a ==> f))).
      impi.
      impi.
      impe (a==>f).
      impe phi.
      hypo.
      weak;hypo.
      impi.
      impe (a&&phi&&f).
      impi.
      unfold meet.
      dneg.
      impi.
      impe (neg (a==>neg phi)==>neg f).
      weak;hypo.
      impi;weak;hypo.
      impe (a&&phi).
      weak;weak;weak;assumption.
      impi.
      impe phi.
      impe a.
      hypo.
      weak;hypo.
      weak;weak;weak;hypo.
      exists p;constructor.
    Qed.

    (** Every filter F_n is also a theory *)
    Lemma F_n_theory : forall n, theory (GAx n) (G n).
    Proof.
      induction n.
      (* base case *)
      unfold G.
      simpl.
      constructor.
      intros.
      assumption.
      intros.
      assert (H2 := proj2 (T1theory f)).
      apply H2.
      clear H2.
      assumption.

      (* induction case *)
      constructor.

      intro H.
      assert (exists Gamma, 
        included Gamma (GAx (S n)) /\ 
        fold_left meet Gamma top <= f
      ).
      simpl in H.
      destruct H as [m [ys [H1 [H2 H3]]]].
      assert (forall y, In y ys -> exists zs, included zs (GAx (S n)) /\
        fold_left meet zs top <= y).
      intros y yys.
      assert (G n y \/ GAx (S n) y).
      assert (H4 := lemma5 _ _ _ H2).
      case H4.
      intro case1.
      left.
      clear -yys case1.
      induction ys.
      simpl in yys.
      contradiction.
      simpl in case1.
      apply lemma61 in case1.
      simpl in yys.
      case yys.
      intro case11.
      rewrite <- case11.
      intuition.
      destruct case1.
      intuition.
      intro case2.
      clear -yys case2.
      destruct case2 as (xn & xnys & nxn & Hfold & Hequi).
      case (formula_dec y xn).
      intro case21.
      right.
      rewrite case21.
      symmetry in nxn.
      simpl.
      intuition.
      intro case22.
      left.
      set (ys' := remove id_B_dec xn ys) in *.
      assert (yys' : In y ys').
      apply remove_In_neq_In; assumption.
      clear -yys' Hfold.
      induction ys'.
      simpl in yys'.
      contradiction.
      simpl in *.
      apply lemma61 in Hfold.
      case yys'.
      intro case221.
      rewrite <- case221.
      intuition.
      intro case222.
      intuition.
      (* *)
      case H.      
      intro case1.
      assert (Hth := proj1 (IHn y) case1).
      clear -Hth.
      simpl.
      destruct Hth as [Gamma [HGamma1 [HGamma2 _]]].
      exists Gamma.
      unfold included in *.
      intuition.
      apply proof_fold_left.
      assumption.
      intro case2.
      exists (y::nil).
      split.
      unfold included.
      simpl In.
      intros yy Hr.
      destruct Hr.
      rewrite <- H0.
      assumption.
      contradiction.
      simpl.
      rewrite meet_top.
      apply leq_refl.
      (* *)
      clear -H H3 IHn.
      assert (exists Gamma : list formula,
        included Gamma (GAx (S n)) /\ fold_left meet Gamma top <= fold_left meet ys top).
      clear H3.
      generalize dependent ys.
      induction ys.
      intros.
      simpl fold_left.
      clear H.
      exists nil.
      split.
      apply nil_included.
      simpl.
      apply leq_refl.
      intros.
      assert (H1 : forall y, In y ys ->
        exists zs : list formula,
          included zs (GAx (S n)) /\ fold_left meet zs top <= y).
      clear -H.
      simpl In in H.
      intros.
      intuition.
      assert (H2 : 
        exists zs : list formula,
          included zs (GAx (S n)) /\ fold_left meet zs top <= a).
      clear -H.
      simpl In in H.
      intros.
      intuition.
      assert (IH := IHys H1).
      clear IHys H H1.
      destruct H2 as (zs & Hzs1 & Hzs2).
      destruct IH as (Gamma & HG1 & HG2).
      exists (zs++Gamma).
      split.
      auto using included_lem1.
      clear -Hzs2 HG2.
      rewrite fold_left_meet_cons.
      rewrite fold_left_app_lem.
      apply meet_leq_compat; assumption. 
      (* *)
      destruct H0 as [Gamma [HG1 HG2]].
      exists Gamma.
      intuition.
      apply leq_trans with (fold_left meet ys top).
      assumption.
      assumption.
      destruct H0 as (Gamma & HG1 & HG2).
      exists Gamma.
      intuition.
      clear -HG2.
      assert (p := fold_left_proof _ HG2).
      exists p.
      constructor.
      (* second direction *)
      intro H.
      simpl in *.
      unfold up at 1.
      destruct H as [Gamma [H01 [H02 _]]].
      exists (length Gamma).
      exists Gamma.
      intuition.
      clear H02.
      induction Gamma.
      simpl in *.
      constructor.
      simpl.
      apply lemma62 ; auto.
      split.
      apply IHGamma.
      clear -H01.
      unfold included in *.
      simpl in *.
      auto.
      clear - H01 IHn.
      unfold included in *.
      simpl in *.
      destruct H01 with a.
      auto.
      left.
      apply (proj2 (IHn a)).
      exists (a::nil).
      split.
      red.
      simpl.
      clear -H.
      intros.
      intuition.
      rewrite <- H1.
      assumption.
      assert (p:proof (a::nil) a).
      hypo.
      exists p; auto.
      right.
      assumption.
      (* now the first subcase *)
      apply proof_fold_left; assumption.
    Qed.

    Theorem Z'theory : theory ZAx Z'.
    Proof.
      constructor.
      intro H0.
      unfold Z' in H0.
      destruct H0 as [n Hn].
      assert (H1 := proj1 (F_n_theory n f)).
      unfold G in H1.
      assert (H3 := H1 Hn).
      clear -H3.
      destruct H3 as [Gamma [H1 H2]].
      exists Gamma.
      intuition.
      clear -H1.
      unfold included in *.
      unfold ZAx.
      intros.
      exists n; auto.
      (* the other direction left (if it's necessary) *)
      intro.
      unfold Z'.
      unfold Z.
      destruct H as [Gamma [H1 [H2 _]]].
      unfold ZAx in H1.
      (* Gamma is a finite list, so there is a maximum n, such that 
         the entire list belongs to (GAx n) *)
      assert (exists m:nat, included Gamma (GAx m)).
      clear -H1.
      unfold included in *.
      induction Gamma.
      simpl in *.
      exists 0.
      intuition.
      assert ((forall f : formula, In f Gamma -> exists n : nat, GAx n f)).
      clear -H1.
      simpl in *.
      intros.
      intuition.
      assert (IH := IHGamma H).
      clear H IHGamma.
      destruct IH as [m Hm].
      assert (H1' := H1 a).
      clear H1.
      simpl in *.
      assert (exists n:nat, GAx n a).
      intuition.
      clear H1'.
      destruct H as [n Hn].
      destruct (Compare_dec.le_lt_dec n m).
      assert (H1:=GAx_monotone l).
      exists m.
      intuition.
      rewrite <- H0 in *.
      auto.
      assert (le m n).
      apply Nat.lt_le_incl; assumption.
      assert (H1:=GAx_monotone H).
      exists n.
      intuition.
      rewrite <- H2 in *.
      auto.
      (*  *)
      destruct H as [m Hm].
      exists m.
      assert (H3:=proj2 ((F_n_theory m) f)).
      apply H3.
      exists Gamma.
      intuition.
      exists H2.
      constructor.
    Qed.

    Definition metaDN (X:formula_set) := forall f:formula,
      (X (neg f) -> X bot) -> X f.

    Lemma metaDNZ': metaDN Z'.
    Proof.
      destruct lem15 as [_ [_ H]].
      unfold metaDN.
      intros.
      unfold complete in H.
      unfold Z'.
      assert (H3 := H f).
      clear H.
      unfold element_complete in H3.
      apply H3.
      clear H3.
      unfold equiconsistent.
      split.
      unfold inconsistent.
      intro.
      apply lem223; auto.
      unfold union_singl.
      left; assumption.
      (* the harder direction: *)
      intro.
      unfold inconsistent.
      unfold Z' in H0.
      apply H0.
      clear H0.
      unfold inconsistent in H.
      destruct H as [m Hm].
      destruct Hm as [ys [H3 [H4 H5]]].
      simpl in H5.
      assert (H6 := lemma8 (Z T1) f  ys H4).
      clear H4.
      destruct H6.
      2 : {
      set (z':=(remove id_B_dec f ys)) in *.
      set (z:=fold_left meet z' top) in *.
      assert ((meet f z) <= bott).
      apply leq_trans with (fold_left meet ys top); auto.
      apply leq_trans with (fold_left meet (f::z') top); auto.
      apply eq_B_leq; auto.
      simpl.
      symmetry.
      unfold z.
      apply fold_left_meet_cons; auto.
      apply lemma2; auto.
      unfold z'.
      apply lemma3; auto.
      clear -H0 Ttheory H AxnoHC.
      assert (z <= neg f).
      destruct H0 as [[p1 _] [p2 _]].
      unfold leq.
      unfold eq_B.
      unfold meet.
      split.
      assert (proof nil (neg (z ==> neg neg f) ==> z)).
      impi.
      dneg.
      impi.
      impe (z==>neg neg f).
      weak;hypo.
      impi.
      apply bot_elim.
      impe z.
      weak;hypo.
      hypo.
      exists H0; auto.
      assert (proof nil (z ==> neg (z ==> neg neg f))).
      unfold meet in p2.
      impi.
      impi.
      impe (neg f).
      impe z.
      hypo.
      weak;hypo.
      weak.
      impi.
      impe (neg (f ==> neg z) ==> neg bott).
      impe (neg (f ==> neg z)).
      weak;weak;assumption.
      impi.
      impe z.
      impe f.
      hypo.
      weak;hypo.
      weak;weak;hypo.
      impi.
      weak;weak;weak.
      impi.
      hypo.
      exists H0;auto.
      apply (upwards_closed (proj1 lem15)) with z; auto.
      unfold z.
      apply lemma4; auto.
      apply (proj1 lem15). }
      idtac.
      assert (bott <= neg f).
      apply leq_bott;auto.
      apply (upwards_closed (proj1 lem15)) with bott; auto.
      apply (upwards_closed (proj1 lem15)) with (fold_left meet ys top); auto.
      apply lemma4; auto.
      apply (proj1 lem15).
    Qed.

    Lemma model_existence2 : 
      (forall A B : formula, Z' (A ==> B) -> Z' A -> Z' B) /\
      (forall A B : formula, (Z' A -> Z' B) -> Z' (A ==> B)).
    Proof.
    (* 
       Z is a theory, because it's a filter, so direction => by modus
       ponens. Direction <=:

       Spse Z A implies Z B. To show: Z (A==>B).

       As Z is complete, Meta-DN holds i.e. for all closed C, ((Z ~C)
       -> Z bot) -> Z C. So, we have to show that ((Z ~(A==>B)) -> Z
       bot). From Z ~(A==>B) we get both Z A and Z ~B. From Z A and
       the hypothesis we get Z B, hence Z bot.
    *)
      assert (dir1: forall A B0 : formula, Z' (A ==> B0) -> Z' A -> Z' B0).
      intros.
      apply (proj2 (Z'theory B0)).
      assert (H1':= proj1 (Z'theory _) H).
      assert (H2':= proj1 (Z'theory _) H0).
      clear -H1' H2'.
      destruct H1' as [Gamma1 [H11 H12]].
      destruct H2' as [Gamma2 [H21 H22]].
      exists (Gamma1++Gamma2).
      split.
      red.
      intros.
      destruct (in_app_or Gamma1 Gamma2 f H); auto.
      assert (proof (Gamma1 ++ Gamma2) B0).
      destruct H12 as [p1 _].
      destruct H22 as [p2 _].
      clear -p1 p2.
      impe A.
      apply weaken_lem1 with Gamma1.
      apply incl_appl.
      apply incl_refl.
      assumption.
      apply weaken_lem1 with Gamma2.
      apply incl_appr.
      apply incl_refl.
      assumption.
      exists H; auto.
      split.
      apply dir1.
      (* direction <= *)
      intros.
      apply metaDNZ'.
      intro.
      apply dir1 with B0.
      assert (H2':= proj1 (Z'theory _) H0).
      destruct H2' as [Gamma2 [H21 H22]].
      destruct H22 as [p2 _].
      assert (proof Gamma2 (neg B0)).
      impi.
      impe (A ==> B0).
      weak; assumption.
      impi.
      weak; hypo.
      apply (proj2 (Z'theory (neg B0))).
      exists Gamma2.
      split.
      assumption.
      exists H1; auto.
      apply H.
      assert (H2':= proj1 (Z'theory _) H0).
      destruct H2' as [Gamma2 [H21 H22]].
      destruct H22 as [p2 _].
      assert (proof Gamma2 A).
      dneg.
      impi.
      impe (A ==> B0).
      weak; assumption.
      impi.
      apply bot_elim.
      impe A.
      weak; hypo.
      hypo.
      apply (proj2 (Z'theory A)).
      exists Gamma2.
      split.
      assumption.
      exists H1; auto.
    Qed.

    Lemma model_existence3' : henkin_complete Z'.
    Proof.
      unfold henkin_complete.
      intros.
      unfold Z'.
      assert (T1 ((f ^^ cnst (added (all f))) ==> all f)).
      unfold T1.
      unfold TH.
      exists (((f ^^ cnst (added (all f))) ==> all f) :: nil).
      split.
      unfold AxH.
      red.
      intros.
      right.
      red.
      simpl in H1.
      intuition.
      exists f.
      intuition.
      (* this was repeating a part of the proof of 'enrich' *)
      assert (p : proof (((f ^^ cnst (added (all f))) ==> all f) :: nil)
        ((f ^^ cnst (added (all f))) ==> all f)).
      hypo.
      exists p; auto.
      unfold Z.
      exists 0.
      simpl.
      assumption.
    Qed.

    Lemma model_existence3 :
      (forall A, Z' (all A) -> (forall t:term, Z' (A^^t))) /\
      (forall A, locl (all A) -> added_cnsts_f A = false -> (forall t:term, loclt t -> Z' (A^^t)) -> Z' (all A)).
    Proof.
      assert (Z'imp := proj1 model_existence2).
      split.
      (* first part: Z' is a filter and so a theory. QED by all_elim. *)
      intros.
      apply (proj2 (Z'theory (A^^t))).
      assert (H0' := proj1 (Z'theory _) H).
      clear H.
      destruct H0' as [Gamma [H01 H02]].
      destruct H02 as [H02 _].
      assert (proof Gamma (A ^^ t)).
      apply all_elim.
      assumption.
      exists Gamma.
      intuition.
      exists H; auto.
      (* second part: use henkin completeness *)
      intros.
      apply Z'imp with (A ^^ cnst (added (all A))).
      apply model_existence3'.
      assumption.
      assert (H2 : forall t:term, loclt t -> 
        exists Gamma : list formula,
          included Gamma ZAx /\ exists H : proof Gamma (A^^t), True).
      intros t Hct.
      apply (proj1 (Z'theory (A^^t))).
      auto.
      assumption.
      apply H1.
      red.
      simpl.
      auto.
    Qed.

    Theorem model_existence : extension Z' T /\ model Z' /\ equicons T Z'.
    Proof.
      assert (H1 := model_existence1).
      intuition.
      constructor.
      intros.
      apply (proj2 (Z'theory (neg neg A ==> A))).
      exists (@nil formula).
      split.
      apply nil_included.
      assert (proof nil (neg neg A ==> A)).
      impi.
      dneg.
      hypo.
      exists H1; auto.
      apply (proj1 (model_existence2)).
      apply (proj2 (model_existence2)).
      apply (proj1 (model_existence3)).
      apply (proj2 (model_existence3)).
    Qed.

  End model_existence.

  Fixpoint HCl (A:list formula) : bool := 
    match A with
      | nil => false
      | cons f fs => orb (added_cnsts_f f) (HCl fs)
    end.

  Lemma HCl_correct : forall f Gamma, In f Gamma -> HCl Gamma = false ->
    added_cnsts_f f = false.
  Proof.
    intros.
    induction Gamma.
    contradict H.
    simpl in H0.
    apply orb_false_elim in H0.
    destruct H0.
    simpl in H.
    destruct H.
    rewrite <- H; assumption.
    auto.
  Qed.

  Definition noHCf (f:formula) := added_cnsts_f f = false.
  Definition noHCl (A:list formula) := HCl A = false.

  (** Finally, the completeness theorem. If Gamma and A contain no Henkin constants, that is, if they are built up of/like usual formulas, and if A is true in every model in which Gamma is true, then there is a derivation of A with hypothesis form Gamma. *)
  Theorem completeness : forall Gamma A, noHCl Gamma -> noHCf A ->
    valid Gamma A -> proof Gamma A.
  Proof. 
    intros Gamma A Hno1 Hno2 H.
    set (Ax := fun f:formula => In f Gamma \/ f = neg A).
    set (T := fun f:formula =>
      exists Delta:list formula,
        included Delta Ax /\ exists p:proof Delta f, True).
    assert (noHCAx : noHC Ax).
      clear - Hno1 Hno2.
      unfold noHC,noHCl,noHCf in *.
      intros f H.
      unfold Ax in H.
      destruct H.
      eauto using HCl_correct.
      rewrite H.
      simpl.
      rewrite Hno2.
      auto.
    assert (Ttheory : theory Ax T).
      unfold theory.
      unfold T.
      intuition.
    assert (H1 := model_existence noHCAx Ttheory).
    destruct H1 as [Mext [Mmodel Mequicons]].
    set (M:=Z' T Ax).
    dneg.
    impi.
    assert (T bot).
      assert (M bot).
      apply model_imp_faithful1 with A.
      assumption.
        assert (T (neg A)).
        red.
        exists ((neg A)::nil).
        split.
        red.
        intros.
        simpl in H0.
        red.
        right.
        intuition.
        assert (proof ((neg A) :: nil) (neg A)).
        hypo.
        exists H0.
        auto.
      unfold M.
      intuition.
    red in H.
    assert (H' := H M Mmodel).
    red in H'.
    apply H'.
    intros.
      assert (T f).
      red.
      exists Gamma.
      split.
      red.
      red.
      intuition.
      assert (proof Gamma f).
      hypo.
      exists H1.
      auto.
      unfold M.
      intuition.
    red in Mequicons.
    intuition.
    red in H0.
    destruct H0 as [Delta [H01 H02]].
    destruct H02 as [p _].
    apply weaken_lem1 with Delta.
    clear - H01.
    red.
    intros.
    red in H01.
    simpl.
    case (H01 a H).
    intuition.
    intuition.
    assumption.
  Qed.
  (* Defined. *)

End Completeness.

Check completeness.
(* Set Printing Depth 1000. *)
(* Set Printing Width 1000. *)
(* Print completeness. *)
(* Print model_existence. *)
(* Print henkin_equiconsistent. *)
(* Set Printing All. *)
(* Eval cbv beta delta iota zeta in completeness. *)

End classical_completeness.

