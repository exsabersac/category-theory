Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Kleisli.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Mon.Coproduct.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Smgrp.

Generalizable All Variables.

(* * * The 幺半群 单子 W₀ algebras （已译） *)

(*
 Book: Awodey, "Category Theory", 1st ed., Carnegie Mellon pre-print,
 Book: Riehl, "Category Theory in Context", Example 5.1.4(ii), printed
 nLab: https://ncatlab.org/nlab/show/free+monoid
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/Kleisli+category

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* Tup0 A 0 = unit and Tup0 A (S n) = Tup A n = A^(n+1). *)
Definition Tup0@{o} (A : Type@{o}) (n : nat) : Type@{o} :=
  match n with
  | O => poly_unit@{o}
  | S n' => Tup@{o} A n'
  end.

(* The letters of a positive tuple, in order. *)
Fixpoint tup_to_list@{o} {A : Type@{o}} (n : nat) : Tup@{o} A n → list A :=
  match n as n0 return Tup A n0 → list A with
  | O => fun a => Datatypes.cons a Datatypes.nil
  | S n' => fun t => Datatypes.cons (fst t) (tup_to_list n' (snd t))
  end.

Definition tup0_to_list@{o} {A : Type@{o}} (n : nat) :
  Tup0@{o} A n → list A :=
  match n as n0 return Tup0 A n0 → list A with
  | O => fun _ => Datatypes.nil
  | S n' => tup_to_list n'
  end.

(* A non-empty list a :: l as a tuple of length (length l) + 1. *)
Fixpoint list_to_tup@{o} {A : Type@{o}} (a : A) (l : list A) :
  Tup@{o} A (length l) :=
  match l as l0 return Tup A (length l0) with
  | Datatypes.nil => a
  | Datatypes.cons b l' => (a, list_to_tup b l')
  end.

Definition list_to_tup0@{o} {A : Type@{o}} (l : list A) :
  Tup0@{o} A (length l) :=
  match l as l0 return Tup0 A (length l0) with
  | Datatypes.nil => ttt
  | Datatypes.cons a l' => list_to_tup a l'
  end.

(* Leibniz: list → tuple → list is the identity. *)
Lemma tup_to_list_list_to_tup@{o} {A : Type@{o}} (a : A) (l : list A) :
  tup_to_list (length l) (list_to_tup a l) = Datatypes.cons a l.
Proof.
  revert a; induction l as [|b l IH]; intro a; simpl; [ reflexivity | ].
  now rewrite IH.
Qed.

Lemma tup0_to_list_list_to_tup0@{o} {A : Type@{o}} (l : list A) :
  tup0_to_list (length l) (list_to_tup0 l) = l.
Proof.
  destruct l as [|a l]; [ reflexivity | apply tup_to_list_list_to_tup ].
Qed.

Lemma tup_to_list_respects@{o} {X : SetoidObject@{o o}} (n m : nat)
  (t : Tup@{o} X n) (u : Tup@{o} X m) :
  tup_eq n m t u → word_eq (tup_to_list n t) (tup_to_list m u).
Proof.
  revert m t u; induction n as [|n IH]; intros [|m] t u H; simpl in *;
    try contradiction.
  - exact (we_cons _ _ _ _ H we_nil).
  - destruct H as [H1 H2]. exact (we_cons _ _ _ _ H1 (IH _ _ _ H2)).
Qed.

Lemma list_to_tup_respects@{o} {X : SetoidObject@{o o}} (a b : X)
  (l l' : list X) :
  a ≈ b → word_eq l l' →
  tup_eq (length l) (length l') (list_to_tup a l) (list_to_tup b l').
Proof.
  intros Hab H; revert a b Hab;
    induction H as [|c d u v Hcd Huv IH]; intros a b Hab; simpl;
    [ exact Hab | ].
  split; [ exact Hab | exact (IH c d Hcd) ].
Qed.

(*
   本节说明 Word 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma list_to_tup_tup_to_list@{o +} {X : SetoidObject@{o o}} (n : nat)
  (t : Tup@{o} X n) :
  match tup_to_list n t return Type@{o} with
  | Datatypes.nil => False
  | Datatypes.cons a l => tup_eq (length l) n (list_to_tup a l) t
  end.
Proof.
  induction n as [|n IH]; simpl; [ reflexivity | ].
  destruct t as [a t']. simpl.
  specialize (IH t').
  destruct (tup_to_list n t') as [|b l]; [ contradiction | ].
  split; [ reflexivity | exact IH ].
Qed.

(* ------------------------------------------------------------------------ *)
(** ** ∐_{n≥0} Xⁿ as a setoid *)

(* 相关说明。 （已译） *)
Definition tup0_eq@{o} {X : SetoidObject@{o o}} (n m : nat) :
  Tup0@{o} X n → Tup0@{o} X m → Type@{o} :=
  match n as n0, m as m0 return Tup0 X n0 → Tup0 X m0 → Type@{o} with
  | O, O => fun _ _ => True
  | S n', S m' => tup_eq n' m'
  | _, _ => fun _ _ => False
  end.

Lemma tup0_eq_refl@{o} {X : SetoidObject@{o o}} (n : nat)
  (t : Tup0@{o} X n) : tup0_eq n n t t.
Proof. destruct n; [ exact Logic.I | apply tup_eq_refl ]. Qed.

Lemma tup0_eq_sym@{o} {X : SetoidObject@{o o}} (n m : nat)
  (t : Tup0@{o} X n) (u : Tup0@{o} X m) :
  tup0_eq n m t u → tup0_eq m n u t.
Proof.
  destruct n, m; simpl; try contradiction;
    [ intros _; exact Logic.I | apply tup_eq_sym ].
Qed.

Lemma tup0_eq_trans@{o} {X : SetoidObject@{o o}} (n m p : nat)
  (t : Tup0@{o} X n) (u : Tup0@{o} X m) (v : Tup0@{o} X p) :
  tup0_eq n m t u → tup0_eq m p u v → tup0_eq n p t v.
Proof.
  destruct n, m, p; simpl; try contradiction; try (intros; exact Logic.I).
  apply tup_eq_trans.
Qed.

Definition Tup0Sum@{o} (X : SetoidObject@{o o}) : Type@{o} :=
  sigT (fun n : nat => Tup0@{o} X n).

Definition Tup0Sum_Setoid@{o} (X : SetoidObject@{o o}) :
  Setoid@{o o} (Tup0Sum@{o} X) :=
  {| equiv := fun w v => tup0_eq (projT1 w) (projT1 v) (projT2 w) (projT2 v)
   ; setoid_equiv :=
       {| Equivalence_Reflexive := fun w => tup0_eq_refl _ (projT2 w)
        ; Equivalence_Symmetric := fun w v =>
            tup0_eq_sym _ _ (projT2 w) (projT2 v)
        ; Equivalence_Transitive := fun w v u =>
            tup0_eq_trans _ _ _ (projT2 w) (projT2 v) (projT2 u) |} |}.

Definition Tup0SumObj@{o} (X : SetoidObject@{o o}) : SetoidObject@{o o} :=
  {| carrier := Tup0Sum@{o} X ; is_setoid := Tup0Sum_Setoid@{o} X |}.

Definition list_to_tup0sum@{o} {X : SetoidObject@{o o}} (l : list X) :
  Tup0Sum@{o} X :=
  existT (fun n => Tup0 X n) (length l) (list_to_tup0 l).

Definition tup0sum_to_list@{o} {X : SetoidObject@{o o}} (w : Tup0Sum@{o} X) :
  list X :=
  tup0_to_list (projT1 w) (projT2 w).

Lemma list_to_tup0sum_respects@{o} {X : SetoidObject@{o o}} (l l' : list X) :
  word_eq l l' →
  tup0_eq (length l) (length l') (list_to_tup0 l) (list_to_tup0 l').
Proof.
  intro H; destruct H as [|a b u v Hab Huv]; [ exact Logic.I | ].
  exact (list_to_tup_respects a b u v Hab Huv).
Qed.

Lemma tup0sum_to_list_respects@{o} {X : SetoidObject@{o o}} (n m : nat)
  (t : Tup0@{o} X n) (u : Tup0@{o} X m) :
  tup0_eq n m t u → word_eq (tup0_to_list n t) (tup0_to_list m u).
Proof.
  destruct n, m; simpl; try contradiction; [ intros _; exact we_nil | ].
  apply tup_to_list_respects.
Qed.

Lemma tup0sum_list_tup0sum@{o} {X : SetoidObject@{o o}}
  (w : Tup0Sum@{o} X) :
  tup0_eq _ _ (list_to_tup0 (tup0sum_to_list w)) (projT2 w).
Proof.
  destruct w as [[|n] t]; [ exact Logic.I | ].
  unfold tup0sum_to_list; simpl.
  pose proof (list_to_tup_tup_to_list n t) as K.
  destruct (tup_to_list n t) as [|a l]; [ contradiction | exact K ].
Qed.

(* 相关说明。 （已译） *)
Definition word0@{o} {A : Type@{o}} : list A := Datatypes.nil.

Definition word1@{o} {A : Type@{o}} (a : A) : list A :=
  Datatypes.cons a Datatypes.nil.

Definition word2@{o} {A : Type@{o}} (a b : A) : list A :=
  Datatypes.cons a (Datatypes.cons b Datatypes.nil).

Lemma word_eq_wapp_nil_r@{o} {X : SetoidObject@{o o}} (l : list X) :
  word_eq (wapp l Datatypes.nil) l.
Proof. rewrite wapp_nil_r. apply word_eq_refl. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** W₀, 单子 伴随 Set ⇀ Mon （已译） *)

Section W0Monad.

Universes o so.

Local Notation MonOS :=
  (@Mon@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).
Local Notation UMonOS :=
  (@Mon_Forget@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).

Definition W0F@{+} : Sets@{o so} ⟶ Sets@{o so} := UMonOS ◯ FreeMonSets.

Definition W0@{+} : @Monad Sets@{o so} W0F :=
  Adjunction_Induced_Monad free_mon_sets_adjunction_hom.

(* μ_X: a word of words, concatenated; the fold of concatenation. *)
Definition wconcat@{+} {X : obj[Sets@{o so}]} (ww : list (list X)) :
  list X :=
  free_mon_extend (L := (FreeMonSetsObject X : obj[MonOS])) (fun w => w) ww.

(* W₀ X is the setoid of words over X. *)
Example W0_obj@{+} (X : obj[Sets@{o so}]) : fobj[W0F] X = WordObj X
  := eq_refl.

Example W0_carrier@{+} (X : obj[Sets@{o so}]) :
  @eq Type@{o} (carrier (fobj[W0F] X)) (list X) := eq_refl.

(* η_X is the insertion of one-letter words, as a setoid map. *)
Example W0_ret@{+} (X : obj[Sets@{o so}]) :
  @ret _ _ W0 X = free_mon_insert X := eq_refl.

Example W0_ret_fun@{+} (X : obj[Sets@{o so}]) (a : X) :
  @ret _ _ W0 X a = word1 a := eq_refl.

(* μ = U ε F. *)
Example W0_join_counit@{+} (X : obj[Sets@{o so}]) :
  @join _ _ W0 X
    = fmap[UMonOS]
        (@counit _ _ _ _ free_mon_sets_adjunction_hom (FreeMonSets X))
  := eq_refl.

(* μ concatenates. *)
Example W0_join_fun@{+} (X : obj[Sets@{o so}]) (ww : list (list X)) :
  @join _ _ W0 X ww = wconcat ww := eq_refl.

Example W0_join_literal@{+} (X : obj[Sets@{o so}]) (a b c : X) :
  @join _ _ W0 X (word2 (word2 a b) (word1 c))
    = Datatypes.cons a (word2 b c) := eq_refl.

Example W0_join_nil@{+} (X : obj[Sets@{o so}]) :
  @join _ _ W0 X word0 = word0 := eq_refl.

(* W₀ f acts letterwise, up to ≈. *)
Lemma W0_map@{+} {X Y : obj[Sets@{o so}]} (f : X ~{Sets@{o so}}~> Y)
  (l : list X) : fmap[W0F] f l ≈ wmap f l.
Proof. exact (free_mon_fmap_is_wmap f l). Qed.

(* W₀ X ≅ ∐_{n≥0} Xⁿ. *)
Definition W0_sum_iso@{+} (X : obj[Sets@{o so}]) :
  @Isomorphism Sets@{o so} (fobj[W0F] X) (Tup0SumObj X).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so} (fobj[W0F] X) (Tup0SumObj X)
       {| morphism := @list_to_tup0sum X |}
       {| morphism := @tup0sum_to_list X |} _ _).
  - intros l l' H. exact (list_to_tup0sum_respects l l' H).
  - intros w v H. exact (tup0sum_to_list_respects _ _ (projT2 w) (projT2 v) H).
  - intro w. exact (tup0sum_list_tup0sum w).
  - intro l. simpl. unfold tup0sum_to_list; simpl.
    rewrite tup0_to_list_list_to_tup0. apply word_eq_refl.
Defined.

(* 相关说明。 （已译） *)
Example W0_sum_iso_to@{+} (X : obj[Sets@{o so}]) (l : list X) :
  to (W0_sum_iso X) l = existT _ (length l) (list_to_tup0 l) := eq_refl.

Example W0_sum_iso_from@{+} (X : obj[Sets@{o so}]) (n : nat)
  (t : Tup0@{o} X n) :
  from (W0_sum_iso X) (existT _ n t) = tup0_to_list n t := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** An algebra 幺半群 (Awodey, Exercise 10.6.6) （已译） *)

Lemma alg_unit@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (a : S) :
  t_alg[α] (word1 a) ≈ a.
Proof. exact (@t_id _ _ _ _ α a). Qed.

(* The action law read on lists: h (map h ww) ≈ h (concat ww). *)
Lemma alg_action@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (ww : list (list S)) :
  t_alg[α] (wmap (t_alg[α]) ww) ≈ t_alg[α] (wconcat ww).
Proof.
  transitivity (t_alg[α] (fmap[W0F] (t_alg[α]) ww)).
  - apply (proper_morphism (t_alg[α])). symmetry.
    exact (@W0_map (fobj[W0F] S) S (t_alg[α]) ww).
  - exact (@t_action _ _ _ _ α ww).
Qed.

(* 相关说明。 （已译） *)
Definition alg_mul@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (a b : S) : S :=
  t_alg[α] (word2 a b).

Definition alg_one@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) : S :=
  t_alg[α] word0.

Lemma alg_mul_respects@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) :
  Proper (equiv ==> equiv ==> equiv) (alg_mul α).
Proof.
  intros a a' Ha b b' Hb. unfold alg_mul.
  apply (proper_morphism (t_alg[α])).
  exact (we_cons _ _ _ _ Ha (we_cons _ _ _ _ Hb we_nil)).
Qed.

(* 相关说明。 （已译） *)
Lemma alg_mul_assoc@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (a b c : S) :
  alg_mul α (alg_mul α a b) c ≈ alg_mul α a (alg_mul α b c).
Proof.
  unfold alg_mul.
  transitivity (t_alg[α] (word2 (t_alg[α] (word2 a b))
                            (t_alg[α] (word1 c)))).
  { apply (proper_morphism (t_alg[α])).
    refine (we_cons _ _ _ _ (reflexivity _) (we_cons _ _ _ _ _ we_nil)).
    symmetry. apply alg_unit. }
  transitivity (t_alg[α] (wconcat (word2 (word2 a b) (word1 c)))).
  { exact (alg_action α (word2 (word2 a b) (word1 c))). }
  transitivity (t_alg[α] (wconcat (word2 (word1 a) (word2 b c)))).
  { reflexivity. }
  transitivity (t_alg[α] (word2 (t_alg[α] (word1 a))
                            (t_alg[α] (word2 b c)))).
  { symmetry. exact (alg_action α (word2 (word1 a) (word2 b c))). }
  apply (proper_morphism (t_alg[α])).
  refine (we_cons _ _ _ _ _ (we_cons _ _ _ _ (reflexivity _) we_nil)).
  apply alg_unit.
Qed.

Lemma alg_one_l@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (a : S) :
  alg_mul α (alg_one α) a ≈ a.
Proof.
  unfold alg_mul, alg_one.
  transitivity (t_alg[α] (word2 (t_alg[α] word0) (t_alg[α] (word1 a)))).
  { apply (proper_morphism (t_alg[α])).
    refine (we_cons _ _ _ _ (reflexivity _) (we_cons _ _ _ _ _ we_nil)).
    symmetry. apply alg_unit. }
  transitivity (t_alg[α] (wconcat (word2 word0 (word1 a)))).
  { exact (alg_action α (word2 word0 (word1 a))). }
  apply alg_unit.
Qed.

Lemma alg_one_r@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (a : S) :
  alg_mul α a (alg_one α) ≈ a.
Proof.
  unfold alg_mul, alg_one.
  transitivity (t_alg[α] (word2 (t_alg[α] (word1 a)) (t_alg[α] word0))).
  { apply (proper_morphism (t_alg[α])).
    refine (we_cons _ _ _ _ _ (we_cons _ _ _ _ (reflexivity _) we_nil)).
    symmetry. apply alg_unit. }
  transitivity (t_alg[α] (wconcat (word2 (word1 a) word0))).
  { exact (alg_action α (word2 (word1 a) word0)). }
  apply alg_unit.
Qed.

(* The monoid of the algebra. *)
Definition alg_monoid@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) : MonOS :=
  mk_mon_obj S (alg_one α) (alg_mul α) (alg_mul_respects α)
    (alg_mul_assoc α) (alg_one_l α) (alg_one_r α).

(* The algebra comes 幺半群: α⟨m1 … mn⟩ ≈ m1 ⋯ mn. （已译） *)
Lemma alg_fold@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (l : list S) :
  free_mon_extend (L := alg_monoid α) (fun x => x) l ≈ t_alg[α] l.
Proof.
  induction l as [|a l IH]; simpl; [ reflexivity | ].
  change (alg_mul α a (free_mon_extend (L := alg_monoid α) (fun x => x) l)
            ≈ t_alg[α] (Datatypes.cons a l)).
  unfold alg_mul.
  transitivity (t_alg[α] (word2 (t_alg[α] (word1 a)) (t_alg[α] l))).
  { apply (proper_morphism (t_alg[α])).
    refine (we_cons _ _ _ _ _ (we_cons _ _ _ _ IH we_nil)).
    symmetry. apply alg_unit. }
  transitivity (t_alg[α] (wconcat (word2 (word1 a) l))).
  { exact (alg_action α (word2 (word1 a) l)). }
  apply (proper_morphism (t_alg[α])).
  exact (we_cons _ _ _ _ (reflexivity a) (word_eq_wapp_nil_r l)).
Qed.

(* ...and no other: 幺半群 same carrier whose products the
 algebra computes has algebra's multiplication unit. （已译） *)
Lemma alg_monoid_unique@{+} (M : MonOS)
  (α : @TAlgebra Sets@{o so} W0F W0 (mon_ob M))
  (H : ∀ l, t_alg[α] l ≈ free_mon_extend (L := M) (fun x => x) l) :
  (∀ a b, mon_mul M a b ≈ alg_mul α a b) * (mon_one M ≈ alg_one α).
Proof.
  split.
  - intros a b. unfold alg_mul. rewrite (H (word2 a b)). simpl.
    apply (mon_mul_resp M); [ reflexivity | ].
    symmetry. apply mon_one_r.
  - unfold alg_one. rewrite (H word0). reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The Eilenberg–Moore 范畴 W₀ Mon （已译） *)

Definition W0Alg@{+} : Category@{so o o} :=
  @EilenbergMoore@{so so so o} Sets@{o so} W0F W0.

Definition EM_mon_map@{+} {x y : W0Alg} (f : x ~{W0Alg}~> y) :
  alg_monoid (projT2 x) ~{MonOS}~> alg_monoid (projT2 y).
Proof.
  refine (@mk_mon_hom (alg_monoid (projT2 x)) (alg_monoid (projT2 y))
            (t_alg_hom[f]) (proper_morphism (t_alg_hom[f])) _ _).
  - intros a b.
    transitivity (t_alg[projT2 y] (fmap[W0F] (t_alg_hom[f]) (word2 a b))).
    + exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f (word2 a b)).
    + apply (proper_morphism (t_alg[projT2 y])).
      exact (W0_map (t_alg_hom[f]) (word2 a b)).
  - transitivity (t_alg[projT2 y] (fmap[W0F] (t_alg_hom[f]) word0)).
    + exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f word0).
    + apply (proper_morphism (t_alg[projT2 y])).
      exact (W0_map (t_alg_hom[f]) word0).
Defined.

Definition EM_to_Mon@{+} : W0Alg ⟶ MonOS.
Proof.
  unshelve refine
    (@Build_Functor W0Alg MonOS (fun x => alg_monoid (projT2 x))
       (fun x y f => EM_mon_map f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The comparison functor K : Mon → Set^{W₀}. *)
Definition Mon_K@{+} : MonOS ⟶ W0Alg :=
  EM_Comparison free_mon_sets_adjunction_hom.

(* The algebra round trip, 恒等 component. （已译） *)
Definition Mon_EM_counit_iso@{+} (x : W0Alg) :
  @Isomorphism W0Alg (fobj[Mon_K ◯ EM_to_Mon] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism W0Alg (fobj[Mon_K ◯ EM_to_Mon] x) x
       (@Build_TAlgebraHom Sets@{o so} W0F W0 (projT1 x) (projT1 x)
          (projT2 (fobj[Mon_K ◯ EM_to_Mon] x)) (projT2 x)
          (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} W0F W0 (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[Mon_K ◯ EM_to_Mon] x))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro l. simpl.
    transitivity (t_alg[projT2 x] l); [ exact (alg_fold (projT2 x) l) | ].
    apply (proper_morphism (t_alg[projT2 x])).
    symmetry. exact (@fmap_id _ _ W0F (projT1 x) l).
  - intro l. simpl.
    transitivity (t_alg[projT2 x] (fmap[W0F] id l)).
    + apply (proper_morphism (t_alg[projT2 x])).
      symmetry. exact (@fmap_id _ _ W0F (projT1 x) l).
    + symmetry. exact (alg_fold (projT2 x) _).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The 幺半群 round trip, 恒等 component: the
 multiplication comes back x · (y · 1). （已译） *)
Definition Mon_EM_unit_iso@{+} (M : MonOS) :
  @Isomorphism MonOS (fobj[EM_to_Mon ◯ Mon_K] M) M.
Proof.
  unshelve refine
    (@Build_Isomorphism MonOS (fobj[EM_to_Mon ◯ Mon_K] M) M
       (@mk_mon_hom (fobj[EM_to_Mon ◯ Mon_K] M) M (fun a => a)
          (fun a b H => H) _ _)
       (@mk_mon_hom M (fobj[EM_to_Mon ◯ Mon_K] M) (fun a => a)
          (fun a b H => H) _ _) _ _).
  - intros a b. simpl.
    apply (mon_mul_resp M); [ reflexivity | apply mon_one_r ].
  - simpl. reflexivity.
  - intros a b. simpl. symmetry.
    apply (mon_mul_resp M); [ reflexivity | apply mon_one_r ].
  - simpl. reflexivity.
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* Awodey Example 10.7 Riehl Example 5.2.6(iii): K 等价,
 恒等 components both ways. （已译） *)
Definition Mon_EM_equivalence@{+} :
  @EquivalenceOfCategories@{so so so so so o} MonOS W0Alg Mon_K.
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ Mon_K EM_to_Mon _ _).
  - exists (fun x => Mon_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun M => iso_sym (Mon_EM_unit_iso M)).
    intros M N f a. reflexivity.
Defined.

(* Monoids are monadic over Set. *)
Definition Mon_Forget_Monadic@{+} :
  @Monadic@{so so so so so o so so} MonOS Sets@{o so} UMonOS.
Proof.
  exists FreeMonSets.
  exists free_mon_sets_adjunction_hom.
  exact Mon_EM_equivalence.
Defined.

(* 相关说明。 （已译） *)
Definition Mon_EM_iso@{c +} : @Isomorphism Cat@{c so so so o} MonOS W0Alg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c so so so o} MonOS W0Alg Mon_K EM_to_Mon _ _).
  - exists (fun x => Mon_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun M => Mon_EM_unit_iso M).
    intros M N f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** Commuting forgetful 函子 (Awodey §10.3) （已译） *)

Definition W0_Forget@{+} : W0Alg ⟶ Sets@{o so} :=
  @EM_Forget Sets@{o so} W0F W0.

Theorem Mon_K_Forget@{+} : W0_Forget ◯ Mon_K ≈ UMonOS.
Proof. exact (EM_Comparison_Forget free_mon_sets_adjunction_hom). Qed.

Theorem EM_to_Mon_Forget@{+} : UMonOS ◯ EM_to_Mon ≈ W0_Forget.
Proof.
  exists (fun x => iso_id).
  intros x y f a. reflexivity.
Qed.

Example Mon_K_Forget_obj@{+} (M : MonOS) :
  fobj[W0_Forget] (fobj[Mon_K] M) = fobj[UMonOS] M := eq_refl.

Example Mon_K_Forget_map@{+} {M N : MonOS} (f : M ~{MonOS}~> N) :
  fmap[W0_Forget] (fmap[Mon_K] f) = fmap[UMonOS] f := eq_refl.

Example EM_to_Mon_Forget_obj@{+} (x : W0Alg) :
  fobj[UMonOS] (fobj[EM_to_Mon] x) = fobj[W0_Forget] x := eq_refl.

Example EM_to_Mon_Forget_map@{+} {x y : W0Alg} (f : x ~{W0Alg}~> y) :
  fmap[UMonOS] (fmap[EM_to_Mon] f) = fmap[W0_Forget] f := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** The Kleisli 范畴 W₀ (Riehl, Example 5.2.11(ii)) （已译） *)

Definition W0Kl@{+} : Category@{so o o} := @Kleisli Sets@{o so} W0F W0.

(* A Kleisli arrow A ⇝ B is a setoid map A → W₀ B. *)
Example W0Kl_hom@{+} (A B : obj[Sets@{o so}]) :
  @eq Type@{o} (@hom W0Kl A B) (A ~{Sets@{o so}}~> fobj[W0F] B) := eq_refl.

Example W0Kl_homset@{+} (A B : obj[Sets@{o so}]) :
  @homset W0Kl A B = @homset Sets@{o so} A (fobj[W0F] B) := eq_refl.

Example W0Kl_id_fun@{+} (A : obj[Sets@{o so}]) (a : A) :
  (@id W0Kl A) a = word1 a := eq_refl.

(* Composition is concatenated mapping, up to ≈. *)
Lemma W0Kl_compose@{+} {A B C : obj[Sets@{o so}]}
  (g : B ~{W0Kl}~> C) (f : A ~{W0Kl}~> B) (a : A) :
  (g ∘[W0Kl] f) a ≈ wconcat (wmap g (f a)).
Proof.
  apply (proper_morphism (@join _ _ W0 C)). exact (W0_map g (f a)).
Qed.

(* A Kleisli arrow A ⇝ B is a setoid map A → ∐_{n≥0} Bⁿ. *)
Definition W0Kl_hom_iso@{+} (A B : obj[Sets@{o so}]) :
  @Isomorphism Sets@{o so}
    {| carrier := @hom W0Kl A B; is_setoid := @homset W0Kl A B |}
    {| carrier := A ~{Sets@{o so}}~> Tup0SumObj B
     ; is_setoid := @homset Sets@{o so} A (Tup0SumObj B) |}.
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so}
       {| carrier := @hom W0Kl A B; is_setoid := @homset W0Kl A B |}
       {| carrier := A ~{Sets@{o so}}~> Tup0SumObj B
        ; is_setoid := @homset Sets@{o so} A (Tup0SumObj B) |}
       {| morphism := fun f => to (W0_sum_iso B) ∘ f |}
       {| morphism := fun g => from (W0_sum_iso B) ∘ g |} _ _).
  - intros f f' H a. exact (proper_morphism (to (W0_sum_iso B)) _ _ (H a)).
  - intros g g' H a. exact (proper_morphism (from (W0_sum_iso B)) _ _ (H a)).
  - intros g a. exact (iso_to_from (W0_sum_iso B) (g a)).
  - intros f a. exact (iso_from_to (W0_sum_iso B) (f a)).
Defined.

Example W0Kl_hom_iso_to@{+} (A B : obj[Sets@{o so}]) (f : A ~{W0Kl}~> B)
  (a : A) :
  to (W0Kl_hom_iso A B) f a = existT _ (length (f a)) (list_to_tup0 (f a))
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks *)

(* The two legs 同构 Cat two 函子. （已译） *)
Example Mon_EM_iso_to@{+} : to Mon_EM_iso = Mon_K := eq_refl.

Example Mon_EM_iso_from@{+} : from Mon_EM_iso = EM_to_Mon := eq_refl.

(* The 幺半群 algebra: carrier, x · y = α⟨x y⟩ 1 = α⟨⟩. （已译） *)
Example alg_monoid_carrier@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) : mon_ob (alg_monoid α) = S
  := eq_refl.

Example alg_monoid_mul@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (a b : S) :
  mon_mul (alg_monoid α) a b = t_alg[α] (word2 a b) := eq_refl.

Example alg_monoid_one@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) :
  mon_one (alg_monoid α) = t_alg[α] word0 := eq_refl.

(* K M ⟨M, U ε_M⟩: structure map fold 恒等, ν₀ the
 unit, νₙ n-fold product, bracketed right unit
 last. （已译） *)
Example Mon_K_carrier@{+} (M : MonOS) :
  projT1 (fobj[Mon_K] M) = mon_ob M := eq_refl.

Example Mon_K_alg@{+} (M : MonOS) :
  t_alg[projT2 (fobj[Mon_K] M)]
    = fmap[UMonOS] (@counit _ _ _ _ free_mon_sets_adjunction_hom M)
  := eq_refl.

Example Mon_K_alg_fun@{+} (M : MonOS) (l : list (mon_ob M)) :
  t_alg[projT2 (fobj[Mon_K] M)] l = free_mon_extend (fun x => x) l
  := eq_refl.

Example Mon_K_nu0@{+} (M : MonOS) :
  t_alg[projT2 (fobj[Mon_K] M)] word0 = mon_one M := eq_refl.

Example Mon_K_nu1@{+} (M : MonOS) (x : mon_ob M) :
  t_alg[projT2 (fobj[Mon_K] M)] (word1 x) = mon_mul M x (mon_one M)
  := eq_refl.

Example Mon_K_nu2@{+} (M : MonOS) (x y : mon_ob M) :
  t_alg[projT2 (fobj[Mon_K] M)] (word2 x y)
    = mon_mul M x (mon_mul M y (mon_one M)) := eq_refl.

Example Mon_K_map@{+} {M N : MonOS} (f : M ~{MonOS}~> N) :
  t_alg_hom[fmap[Mon_K] f] = `1 f := eq_refl.

(* The 幺半群 algebra, through 函子. （已译） *)
Example EM_to_Mon_carrier@{+} (x : W0Alg) :
  mon_ob (fobj[EM_to_Mon] x) = projT1 x := eq_refl.

Example EM_to_Mon_mul@{+} (x : W0Alg) (a b : projT1 x) :
  mon_mul (fobj[EM_to_Mon] x) a b = t_alg[projT2 x] (word2 a b) := eq_refl.

Example EM_to_Mon_one@{+} (x : W0Alg) :
  mon_one (fobj[EM_to_Mon] x) = t_alg[projT2 x] word0 := eq_refl.

Example EM_to_Mon_map@{+} {x y : W0Alg} (f : x ~{W0Alg}~> y) :
  `1 (fmap[EM_to_Mon] f) = t_alg_hom[f] := eq_refl.

(* 相关说明。 （已译） *)
Example Mon_rt_carrier@{+} (M : MonOS) :
  mon_ob (fobj[EM_to_Mon ◯ Mon_K] M) = mon_ob M := eq_refl.

Example Mon_rt_one@{+} (M : MonOS) :
  mon_one (fobj[EM_to_Mon ◯ Mon_K] M) = mon_one M := eq_refl.

Example Mon_rt_mul_fun@{+} (M : MonOS) (a b : mon_ob M) :
  mon_mul (fobj[EM_to_Mon ◯ Mon_K] M) a b
    = mon_mul M a (mon_mul M b (mon_one M)) := eq_refl.

Lemma Mon_rt_mul@{+} (M : MonOS) (a b : mon_ob M) :
  mon_mul (fobj[EM_to_Mon ◯ Mon_K] M) a b ≈ mon_mul M a b.
Proof. exact (mon_mul_resp M _ _ (reflexivity a) _ _ (mon_one_r M b)). Qed.

Example Mon_rt_hom@{+} {M N : MonOS} (f : M ~{MonOS}~> N) :
  mon_fun (fmap[EM_to_Mon ◯ Mon_K] f) = mon_fun f := eq_refl.

Example EM_rt_carrier@{+} (x : W0Alg) :
  projT1 (fobj[Mon_K ◯ EM_to_Mon] x) = projT1 x := eq_refl.

Example EM_rt_alg_fun@{+} (x : W0Alg) (l : list (projT1 x)) :
  t_alg[projT2 (fobj[Mon_K ◯ EM_to_Mon] x)] l
    = free_mon_extend (L := alg_monoid (projT2 x)) (fun s => s) l
  := eq_refl.

Example EM_rt_alg_hom@{+} {x y : W0Alg} (f : x ~{W0Alg}~> y) :
  t_alg_hom[fmap[Mon_K ◯ EM_to_Mon] f] = t_alg_hom[f] := eq_refl.

(* Every component two natural isomorphisms 恒等, at a
 variable 对象, from. （已译） *)
Example Mon_EM_iso_to_from_component@{+} (x : W0Alg) :
  (t_alg_hom[to (projT1 (iso_to_from Mon_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from Mon_EM_iso) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example Mon_EM_iso_from_to_component@{+} (M : MonOS) :
  (mon_fun (to (projT1 (iso_from_to Mon_EM_iso) M)),
   mon_fun (from (projT1 (iso_from_to Mon_EM_iso) M)))
    = ((fun a : mon_ob M => a), (fun a : mon_ob M => a)) := eq_refl.

Example Mon_EM_counit_component@{+} (x : W0Alg) :
  (t_alg_hom[to (projT1 (@equivalence_counit _ _ _ Mon_EM_equivalence) x)],
   t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             Mon_EM_equivalence) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example Mon_EM_unit_component@{+} (M : MonOS) :
  (mon_fun (to (projT1 (@equivalence_unit _ _ _ Mon_EM_equivalence) M)),
   mon_fun (from (projT1 (@equivalence_unit _ _ _ Mon_EM_equivalence) M)))
    = ((fun a : mon_ob M => a), (fun a : mon_ob M => a)) := eq_refl.

End W0Monad.
