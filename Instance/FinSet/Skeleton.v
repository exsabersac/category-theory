Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Theory.Skeleton.

Generalizable All Variables.

(* * * The skeleton 等价: finite setoids finite ordinals （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/equivalence+of+categories

   本文件给出骨架相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab: https://ncatlab.org/nlab/show/skeleton+of+a+category
   nLab: https://ncatlab.org/nlab/show/principle+of+equivalence

   本节说明 Skeleton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition fin_setoid (n : nat) : SetoidObject := {|
  carrier := Fin.t n;
  is_setoid := Fin_Setoid
|}.

(* A setoid map, packaged respectfulness 证明 shape the
 proofs below produce. Nothing here specific finiteness. （已译） *)
Definition setoid_map {X Y : SetoidObject} (f : X → Y)
  (Hf : ∀ a b, a ≈ b → f a ≈ f b) : X ~{Sets}~> Y :=
  Build_SetoidMorphism X (is_setoid X) Y (is_setoid Y) f Hf.

(* On canonical setoids 等价 Leibniz equality, so EVERY
 function between them respectful: 这是 exactly why 含入
 below full. （已译） *)
Definition fin_map {m n : nat} (f : Fin.t m → Fin.t n) :
  fin_setoid m ~{Sets}~> fin_setoid n :=
  setoid_map (X := fin_setoid m) (Y := fin_setoid n) f
    (fun a b H => f_equal f H).

(* 相关说明。 （已译） *)

Fixpoint fin_enum (n : nat) : list (Fin.t n) :=
  match n with
  | O => nil
  | Datatypes.S k => Fin.F1 :: List.map Fin.FS (fin_enum k)
  end.

(* 相关说明。 （已译） *)
Lemma length_of_map {A B : Type} (h : A → B) (l : list A) :
  List.length (List.map h l) = List.length l.
Proof.
  induction l as [| a l IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma fin_enum_length (n : nat) : List.length (fin_enum n) = n.
Proof.
  induction n as [| k IH]; simpl.
  - reflexivity.
  - now rewrite length_of_map, IH.
Qed.

Lemma fin_enum_full {n : nat} (i : Fin.t n) : List.In i (fin_enum n).
Proof.
  induction n as [| k IH].
  - exact (Fin.case0 (fun i => List.In i (fin_enum 0)) i).
  - apply (Fin.caseS' i (fun i => List.In i (fin_enum (Datatypes.S k)))).
    + now left.
    + intro q; right.
      now apply List.in_map.
Qed.

(* Injectivity of [Fin.FS], proved through a local partial inverse rather
   than by [injection] on a dependent constructor, so that it holds by
   plain reduction on every supported version. *)
(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fin_pred_option {n : nat} (i : Fin.t (Datatypes.S n)) : option (Fin.t n) :=
  Fin.caseS' i (fun _ => option (Fin.t n)) None (fun q => Some q).

Lemma FS_injective {n : nat} (x y : Fin.t n) : Fin.FS x = Fin.FS y → x = y.
Proof.
  intro H.
  apply (f_equal fin_pred_option) in H.
  simpl in H.
  now injection H.
Qed.

(* [Fin.FS] is injective, so it carries duplicate-freeness along. *)
Lemma nodup_map_FS {k : nat} (l : list (Fin.t k)) :
  List.NoDup l → List.NoDup (List.map Fin.FS l).
Proof.
  induction l as [| a l IH]; simpl; intro Hnd.
  - constructor.
  - inversion Hnd as [| ? ? Hnotin Hnd']; subst.
    constructor.
    + intro Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as [q [Hq Hq']].
      apply FS_injective in Hq; subst.
      contradiction.
    + now apply IH.
Qed.

Lemma fin_enum_nodup (n : nat) : List.NoDup (fin_enum n).
Proof.
  induction n as [| k IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as [q [Hq _]].
      discriminate Hq.
    + now apply nodup_map_FS.
Qed.

(* Two finite ordinals connected mutually inverse maps have same
 index: each enumeration embeds 进入 image other without
 repetition, so two lengths bound one another. （已译） *)
Lemma fin_bijection_index {m n : nat}
  (f : Fin.t m → Fin.t n) (g : Fin.t n → Fin.t m)
  (fg : ∀ j, f (g j) = j) (gf : ∀ i, g (f i) = i) : m = n.
Proof.
  assert (Hle : ∀ (p q : nat) (u : Fin.t p → Fin.t q) (v : Fin.t q → Fin.t p),
             (∀ j, u (v j) = j) → (q <= p)%nat).
  { intros p q u v uv.
    rewrite <- (fin_enum_length q), <- (fin_enum_length p).
    rewrite <- (length_of_map u (fin_enum p)).
    apply List.NoDup_incl_length.
    - apply fin_enum_nodup.
    - intros j Hj.
      apply List.in_map_iff.
      exists (v j); split; [apply uv | apply fin_enum_full]. }
  apply Nat.le_antisymm.
  - exact (Hle n m g f gf).
  - exact (Hle m n f g fg).
Qed.

(* * ** The 范畴 finite setoids （已译） *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record FinSetoid : Type := {
  fs_obj : SetoidObject;
  fs_card : nat;
  fs_theta : @Isomorphism Sets fs_obj (fin_setoid fs_card)
}.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Set_f : Category := {|
  obj := FinSetoid;
  hom := fun A B => fs_obj A ~{Sets}~> fs_obj B;
  homset := fun A B => @homset Sets (fs_obj A) (fs_obj B);
  id := fun A => @id Sets (fs_obj A);
  compose := fun A B C f g => @compose Sets (fs_obj A) (fs_obj B) (fs_obj C) f g;
  compose_respects := fun A B C =>
    @compose_respects Sets (fs_obj A) (fs_obj B) (fs_obj C);
  id_left := fun A B => @id_left Sets (fs_obj A) (fs_obj B);
  id_right := fun A B => @id_right Sets (fs_obj A) (fs_obj B);
  comp_assoc := fun A B C D =>
    @comp_assoc Sets (fs_obj A) (fs_obj B) (fs_obj C) (fs_obj D);
  comp_assoc_sym := fun A B C D =>
    @comp_assoc_sym Sets (fs_obj A) (fs_obj B) (fs_obj C) (fs_obj D)
|}.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition setf_iso {A B : Set_f}
  (i : @Isomorphism Sets (fs_obj A) (fs_obj B)) : A ≅[Set_f] B :=
  @Build_Isomorphism Set_f A B (to i) (from i)
    (iso_to_from i) (iso_from_to i).

Definition sets_iso {A B : Set_f}
  (i : A ≅[Set_f] B) : @Isomorphism Sets (fs_obj A) (fs_obj B) :=
  @Build_Isomorphism Sets (fs_obj A) (fs_obj B) (to i) (from i)
    (iso_to_from i) (iso_from_to i).

(*
   本节说明 Skeleton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example setf_sets_iso (A B : Set_f) (i : A ≅[Set_f] B) :
  setf_iso (sets_iso i) = i.
Proof. now destruct i. Qed.

Example sets_setf_iso (A B : Set_f)
  (i : @Isomorphism Sets (fs_obj A) (fs_obj B)) :
  sets_iso (@setf_iso A B i) = i.
Proof. now destruct i. Qed.

(* * ** The 含入 finite ordinals （已译） *)

(*
   本节说明 Skeleton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition finset_obj (n : nat) : FinSetoid := {|
  fs_obj := fin_setoid n;
  fs_card := n;
  fs_theta := iso_id
|}.

Program Definition FinSet_Incl : FinSet ⟶ Set_f := {|
  fobj := finset_obj;
  fmap := fun m n f => fin_map f
|}.

(** ** The cardinal functor *)

(*
   本节说明（余）强度、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma theta_to_from {A : Set_f} (i : Fin.t (fs_card A)) :
  to (fs_theta A) (from (fs_theta A) i) = i.
Proof. exact (iso_to_from (fs_theta A) i). Qed.

Lemma theta_from_to {A : Set_f} (a : fs_obj A) :
  from (fs_theta A) (to (fs_theta A) a) ≈ a.
Proof. exact (iso_from_to (fs_theta A) a). Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma card_map_respects {A B : Set_f} (f g : A ~{Set_f}~> B)
  (i : Fin.t (fs_card A)) :
  f ≈ g →
  to (fs_theta B) (f (from (fs_theta A) i))
    = to (fs_theta B) (g (from (fs_theta A) i)).
Proof.
  intro Hfg.
  exact (proper_morphism (to (fs_theta B)) _ _ (Hfg (from (fs_theta A) i))).
Qed.

Lemma card_map_comp {A B C : Set_f} (f : B ~{Set_f}~> C) (g : A ~{Set_f}~> B)
  (i : Fin.t (fs_card A)) :
  to (fs_theta C) (f (g (from (fs_theta A) i)))
    = to (fs_theta C)
        (f (from (fs_theta B) (to (fs_theta B) (g (from (fs_theta A) i))))).
Proof.
  exact (proper_morphism (to (fs_theta C)) _ _
           (proper_morphism f _ _
              (symmetry (theta_from_to (g (from (fs_theta A) i)))))).
Qed.

(* Mac Lane's cardinal functor [#]: on objects the carried index, on
   morphisms [# f = θ_Y ∘ f ∘ θ_X⁻¹].  Definable without any choice
   principle exactly because [fs_theta] is data. *)
Program Definition Card : Set_f ⟶ FinSet := {|
  fobj := fs_card;
  fmap := fun A B f i => to (fs_theta B) (f (from (fs_theta A) i))
|}.
Next Obligation.
  repeat intro.
  now apply card_map_respects.
Qed.
Next Obligation. now apply theta_to_from. Qed.
Next Obligation. now apply card_map_comp. Qed.

(* * ** The 含入 full, faithful 本质满射 （已译） *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FinSet_Incl_Full : @Full FinSet Set_f FinSet_Incl :=
  @Build_Full FinSet Set_f FinSet_Incl
    (fun m n g i => g i)
    (fun m n g i => eq_refl).

Definition FinSet_Incl_Faithful : @Faithful FinSet Set_f FinSet_Incl :=
  @Build_Faithful FinSet Set_f FinSet_Incl (fun m n f g H => H).

Definition FinSet_Incl_EssSurj :
  @EssentiallySurjective FinSet Set_f FinSet_Incl :=
  @Build_EssentiallySurjective FinSet Set_f FinSet_Incl
    fs_card
    (fun A => @setf_iso (finset_obj (fs_card A)) A (iso_sym (fs_theta A))).

(** ** The equivalence *)

(* Mac Lane's example, obtained through general criterion rather than
 hand. This 常值 audit [Print Assumptions]. （已译） *)
Definition FinSet_Setf_Equivalence : EquivalenceOfCategories FinSet_Incl :=
  @FF_ESO_Equivalence FinSet Set_f FinSet_Incl
    FinSet_Incl_Full FinSet_Incl_Faithful FinSet_Incl_EssSurj.

Lemma Card_is_quasi_inverse :
  @quasi_inverse FinSet Set_f FinSet_Incl FinSet_Setf_Equivalence ≈ Card.
Proof.
  exists (fun A => iso_id).
  intros A B f i.
  reflexivity.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Card_quasi_inverse_fobj (A : Set_f) :
  fobj[@quasi_inverse FinSet Set_f FinSet_Incl FinSet_Setf_Equivalence] A
    = fobj[Card] A := eq_refl.

Example Card_quasi_inverse_fmap {A B : Set_f} (f : A ~> B) :
  fmap[@quasi_inverse FinSet Set_f FinSet_Incl FinSet_Setf_Equivalence] f
    = fmap[Card] f := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明 Skeleton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Card_Incl_id : Card ◯ FinSet_Incl ≈ Id[FinSet].
Proof.
  exists (fun n => iso_id).
  intros m n f i.
  reflexivity.
Defined.

Definition Incl_Card_theta : Id[Set_f] ≈ FinSet_Incl ◯ Card.
Proof.
  exists (fun A => @setf_iso A (finset_obj (fs_card A)) (fs_theta A)).
  intros A B f a.
  (* 相关说明。 （已译） *)
  transitivity (f (from (fs_theta A) (to (fs_theta A) a))).
  - exact (proper_morphism f _ _ (symmetry (theta_from_to a))).
  - exact (symmetry
             (theta_from_to (f (from (fs_theta A) (to (fs_theta A) a))))).
Defined.

Definition Card_Equivalence : EquivalenceOfCategories Card :=
  @Build_EquivalenceOfCategories Set_f FinSet Card FinSet_Incl
    Card_Incl_id Incl_Card_theta.

Definition Incl_Card_theta_iso : Id[Set_f] ≅[Fun] FinSet_Incl ◯ Card :=
  equiv_iso Incl_Card_theta.

(** ** Skeletality *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem FinSet_skeletal {m n : FinSet} (i : m ≅ n) : m = n.
Proof.
  exact (fin_bijection_index (to i) (from i) (iso_to_from i) (iso_from_to i)).
Qed.

(** ** Cardinality *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明 Skeleton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition setf_cardinality (A : Set_f) : nat := fs_card A.

Definition setf_cardinality_iso (A : Set_f) : FinSet_Incl (setf_cardinality A) ≅ A :=
  @eso_iso FinSet Set_f FinSet_Incl FinSet_Incl_EssSurj A.

Lemma setf_cardinality_unique (A : Set_f) (n : nat) :
  FinSet_Incl n ≅ A → n = setf_cardinality A.
Proof.
  intro i.
  apply FinSet_skeletal.
  apply (@FullyFaithful FinSet Set_f FinSet_Incl
           FinSet_Incl_Full FinSet_Incl_Faithful).
  exact (iso_compose (iso_sym (setf_cardinality_iso A)) i).
Qed.

Theorem setf_cardinality_iso_invariant (A B : Set_f) :
  A ≅ B → setf_cardinality A = setf_cardinality B.
Proof.
  intro i.
  apply setf_cardinality_unique.
  exact (iso_compose i (setf_cardinality_iso A)).
Qed.

Theorem setf_cardinality_complete (A B : Set_f) :
  setf_cardinality A = setf_cardinality B → A ≅ B.
Proof.
  intro H.
  apply (iso_compose (setf_cardinality_iso B)).
  rewrite <- H.
  exact (iso_sym (setf_cardinality_iso A)).
Qed.

Corollary setf_cardinality_classifies (A B : Set_f) :
  (A ≅ B) ↔ (setf_cardinality A = setf_cardinality B).
Proof.
  split.
  - apply setf_cardinality_iso_invariant.
  - apply setf_cardinality_complete.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Card_Incl_fobj_strict (n : FinSet) : fobj[Card ◯ FinSet_Incl] n = n.
Proof. reflexivity. Qed.

Lemma Card_Incl_fmap_strict {m n : FinSet} (f : m ~> n) :
  fmap[Card ◯ FinSet_Incl] f = f.
Proof. reflexivity. Qed.

Lemma Incl_unit_is_identity (n : FinSet) :
  to (@equivalence_unit_at FinSet Set_f FinSet_Incl FinSet_Setf_Equivalence n)
    = id[n].
Proof. reflexivity. Qed.

(** ** Concrete objects *)

(*
   本节说明 Skeleton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fin_swap2 (i : Fin.t 2) : Fin.t 2 :=
  Fin.caseS' i (fun _ => Fin.t 2) (Fin.FS Fin.F1) (fun _ => Fin.F1).

Lemma fin_swap2_involutive (i : Fin.t 2) : fin_swap2 (fin_swap2 i) = i.
Proof.
  apply (Fin.caseS' i (fun i => fin_swap2 (fin_swap2 i) = i)).
  - reflexivity.
  - intro q.
    apply (Fin.caseS' q
             (fun q => fin_swap2 (fin_swap2 (Fin.FS q)) = Fin.FS q)).
    + reflexivity.
    + intro r.
      exact (Fin.case0
               (fun r => fin_swap2 (fin_swap2 (Fin.FS (Fin.FS r)))
                           = Fin.FS (Fin.FS r)) r).
Qed.

Definition fin_swap2_iso :
  @Isomorphism Sets (fin_setoid 2) (fin_setoid 2) :=
  @Build_Isomorphism Sets (fin_setoid 2) (fin_setoid 2)
    (fin_map fin_swap2) (fin_map fin_swap2)
    fin_swap2_involutive fin_swap2_involutive.

Definition two_swap : FinSetoid := {|
  fs_obj := fin_setoid 2;
  fs_card := 2;
  fs_theta := fin_swap2_iso
|}.

Definition FinSet_swap_iso : @Isomorphism FinSet (2 : nat) (2 : nat) :=
  @Build_Isomorphism FinSet (2 : nat) (2 : nat) fin_swap2 fin_swap2
    fin_swap2_involutive fin_swap2_involutive.

Example FinSet_swap_not_identity :
  to FinSet_swap_iso ≈ @id FinSet (2 : nat) → False.
Proof.
  intro H.
  specialize (H Fin.F1).
  discriminate H.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example FinSet_skeletal_at_swap : (2 = 2)%nat :=
  FinSet_skeletal FinSet_swap_iso.

Example FinSet_one_not_iso_two :
  @Isomorphism FinSet (1 : nat) (2 : nat) → False.
Proof.
  intro i.
  apply FinSet_skeletal in i.
  discriminate i.
Qed.

(* The comparison cell at [two_swap] computes transposition, and
 provably not 恒等 — contrast [Incl_unit_is_identity], which
 holds at EVERY 对象 [FinSet]. （已译） *)
Example counit_at_two_swap :
  to (@equivalence_counit_at FinSet Set_f FinSet_Incl
        FinSet_Setf_Equivalence two_swap) Fin.F1 = Fin.FS Fin.F1.
Proof. reflexivity. Qed.

Example counit_at_two_swap_not_identity :
  to (@equivalence_counit_at FinSet Set_f FinSet_Incl
        FinSet_Setf_Equivalence two_swap) ≈ @id Set_f two_swap → False.
Proof.
  intro H.
  specialize (H Fin.F1).
  simpl in H.
  discriminate H.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Card_two_swap : Card two_swap = 2%nat := eq_refl.

Example Card_conjugates_theta :
  fmap[Card] (fin_map (fun i : Fin.t 2 => i)
                : finset_obj 2 ~{Set_f}~> two_swap) Fin.F1
    = Fin.FS Fin.F1 := eq_refl.

(*
   本节说明 Skeleton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Card_conjugation_moves_constant :
  fmap[Card] (fin_map (fun _ : Fin.t 2 => Fin.F1)
                : two_swap ~{Set_f}~> two_swap) Fin.F1
    = Fin.FS Fin.F1 := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Incl_Card_forgets_theta :
  fs_theta (FinSet_Incl (Card two_swap)) = fs_theta two_swap → False.
Proof.
  intro H.
  apply (f_equal (fun i : @Isomorphism Sets (fin_setoid 2) (fin_setoid 2)
                  => to i Fin.F1)) in H.
  simpl in H.
  discriminate H.
Qed.

(* 相关说明。 （已译） *)

(* [nat] under equality parity: two 等价 classes, infinitely
 many inhabitants. It is 对象 [Set_f] cardinality 2, so
 [Set_f] is not relabelling [FinSet] — cardinal 函子
 computes it.（已译） *)
Program Definition parity_setoid : SetoidObject := {|
  carrier := nat;
  is_setoid := {| equiv := fun x y => Nat.odd x = Nat.odd y |}
|}.

Definition parity_index (i : Fin.t 2) : nat :=
  Fin.caseS' i (fun _ => nat) (0%nat) (fun _ => 1%nat).

Definition parity_enum (x : nat) : Fin.t 2 :=
  if Nat.odd x then Fin.FS Fin.F1 else Fin.F1.

Lemma parity_enum_respects (a b : nat) :
  Nat.odd a = Nat.odd b → parity_enum a = parity_enum b.
Proof. intro H; unfold parity_enum; now rewrite H. Qed.

Lemma parity_index_respects (i j : Fin.t 2) :
  i = j → Nat.odd (parity_index i) = Nat.odd (parity_index j).
Proof. intro H; now subst. Qed.

Lemma parity_to_from (i : Fin.t 2) : parity_enum (parity_index i) = i.
Proof.
  apply (Fin.caseS' i (fun i => parity_enum (parity_index i) = i)).
  - reflexivity.
  - intro q.
    apply (Fin.caseS' q
             (fun q => parity_enum (parity_index (Fin.FS q)) = Fin.FS q)).
    + reflexivity.
    + intro r.
      exact (Fin.case0
               (fun r => parity_enum (parity_index (Fin.FS (Fin.FS r)))
                           = Fin.FS (Fin.FS r)) r).
Qed.

Lemma parity_from_to (a : nat) :
  Nat.odd (parity_index (parity_enum a)) = Nat.odd a.
Proof.
  unfold parity_enum.
  destruct (Nat.odd a) eqn:Ha; now simpl.
Qed.

Definition parity_iso : @Isomorphism Sets parity_setoid (fin_setoid 2) :=
  @Build_Isomorphism Sets parity_setoid (fin_setoid 2)
    (setoid_map (X := parity_setoid) (Y := fin_setoid 2)
       parity_enum parity_enum_respects)
    (setoid_map (X := fin_setoid 2) (Y := parity_setoid)
       parity_index parity_index_respects)
    parity_to_from parity_from_to.

Definition parity_two : FinSetoid := {|
  fs_obj := parity_setoid;
  fs_card := 2;
  fs_theta := parity_iso
|}.

Lemma succ_respects (a b : nat) :
  Nat.odd a = Nat.odd b → Nat.odd (Datatypes.S a) = Nat.odd (Datatypes.S b).
Proof.
  intro H.
  rewrite !Nat.odd_succ, <- !Nat.negb_odd.
  now rewrite H.
Qed.

Definition parity_succ : parity_two ~{Set_f}~> parity_two :=
  setoid_map (X := parity_setoid) (Y := parity_setoid)
    Datatypes.S succ_respects.

(* The carrier [nat]: 对象 [Set_f] finite setoid sense
 — finitely many EQUIVALENCE CLASSES — so carrier type need not be. （已译） *)
(* PROJECTION: identification carriers, holding because [parity_two]
 was built over [parity_setoid] whose carrier is [nat]. It records that a
 two-element 对象 may have 无限 carrier; it proves nothing about
 finiteness witness.（已译） *)
Example parity_carrier_is_nat : carrier (fs_obj parity_two) = nat := eq_refl.

(*
   本节说明 Skeleton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example parity_round_trip_moves_3 :
  parity_index (parity_enum 3) = 1%nat := eq_refl.

(*
   本节说明 Skeleton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example cardinality_parity_two : setf_cardinality parity_two = 2%nat := eq_refl.

Example Card_parity_succ_F1 :
  fmap[Card] parity_succ Fin.F1 = Fin.FS Fin.F1 := eq_refl.

Example Card_parity_succ_FS :
  fmap[Card] parity_succ (Fin.FS Fin.F1) = Fin.F1 := eq_refl.

(* The counit at [parity_two], computed.  Again Leibniz equality of
   natural numbers, strictly stronger than [parity_setoid]'s ≈: the
   component does not merely land in the even class, it returns 0.（标题）（已译） *)
Example counit_at_parity_two :
  to (@equivalence_counit_at FinSet Set_f FinSet_Incl
        FinSet_Setf_Equivalence parity_two) Fin.F1 = 0%nat := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明 Skeleton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem FinSet_Skeletal : Skeletal FinSet.
Proof. intros m n i; exact (FinSet_skeletal i). Qed.

Definition FinSet_Skeleton : Skeleton FinSet :=
  Skeleton_of_Skeletal FinSet_Skeletal.
