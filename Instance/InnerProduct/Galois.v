(** * The orthogonal complement as a Galois connection *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Grp.Galois.
Require Import Category.Adjunction.Right.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** (A) The orthogonality relation *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record PerpRel@{o} (X : SetoidObject@{o o}) := {
  perp : carrier X → carrier X → Prop;
  perp_sym : ∀ x y, perp x y → perp y x;
  perp_respects : ∀ x x' y y', x ≈ x' → y ≈ y' → perp x y → perp x' y'
}.

Arguments perp {X} p x y.
Arguments perp_sym {X} p x y _.
Arguments perp_respects {X} p x x' y y' _ _ _.

(* The [Proper (equiv ==> equiv ==> iff)] reading, as a theorem rather
   than as a field: the record carries one implication, and both
   directions follow from it by symmetry of [≈]. *)
Lemma perp_respects_iff@{o +} {X : SetoidObject@{o o}} (P : PerpRel@{o} X)
  (x x' y y' : carrier X) (Hx : x ≈ x') (Hy : y ≈ y') :
  perp P x y ↔ perp P x' y'.
Proof.
  split; intro H.
  - exact (perp_respects P x x' y y' Hx Hy H).
  - refine (perp_respects P x' x y' y _ _ H); now symmetry.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (B) The orthogonal complement, and the transposition *)

Section Perp.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Universe o u.
Constraint Set < o.

Context {X : SetoidObject@{o o}}.
Context (P : PerpRel@{o} X).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition perp_set (S : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X).
Proof using P.
  unshelve refine (@Build_SetoidMorphism@{o o o}
    (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
    (fun x => ∀ s, S s → perp P s x) _).
  intros x y Hxy; split; intros H s Hs.
  - refine (perp_respects P s s x y _ Hxy (H s Hs)); reflexivity.
  - refine (perp_respects P s s y x _ _ (H s Hs));
      [ reflexivity | now symmetry ].
Defined.

(* Membership, on the nose.  An equation between [Prop]s, that is between
   OBJECTS of the power set, not between morphisms. *)
Example perp_set_mem (S : carrier (Powerset_Prop_obj@{o} X))
  (x : carrier X) : perp_set S x = (∀ s, S s → perp P s x) := eq_refl.

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition perp_transpose (S T : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le@{o} S (perp_set T)) : subset_le@{o} T (perp_set S) :=
  fun y Hy s Hs => perp_sym P y s (H s Hs y Hy).

(* Order-reversal, in the elementary form.  The connection reads it at
   [op_rel], where it becomes the covariant field the donor record asks
   for. *)
Lemma perp_set_antitone (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le@{o} S T → subset_le@{o} (perp_set T) (perp_set S).
Proof using P. intros H x Hx s Hs; exact (Hx s (H s Hs)). Qed.

(* Both operators of a Galois connection respect the carriers' own [≈];
   here there is one operator, and order-reversal read both ways gives
   it. *)
Lemma perp_set_respects (S T : carrier (Powerset_Prop_obj@{o} X))
  (H : S ≈ T) : perp_set S ≈ perp_set T.
Proof using P.
  apply subset_le_antisym.
  - exact (perp_set_antitone T S (fun x Hx => proj2 (H x) Hx)).
  - exact (perp_set_antitone S T (fun x Hx => proj1 (H x) Hx)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (C) The Galois connection *)

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition perp_galois :
  GaloisConnection (@subset_le@{o} X) (op_rel (@subset_le@{o} X)) :=
  {| gal_l := perp_set
   ; gal_r := perp_set
   ; gal_mono_l := perp_set_antitone
   ; gal_mono_r := fun S T H => perp_set_antitone T S H
   ; gal_to   := fun S T H => perp_transpose T S H
   ; gal_from := fun S T H => perp_transpose S T H |}.

(* MAC LANE'S [L S = R S], as an equation between the two fields. *)
Example perp_galois_l_is_r :
  gal_l perp_galois = gal_r perp_galois := eq_refl.

Example perp_galois_l_is_perp_set :
  gal_l perp_galois = perp_set := eq_refl.

(* The two halves of the biconditional are the same function at swapped
   arguments -- so "if and only if" costs one term, not two. *)
Example perp_to_is_from_swapped (S T : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le@{o} T (perp_set S)) :
  gal_to perp_galois S T H = gal_from perp_galois T S H := eq_refl.

(* The two preorders the connection is read at. *)
Definition perp_PreOrder_l : PreOrder (@subset_le@{o} X) :=
  subset_le_preorder@{o} X.

Definition perp_PreOrder_r : PreOrder (op_rel (@subset_le@{o} X)) :=
  op_PreOrder (subset_le_preorder@{o} X).

(* ------------------------------------------------------------------------ *)
(** ** (D) Mac Lane's display (2), at this connection *)

(* [S] is contained in its double complement.  This is #380's [gal_unit]
   applied; no argument is written here. *)
Definition perp_unit (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le@{o} S (perp_set (perp_set S)) :=
  gal_unit perp_galois perp_PreOrder_r S.

(* The counit, at the SAME type: reading [gal_counit] at the reversed
   order turns it into the very inequality [gal_unit] gives, and the two
   are the same term. *)
Definition perp_counit (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le@{o} S (perp_set (perp_set S)) :=
  gal_counit perp_galois perp_PreOrder_l S.

Example perp_unit_is_counit (S : carrier (Powerset_Prop_obj@{o} X)) :
  perp_unit S = perp_counit S := eq_refl.

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma perp_triple (S : carrier (Powerset_Prop_obj@{o} X)) :
  perp_set (perp_set (perp_set S)) ≈ perp_set S.
Proof using P.
  apply subset_le_antisym.
  - exact (gal_lrl_above perp_PreOrder_r perp_galois S).
  - exact (gal_lrl_below perp_PreOrder_l perp_galois S).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (E) The closed elements *)

(* One inclusion of [S ≈ S^⊥⊥] is free ([perp_unit]), so the predicate
   records only the direction that is not. *)
Definition ClosedPerp (S : carrier (Powerset_Prop_obj@{o} X)) : Prop :=
  subset_le@{o} (perp_set (perp_set S)) S.

(* Section (A)'s two predicates coincide here, since [gal_l] and [gal_r]
   are one map and the second order is the first reversed. *)
Example ClosedPerp_is_GalClosed_r (S : carrier (Powerset_Prop_obj@{o} X)) :
  ClosedPerp S = GalClosed_r perp_galois S := eq_refl.

Example ClosedPerp_is_GalClosed_l (S : carrier (Powerset_Prop_obj@{o} X)) :
  ClosedPerp S = GalClosed_l perp_galois S := eq_refl.

(* Every complement is closed. *)
Definition perp_set_closed (S : carrier (Powerset_Prop_obj@{o} X)) :
  ClosedPerp (perp_set S) :=
  gal_closed_r_image perp_PreOrder_l perp_galois S.

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma closed_perp_iff (S : carrier (Powerset_Prop_obj@{o} X)) :
  ClosedPerp S ↔ ∃ T, perp_set T ≈ S.
Proof using P.
  split.
  - intro H.
    destruct (fst (gal_closed_r_iff perp_PreOrder_l perp_PreOrder_r
                     perp_galois S) H) as [T [H1 H2]].
    exists T; exact (subset_le_antisym H2 H1).
  - intros [T HT].
    refine (snd (gal_closed_r_iff perp_PreOrder_l perp_PreOrder_r
                   perp_galois S) _).
    exists T; exact (fun x Hx => proj2 (HT x) Hx,
                     fun x Hx => proj1 (HT x) Hx).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (F) The two packagings *)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PerpFunctor : Subsets@{o u} X ⟶ Proset@{o u} perp_PreOrder_r :=
  GaloisFunctor_l perp_PreOrder_l perp_PreOrder_r perp_galois.

Definition PerpFunctor_r : Proset@{o u} perp_PreOrder_r ⟶ Subsets@{o u} X :=
  GaloisFunctor_r perp_PreOrder_l perp_PreOrder_r perp_galois.

Definition perp_adjunction : PerpFunctor ⊣ PerpFunctor_r :=
  GaloisAdjunction perp_PreOrder_l perp_PreOrder_r perp_galois.

Example PerpFunctor_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[PerpFunctor] S = perp_set S := eq_refl.

Example PerpFunctor_r_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[PerpFunctor_r] S = perp_set S := eq_refl.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := simpl; repeat intro; exact I.

Program Definition PerpOp :
  (Subsets@{o u} X)^op ⟶ Subsets@{o u} X := {|
  fobj := perp_set;
  fmap := fun S T f => perp_set_antitone T S f
|}.

Program Definition perp_AdjointOnTheRight :
  AdjointOnTheRight PerpOp PerpOp := {|
  aor := fun S T =>
    {| to   := {| morphism := fun h => perp_transpose S T h |}
     ; from := {| morphism := fun h => perp_transpose T S h |} |}
|}.

Example PerpOp_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[PerpOp] S = perp_set S := eq_refl.

(*
   本节说明幺半结构、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example perp_aor_to (S T : carrier (Powerset_Prop_obj@{o} X))
  (h : subset_le@{o} S (perp_set T)) :
  @to Sets _ _ (@aor _ _ _ _ perp_AdjointOnTheRight S T) h
    = perp_transpose S T h := eq_refl.

Example perp_aor_from (S T : carrier (Powerset_Prop_obj@{o} X))
  (h : subset_le@{o} T (perp_set S)) :
  @from Sets _ _ (@aor _ _ _ _ perp_AdjointOnTheRight S T) h
    = perp_transpose T S h := eq_refl.

End Perp.

Arguments perp_set {X} P S.
Arguments ClosedPerp {X} P S.

(* ------------------------------------------------------------------------ *)
(** ** (G) A witness: ℤ² with the dot product *)

(* The setoid of integer pairs, at ONE universe.  [eq_Setoid]
   (Lib/Setoid.v) is polymorphic in exactly the level [Subsets] needs,
   so [≈] here is Leibniz equality and every respectfulness obligation
   below is a substitution. *)
Definition zz_setoid@{wo} : SetoidObject@{wo wo} :=
  {| carrier := (Z * Z)%type ; is_setoid := eq_Setoid@{wo} (Z * Z)%type |}.

(* The ordinary dot product, and the orthogonality relation it induces. *)
Definition zdot (p q : Z * Z) : Prop :=
  (fst p * fst q + snd p * snd q = 0)%Z.

Definition ZZPerp@{wo} : PerpRel@{wo} zz_setoid@{wo}.
Proof.
  unshelve refine (@Build_PerpRel@{wo} zz_setoid@{wo} zdot _ _).
  - intros x y H; unfold zdot in *.
    rewrite (Z.mul_comm (fst y) (fst x)), (Z.mul_comm (snd y) (snd x));
      exact H.
  - intros x x' y y' Hx Hy H; simpl in Hx, Hy; subst; exact H.
Defined.

Example zz_perp_is_dot : perp ZZPerp = zdot := eq_refl.

(* Subsets of ℤ².  Respectfulness is a substitution, [≈] being [eq]. *)
Definition zz_sub@{wo} (p : Z * Z → Prop) :
  carrier (Powerset_Prop_obj@{wo} zz_setoid@{wo}).
Proof.
  unshelve refine (@Build_SetoidMorphism@{wo wo wo}
    (Z * Z)%type (is_setoid zz_setoid@{wo})
    Prop (is_setoid Powerset_Prop_truth@{wo}) p _).
  intros x y Hxy; simpl in Hxy; subst; split; exact (fun h => h).
Defined.

Definition zz_e1@{wo} : carrier (Powerset_Prop_obj@{wo} zz_setoid@{wo}) :=
  zz_sub@{wo} (fun v => v = (1%Z, 0%Z)).

Definition zz_yaxis@{wo} : carrier (Powerset_Prop_obj@{wo} zz_setoid@{wo}) :=
  zz_sub@{wo} (fun v => fst v = 0%Z).

Definition zz_xaxis@{wo} : carrier (Powerset_Prop_obj@{wo} zz_setoid@{wo}) :=
  zz_sub@{wo} (fun v => snd v = 0%Z).

(* THE COMPLEMENT OF THE SINGLETON {(1,0)} IS THE SECOND AXIS.  Both
   inclusions are one instantiation and one arithmetic step. *)
Lemma zz_perp_e1_is_yaxis : perp_set ZZPerp zz_e1 ≈ zz_yaxis.
Proof.
  apply subset_le_antisym.
  - intros x Hx; change (fst x = 0%Z).
    specialize (Hx (1%Z, 0%Z) eq_refl).
    change ((1 * fst x + 0 * snd x)%Z = 0%Z) in Hx; lia.
  - intros x Hx s Hs; change (fst x = 0%Z) in Hx.
    change (s = (1%Z, 0%Z)) in Hs; subst s.
    change ((1 * fst x + 0 * snd x)%Z = 0%Z); lia.
Qed.

(* Two named points, one in the complement and one out of it. *)
Example zz_perp_e1_contains : perp_set ZZPerp zz_e1 (0%Z, 5%Z).
Proof.
  intros s Hs; change (s = (1%Z, 0%Z)) in Hs; subst s.
  change ((1 * 0 + 0 * 5)%Z = 0%Z); reflexivity.
Qed.

Example zz_perp_e1_excludes :
  perp_set ZZPerp zz_e1 (2%Z, 0%Z) → False.
Proof.
  intro H; specialize (H (1%Z, 0%Z) eq_refl).
  change ((1 * 2 + 0 * 0)%Z = 0%Z) in H; lia.
Qed.

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example zz_e1_not_self_perp :
  perp_set ZZPerp zz_e1 (1%Z, 0%Z) → False.
Proof.
  intro H; specialize (H (1%Z, 0%Z) eq_refl).
  change ((1 * 1 + 0 * 0)%Z = 0%Z) in H; lia.
Qed.

(* THE SINGLETON IS NOT CLOSED: its double complement is the first axis,
   which contains [(2,0)]. *)
Lemma zz_double_perp_e1_has_20 :
  perp_set ZZPerp (perp_set ZZPerp zz_e1) (2%Z, 0%Z).
Proof.
  intros s Hs.
  assert (fst s = 0%Z) as Hfs
    by (exact (proj1 (zz_perp_e1_is_yaxis s) Hs)).
  change ((fst s * 2 + snd s * 0)%Z = 0%Z); rewrite Hfs; lia.
Qed.

Theorem zz_e1_not_ClosedPerp : ClosedPerp ZZPerp zz_e1 → False.
Proof.
  intro H; pose proof (H (2%Z, 0%Z) zz_double_perp_e1_has_20) as Hin.
  change ((2%Z, 0%Z) = (1%Z, 0%Z)) in Hin.
  injection Hin; intros; lia.
Qed.

(* THE AXIS IS CLOSED, and the proof exercises the general
   characterisation rather than recomputing: it is a complement, and every
   complement is closed. *)
Theorem zz_yaxis_ClosedPerp : ClosedPerp ZZPerp zz_yaxis.
Proof.
  refine (snd (closed_perp_iff ZZPerp zz_yaxis) _).
  exists zz_e1; exact zz_perp_e1_is_yaxis.
Qed.

(* The complement of the second axis is the first, which pins the double
   complement of the singleton exactly. *)
Lemma zz_perp_yaxis_is_xaxis : perp_set ZZPerp zz_yaxis ≈ zz_xaxis.
Proof.
  apply subset_le_antisym.
  - intros x Hx; change (snd x = 0%Z).
    specialize (Hx (0%Z, 1%Z) eq_refl).
    change ((0 * fst x + 1 * snd x)%Z = 0%Z) in Hx; lia.
  - intros x Hx s Hs; change (snd x = 0%Z) in Hx.
    change (fst s = 0%Z) in Hs.
    change ((fst s * fst x + snd s * snd x)%Z = 0%Z).
    rewrite Hs, Hx; lia.
Qed.

(* The two axes are distinct subsets, so the witness is not degenerate on
   the axis that matters: the complement moves. *)
Example zz_axes_differ : zz_yaxis ≈ zz_xaxis → False.
Proof.
  intro H; pose proof (proj1 (H (0%Z, 1%Z)) eq_refl) as Hin.
  change (1%Z = 0%Z) in Hin; lia.
Qed.
