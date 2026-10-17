Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.DoubleCategory.
Require Import Category.Theory.DoubleCategory.Companion.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/double+category (Examples)

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Sq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Program Definition trivial_setoid (A : Type) : Setoid A := {|
  equiv := fun _ _ => True
|}.

Local Obligation Tactic := simpl; intros; repeat intro; try exact I.

Program Definition Sq (C : Category) : DoubleCategory := {|
  dcat := C;
  dhor := fun a b => a ~{C}~> b;
  dsq := fun a b c d h u v k => k ∘ u ≈ v ∘ h;
  dsq_setoid := fun a b c d h u v k => trivial_setoid _;
  dhid := fun a => id[a];
  dhcomp := fun a b c g f => g ∘ f
|}.
Next Obligation.
  (* dsq_coerce : k ∘ u' ≈ v' ∘ h from k ∘ u ≈ v ∘ h along u ≈ u', v ≈ v' *)
  now rewrite <- eu, <- ev.
Qed.
Next Obligation.
  (* dsq_vid : h ∘ id ≈ id ∘ h *)
  cat.
Qed.
Next Obligation.
  (* dsq_vcomp : l ∘ (u' ∘ u) ≈ (v' ∘ v) ∘ h *)
  rewrite comp_assoc, X0, <- comp_assoc, X, comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  (* dsq_hcomp : (k' ∘ k) ∘ u ≈ w ∘ (h' ∘ h) *)
  rewrite <- comp_assoc, X, comp_assoc, X0, <- comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  (* dassoc : the globular associator is associativity of C *)
  unshelve eexists.
  { rewrite id_right, id_left.
    symmetry; apply comp_assoc. }
  unshelve eexists.
  { rewrite id_right, id_left.
    apply comp_assoc. }
  split; exact I.
Qed.
Next Obligation.
  (* dunit_left : the globular left unitor is id_left of C *)
  unshelve eexists.
  { cat. }
  unshelve eexists.
  { cat. }
  split; exact I.
Qed.
Next Obligation.
  (* dunit_right : the globular right unitor is id_right of C *)
  unshelve eexists.
  { cat. }
  unshelve eexists.
  { cat. }
  split; exact I.
Qed.

(*
   本节说明 Sq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Sq_DoubleCoerceComp (C : Category) : DoubleCoerceComp (Sq C).
Proof. construct; exact I. Defined.

(*
   本节说明 Sq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Sq_companion {C : Category} {a b : C}
  (u : a ~{C}~> b) : Companion (D:=Sq C) u := {|
  comp_hor := u
|}.
Next Obligation.
  (* comp_unit : u ∘ id ≈ u ∘ id *)
  reflexivity.
Qed.
Next Obligation.
  (* comp_counit : id ∘ u ≈ id ∘ u *)
  reflexivity.
Qed.

(*
   本节说明伴随、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Sq_conjoint {C : Category} {a b : C}
  (u : a ≅ b) : Conjoint (D:=Sq C) (to u) := {|
  conj_hor := from u
|}.
Next Obligation.
  (* conj_unit : from u ∘ to u ≈ id ∘ id *)
  rewrite iso_from_to; cat.
Qed.
Next Obligation.
  (* conj_counit : id ∘ id ≈ to u ∘ from u *)
  rewrite iso_to_from; cat.
Qed.

(* Necessity: a conjoint of [u] in [Sq C] is a two-sided inverse of [u],
   so only isomorphisms have conjoints in this model. *)
Program Definition Sq_conjoint_iso {C : Category} {a b : C}
  (u : a ~{C}~> b) (P : Conjoint (D:=Sq C) u) : a ≅ b := {|
  to := u;
  from := conj_hor P
|}.
Next Obligation.
  (* iso_to_from : u ∘ conj_hor P ≈ id *)
  pose proof (conj_counit P) as Hc; simpl in Hc.
  rewrite <- Hc; cat.
Qed.
Next Obligation.
  (* iso_from_to : conj_hor P ∘ u ≈ id *)
  pose proof (conj_unit P) as Hu; simpl in Hu.
  rewrite Hu; cat.
Qed.
