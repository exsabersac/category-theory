Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Natural.Transformation.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab: https://ncatlab.org/nlab/show/opposite+category

   本文件给出反范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Double-opposite, navigated definitionally *)

Program Definition op_invol_to {C : Category} :
  Opposite (Opposite C) ⟶ C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros C x y f g Hfg; exact Hfg. Qed.
Next Obligation. intros C x; simpl; reflexivity. Qed.
Next Obligation. intros C x y z f g; simpl; reflexivity. Qed.

Program Definition op_invol_from {C : Category} :
  C ⟶ Opposite (Opposite C) := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros C x y f g Hfg; exact Hfg. Qed.
Next Obligation. intros C x; simpl; reflexivity. Qed.
Next Obligation. intros C x y z f g; simpl; reflexivity. Qed.

(** ** The op endofunctor of Cat *)

Program Definition Op : Cat ⟶ Cat := {|
  fobj := fun C : Category => Opposite C;
  fmap := fun C D (F : C ⟶ D) => Opposite_Functor F
|}.
Next Obligation.
  (*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intro C; simpl.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
Next Obligation.
  intros C D E F G; simpl.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.

(** ** The involution *)

(* The component at C: an isomorphism of categories (in Cat's
   equivalence sense) between (C^op)^op and C, with identity round
   trips. *)
Program Definition op_invol_iso {C : Category} :
  @Isomorphism Cat (Opposite (Opposite C)) C := {|
  to := op_invol_to;
  from := op_invol_from
|}.
Next Obligation.
  intro C.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
Next Obligation.
  intro C.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.

Theorem Op_invol : Op ◯ Op ≈ Id[Cat].
Proof.
  exists (fun C : Category => op_invol_iso).
  intros C D F; simpl.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.

(** ** The strict variant *)

(* The StrictCat variant: same maps, laws at strict functor
   equality. *)
Program Definition Op_Strict : StrictCat ⟶ StrictCat := {|
  fobj := fun C : Category => Opposite C;
  fmap := fun C D (F : C ⟶ D) => Opposite_Functor F
|}.
Next Obligation.
  intros C D F G [e He].
  exists e.
  intros x y f; simpl.
  (*
   本节说明 Opposite 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  pose proof (He y x f) as K; revert K.
  generalize (fmap[G] f).
  generalize (fmap[F] f).
  destruct (e x), (e y); simpl.
  intros h g K; exact K.
Qed.
Next Obligation.
  intro C.
  exists (fun x => eq_refl).
  intros x y f; simpl; reflexivity.
Qed.
Next Obligation.
  intros C D E F G.
  exists (fun x => eq_refl).
  intros x y f; simpl; reflexivity.
Qed.

(* The strict involution, with eq_refl object components — the record
   eta of Category makes the double opposite definitional. *)
Theorem Op_Strict_invol :
  @equiv _ (@Functor_StrictEq_Setoid StrictCat StrictCat)
         (Op_Strict ◯ Op_Strict) (Id[StrictCat]).
Proof.
  exists (fun C : Category => eq_refl).
  intros C D F.
  unfold Logic.transport, Logic.transport_r; simpl.
  exists (fun x => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

(** ** Riehl's Exercise 1.3.v: the hom-setoid bijections *)

Program Definition op_flip_iso (C D : Category) :
  @Isomorphism Sets
    {| carrier := Opposite C ⟶ D ; is_setoid := @Functor_Setoid _ _ |}
    {| carrier := C ⟶ Opposite D ; is_setoid := @Functor_Setoid _ _ |} := {|
  to := {| morphism := fun F => Opposite_Functor F ◯ op_invol_from |};
  from := {| morphism := fun G => op_invol_to ◯ Opposite_Functor G |}
|}.
Next Obligation.
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intros C D G.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
Next Obligation.
  intros C D F.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.

Program Definition op_conjugate_iso (C D : Category) :
  @Isomorphism Sets
    {| carrier := C ⟶ D ; is_setoid := @Functor_Setoid _ _ |}
    {| carrier := Opposite C ⟶ Opposite D
     ; is_setoid := @Functor_Setoid _ _ |} := {|
  to := {| morphism := fun F => Opposite_Functor F |};
  from := {| morphism := fun G =>
               op_invol_to ◯ Opposite_Functor G ◯ op_invol_from |}
|}.
Next Obligation.
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intros C D G.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
Next Obligation.
  intros C D F.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
