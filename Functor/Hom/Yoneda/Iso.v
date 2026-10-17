Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.
Require Import Category.Theory.Sheaf.
Require Import Category.Functor.Hom.Yoneda.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
    nLab: https://ncatlab.org/nlab/show/Yoneda+embedding

   本文件给出 Yoneda 相关结果。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section RepresentablyIso.

Context {C : Category}.

(* [Curried_CoHom C] is [Curried_Hom C^op] by definition, but typeclass
   resolution does not unfold definitions; these instances make the
   contravariant embedding's full faithfulness available by name. *)
#[export] Instance CoYoneda_Faithful : Faithful (Curried_CoHom C) :=
  Yoneda_Faithful C^op.

#[export] Instance CoYoneda_Full : Full (Curried_CoHom C) :=
  Yoneda_Full C^op.

(* An 同构 read opposite 范畴, two triangle
 laws exchanged. （已译） *)
Definition iso_op {x y : C} (i : x ≅ y) : @Isomorphism C^op y x := {|
  to := to i : @hom C^op y x;
  from := from i;
  iso_to_from := iso_from_to i;
  iso_from_to := iso_to_from i
|}.

(* 相关说明。 （已译） *)

(* Two objects are representably isomorphic when both represented
   functors agree up to natural isomorphism: C(−,x) ≅ C(−,y) in
   presheaves AND C(y,−) ≅ C(x,−) in copresheaves (Riehl's directions;
   either component determines the other through x ≅ y below). *)
Definition ContravariantRepresentableIso (x y : C) : Type :=
  @Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y].

Definition CovariantRepresentableIso (x y : C) : Type :=
  @Isomorphism (@Copresheaves C Sets) [Hom y,─] [Hom x,─].

Definition RepresentablyIsomorphic (x y : C) : Type :=
  ContravariantRepresentableIso x y * CovariantRepresentableIso x y.

(* 相关说明。 （已译） *)

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition iso_iff_representably_iso (x y : C) :
  iffT (x ≅ y) (@Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]).
Proof.
  split.
  - exact (@fobj_iso _ _ (Curried_CoHom C) x y).
  - exact (@FullyFaithful _ _ (Curried_CoHom C) _ _ x y).
Defined.

(* Covariant twin: x ≅ y exactly when [Hom y,─] ≅ [Hom x,─], through
   the opposite category. *)
Definition iso_iff_corepresentably_iso (x y : C) :
  iffT (x ≅ y) (@Isomorphism (@Copresheaves C Sets) [Hom y,─] [Hom x,─]).
Proof.
  split.
  - intros i.
    exact (@fobj_iso _ _ (Curried_Hom C) y x (iso_op i)).
  - intros α.
    pose (i := @FullyFaithful _ _ (Curried_Hom C) _ _ y x α).
    exact {| to := to i : x ~{C}~> y
           ; from := from i
           ; iso_to_from := iso_from_to i
           ; iso_from_to := iso_to_from i |}.
Defined.

(* Isomorphic 对象 representably isomorphic both variances at
 once, two variances agree each other. （已译） *)
Definition representably_isomorphic_of_iso {x y : C} (i : x ≅ y) :
  RepresentablyIsomorphic x y :=
  (fst (iso_iff_representably_iso x y) i,
   fst (iso_iff_corepresentably_iso x y) i).

(* ...and conversely, either representable 同构 recovers the
 同构 对象. （已译） *)
Definition iso_of_representably_isomorphic {x y : C}
  (r : RepresentablyIsomorphic x y) : x ≅ y :=
  snd (iso_iff_representably_iso x y) (fst r).

Definition representably_iso_variances_agree (x y : C) :
  iffT (@Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y])
       (@Isomorphism (@Copresheaves C Sets) [Hom y,─] [Hom x,─]).
Proof.
  split; intros α.
  - exact (fst (iso_iff_corepresentably_iso x y)
             (snd (iso_iff_representably_iso x y) α)).
  - exact (fst (iso_iff_representably_iso x y)
             (snd (iso_iff_corepresentably_iso x y) α)).
Defined.

End RepresentablyIso.

(*
   本节说明函子、Yoneda、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition repr_pair_iso {C : Category} {F : C ⟶ Sets} {c v : C}
  (b1 : @Isomorphism (@Copresheaves C Sets) [Hom c,─] F)
  (b2 : @Isomorphism (@Copresheaves C Sets) [Hom v,─] F) : c ≅ v.
Proof.
  unshelve econstructor.
  - exact (@two_sided_inverse _ _ _ _ (Yoneda_Embedding' C v c)
             (from b1 ∘ to b2)).
  - exact (@two_sided_inverse _ _ _ _ (Yoneda_Embedding' C c v)
             (from b2 ∘ to b1)).
  - abstract(apply (@fmap_inj _ _ (Curried_Hom C) _);
    set (j := ( _ ( compose  _ _)));
    set (j' := ( _ ( compose  _ _)));
    change j with (op j);
    change j' with (op j');
    set (m := @fmap_comp _ _ C v c v (op j') (op j));
    rewrite m;
    unfold op, j, j';
    rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C v c) (from b1 ∘ b2));
    rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C c v) (from b2 ∘ b1));
    simpl; intros x f; unfold op; rewrite id_right;
    set (ab := (iso_to_from b1));
    simpl in ab; rewrite ab;
    rewrite (@fmap_id _ _ F x (to b2 x f));
    simpl; clear ab;
    set (ab' := (iso_from_to b2));
    simpl in ab'; rewrite ab'; rewrite id_left;
    reflexivity).
  - abstract(apply (@fmap_inj _ _ (Curried_Hom C) _);
    set (j := ( _ ( compose  _ _)));
    set (j' := ( _ ( compose  _ _)));
    change j with (op j);
    change j' with (op j');
    set (m := @fmap_comp _ _ C c v c (op j') (op j));
    rewrite m;
    unfold op, j, j';
    rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C v c) (from b1 ∘ b2));
    rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C c v) (from b2 ∘ b1));
    simpl; intros x f; unfold op; rewrite id_right;
    set (ab := (iso_to_from b2));
    simpl in ab; rewrite ab;
    rewrite (@fmap_id _ _ F x (to b1 x f));
    simpl; clear ab;
    set (ab' := (iso_from_to b1));
    simpl in ab'; rewrite ab'; rewrite id_left;
    reflexivity).
Defined.

(* 相关说明。 （已译） *)

(* An 同构 read back opposite 范畴. （已译） *)
Definition iso_unop {C : Category} {x y : C}
  (i : @Isomorphism C^op x y) : x ≅ y := {|
  to := from i : x ~{C}~> y;
  from := to i;
  iso_to_from := iso_to_from i;
  iso_from_to := iso_from_to i
|}.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition eval_iso {C : Category} {x y : C}
  (α : @Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]) : x ≅ y :=
  iso_unop (@repr_pair_iso C^op (fobj[Curried_CoHom C] y) x y α iso_id).

Lemma eval_iso_to {C : Category} {x y : C}
  (α : @Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]) :
  to (eval_iso α) ≈ transform[to α] x id.
Proof. simpl; cat. Qed.

Lemma eval_iso_from {C : Category} {x y : C}
  (α : @Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]) :
  from (eval_iso α) ≈ transform[from α] y id.
Proof. simpl; cat. Qed.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition representable_iso_setoid {C : Category} (x y : C) :
  (x ≅ y) ≊ (@Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]) := {|
  to := {| morphism := fst (iso_iff_representably_iso x y) |};
  from := {| morphism := eval_iso |}
|}.
Next Obligation.
  intros C x y i j [Ht Hf]; split; simpl.
  - intros c g; unfold op; now rewrite Ht.
  - intros c g; unfold op; now rewrite Hf.
Qed.
Next Obligation.
  intros C x y α β [Ht Hf]; split; simpl.
  - now rewrite (Ht x id).
  - exact (Hf y (id ∘ id)).
Qed.
Next Obligation.
  intros C x y α; split; simpl.
  - intros c g; unfold op; rewrite id_right.
    exact (iso_from_to (Yoneda_Embedding C x y) (to α) c g).
  - intros c g; unfold op; rewrite id_right.
    exact (iso_from_to (Yoneda_Embedding C y x) (from α) c g).
Qed.
Next Obligation.
  intros C x y i; split; simpl; cat.
Qed.
