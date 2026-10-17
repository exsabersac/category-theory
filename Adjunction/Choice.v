Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Adj.Forgetful.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Two.

Generalizable All Variables.

#[local] Obligation Tactic := intros.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/mate

   本文件给出选择相关伴随。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)
(* * ** (A) The full subcategory 函子 have 右伴随 （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition HasRightAdjoint {C D : Category} (F : D ⟶ C) : Type :=
  ∃ U : C ⟶ D, F ⊣ U.

(* Mac Lane's S: FULL subcategory A^X = [D, C] those 对象.
 [shom] terminal predicate, so every ambient transformation
 between selected 函子 retained. （已译） *)
Definition LeftAdjSub (C D : Category) : Subcategory ([D, C]) :=
  @Build_Subcategory ([D, C])
    (fun F : D ⟶ C => HasRightAdjoint F)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition LeftAdjCat (C D : Category) : Category :=
  Sub ([D, C]) (LeftAdjSub C D).

(* THE PIVOT. An 对象 S IS 对象 #395's 范畴 of
 伴随, nose: both {F & {U & F ⊣ U}}. （已译） *)
Example leftadj_obj (C D : Category) : obj[LeftAdjCat C D] = AdjObj C D
  := eq_refl.

Definition LeftAdjSub_Full (C D : Category) :
  Category.Construction.Subcategory.Full ([D, C]) (LeftAdjSub C D) :=
  fun _ _ _ _ _ => I.

(* ------------------------------------------------------------------ *)
(** ** (B) R : S^op ⟶ X^A *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition RightAdjointFunctor (C D : Category) :
  Opposite (LeftAdjCat C D) ⟶ [C, D] := {|
  fobj := fun x => adjobj_right (x : AdjObj C D);
  fmap := fun x y f =>
            conj_mate (adjobj_adj (x : AdjObj C D))
                      (adjobj_adj (y : AdjObj C D)) (`1 f)
|}.
Next Obligation. intros f g Hfg; now apply conj_mate_respects. Qed.
Next Obligation. now apply conj_mate_id. Qed.
Next Obligation. now apply conj_mate_compose. Qed.

(*
   本节说明 Choice 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example raf_fmap_variance (C D : Category)
        (x y : Opposite (LeftAdjCat C D)) (f : x ~> y) :
  fmap[RightAdjointFunctor C D] f
    = conj_mate (adjobj_adj (x : AdjObj C D))
                (adjobj_adj (y : AdjObj C D)) (`1 f) := eq_refl.

Example raf_id_is_conj_mate_id (C D : Category)
        (x : Opposite (LeftAdjCat C D)) :
  fmap[RightAdjointFunctor C D] (@id (Opposite (LeftAdjCat C D)) x)
    = conj_mate (adjobj_adj (x : AdjObj C D))
                (adjobj_adj (x : AdjObj C D)) nat_id := eq_refl.

(* ------------------------------------------------------------------ *)
(* * ** (C) S against #395's 范畴 伴随 （已译） *)

(* Identity 对象; arrow, bare σ 与…配对 mate.
 This literally Instance/Adj/Forgetful.v's [AdjForgetLeft_Full]
 [prefmap], read 函子. （已译） *)
Program Definition SubToAdj (C D : Category) : LeftAdjCat C D ⟶ Adj C D := {|
  fobj := fun x => (x : AdjObj C D);
  fmap := fun x y f =>
            {| conj_left  := `1 f
             ; conj_right := conj_mate (adjobj_adj (y : AdjObj C D))
                                       (adjobj_adj (x : AdjObj C D)) (`1 f) |}
|}.
Next Obligation. exact (conjugate_conj_mate _ _ _). Qed.
Next Obligation.
  intros f g Hfg; split; simpl; [ exact Hfg | now apply conj_mate_respects ].
Qed.
Next Obligation. split; simpl; [ reflexivity | now apply conj_mate_id ]. Qed.
Next Obligation.
  split; simpl; [ reflexivity | now apply conj_mate_compose ].
Qed.

(* R IS #395's second forgetful 函子 transported along that
 comparison: both actions agree nose. （已译） *)
Definition RAF_via (C D : Category) : Opposite (LeftAdjCat C D) ⟶ [C, D] :=
  AdjForgetRight C D ◯ Opposite_Functor (SubToAdj C D).

Example raf_obj_via (C D : Category) (x : Opposite (LeftAdjCat C D)) :
  fobj[RAF_via C D] x = fobj[RightAdjointFunctor C D] x := eq_refl.

Example raf_map_via (C D : Category) (x y : Opposite (LeftAdjCat C D))
        (f : x ~> y) :
  fmap[RAF_via C D] f = fmap[RightAdjointFunctor C D] f := eq_refl.

(* And first forgetful 函子, composed same way, IS the
 含入 subcategory -- again both actions. （已译） *)
Definition LI_via (C D : Category) : LeftAdjCat C D ⟶ [D, C] :=
  AdjForgetLeft C D ◯ SubToAdj C D.

Example incl_obj_via (C D : Category) (x : LeftAdjCat C D) :
  fobj[LI_via C D] x = fobj[Incl ([D, C]) (LeftAdjSub C D)] x := eq_refl.

Example incl_map_via (C D : Category) (x y : LeftAdjCat C D) (f : x ~> y) :
  fmap[LI_via C D] f = fmap[Incl ([D, C]) (LeftAdjSub C D)] f := eq_refl.

#[export]
Program Instance SubToAdj_Faithful (C D : Category) :
  Category.Theory.Functor.Faithful (SubToAdj C D).
Next Obligation. destruct X as [Hl _]; exact Hl. Qed.

(* 相关说明。 （已译） *)
#[export]
Program Instance SubToAdj_Full (C D : Category) :
  Category.Theory.Functor.Full (SubToAdj C D) := {|
  prefmap := fun x y g => (conj_left g; I)
|}.
Next Obligation.
  split; simpl; [ reflexivity | ].
  symmetry; apply conj_mate_uniq; exact (conj_pair_law g).
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local]
Program Instance SubToAdj_ESO (C D : Category) :
  EssentiallySurjective (SubToAdj C D) := {|
  eso_obj := fun d => (d : LeftAdjCat C D)
|}.

Definition SubToAdj_Equivalence (C D : Category) :
  EquivalenceOfCategories (SubToAdj C D) := FF_ESO_Equivalence (SubToAdj C D).

Program Definition AdjToSub (C D : Category) : Adj C D ⟶ LeftAdjCat C D := {|
  fobj := fun x => (x : LeftAdjCat C D);
  fmap := fun x y f => (conj_left f; I)
|}.
Next Obligation. intros f g [Hl _]; exact Hl. Qed.
Next Obligation. simpl; reflexivity. Qed.
Next Obligation. simpl; reflexivity. Qed.

Example rt_adj_obj (C D : Category) (x : Adj C D) :
  fobj[SubToAdj C D ◯ AdjToSub C D] x = x := eq_refl.

Example rt_sub_obj (C D : Category) (x : LeftAdjCat C D) :
  fobj[AdjToSub C D ◯ SubToAdj C D] x = x := eq_refl.

(* The strongest available identification.  `≅[StrictCat]` is an
   ISOMORPHISM OF CATEGORIES; `≅[Cat]` would be only an equivalence. *)
Program Definition SubAdj_strict_iso (C D : Category) :
  @Isomorphism StrictCat (LeftAdjCat C D) (Adj C D) := {|
  to := SubToAdj C D; from := AdjToSub C D
|}.
Next Obligation.
  exists (fun x => eq_refl).
  intros x y f; simpl.
  split; simpl; [ reflexivity | ].
  symmetry; apply conj_mate_uniq; exact (conj_pair_law f).
Qed.
Next Obligation.
  exists (fun x => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** (D)(a) Two choices for one F *)

(* The subcategory full, so ambient 恒等 F lifts twice and
 two memberships give ISOMORPHIC 对象 S. （已译） *)
Definition choice_iso_in_Sub (C D : Category) (F : D ⟶ C)
           (p q : HasRightAdjoint F) :
  ((F; p) : LeftAdjCat C D) ≅[LeftAdjCat C D] (F; q) :=
  Full_membership_iso ([D, C]) (LeftAdjSub C D) (LeftAdjSub_Full C D) F p q.

(* R carries 同构 mate 恒等, nose,
 BOTH legs. （已译） *)
Example raf_choice_iso_to (C D : Category) (F : D ⟶ C)
        (p q : HasRightAdjoint F) :
  fmap[RightAdjointFunctor C D] (to (choice_iso_in_Sub C D F p q))
    = conj_mate (adjobj_adj ((F; q) : AdjObj C D))
                (adjobj_adj ((F; p) : AdjObj C D)) nat_id := eq_refl.

Example raf_choice_iso_from (C D : Category) (F : D ⟶ C)
        (p q : HasRightAdjoint F) :
  fmap[RightAdjointFunctor C D] (from (choice_iso_in_Sub C D F p q))
    = conj_mate (adjobj_adj ((F; p) : AdjObj C D))
                (adjobj_adj ((F; q) : AdjObj C D)) nat_id := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition choice_right_adjoints_iso (C D : Category) (F : D ⟶ C)
           (p q : HasRightAdjoint F) : `1 p ≈ `1 q :=
  right_adjoint_iso F (`1 p) (`1 q) (`2 p) (`2 q).

(* The inverse law holds up `≈` not nose: it is
 [conj_mate_compose] followed [conj_mate_id], one
 恒等-cancellation between them. （已译） *)
Lemma raf_choice_inverse (C D : Category) (F : D ⟶ C)
      (p q : HasRightAdjoint F) :
  conj_mate (adjobj_adj ((F; q) : AdjObj C D))
            (adjobj_adj ((F; p) : AdjObj C D)) nat_id
    ∙ conj_mate (adjobj_adj ((F; p) : AdjObj C D))
                (adjobj_adj ((F; q) : AdjObj C D)) nat_id
  ≈ nat_id.
Proof.
  rewrite <- conj_mate_compose.
  transitivity (conj_mate (adjobj_adj ((F; p) : AdjObj C D))
                          (adjobj_adj ((F; p) : AdjObj C D)) nat_id).
  - apply conj_mate_respects; intro a; simpl; cat.
  - now apply conj_mate_id.
Qed.

(* ------------------------------------------------------------------ *)
(* * ** (D)(b) A choice function explicit 论元 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cm_comp_fun {C D : Category} {F1 U1 F2 U2 F3 U3}
      (A1 : @Adjunction C D F1 U1) (A2 : @Adjunction C D F2 U2)
      (A3 : @Adjunction C D F3 U3)
      (s : F2 ⟹ F1) (s' : F3 ⟹ F2) :
  @compose ([C, D]) _ _ _ (conj_mate A2 A3 s') (conj_mate A1 A2 s)
    ≈ conj_mate A1 A3 (@compose ([D, C]) _ _ _ s s').
Proof. symmetry; now apply conj_mate_compose. Qed.

Lemma cm_id_fun {C D : Category} {F1 U1} (A1 : @Adjunction C D F1 U1) :
  conj_mate A1 A1 (@id ([D, C]) F1) ≈ @id ([C, D]) U1.
Proof. now apply conj_mate_id. Qed.

(* Mac Lane's "choosing one RF each F", quantified: function
 re-choosing 右伴随 every member S. The name avoids
 taken [Choice]. （已译） *)
Definition RightAdjChoice (C D : Category) : Type :=
  ∀ F : D ⟶ C, HasRightAdjoint F → HasRightAdjoint F.

Definition ch_obj {C D : Category} (ch : RightAdjChoice C D)
           (x : LeftAdjCat C D) : AdjObj C D := (`1 x; ch (`1 x) (`2 x)).

Program Definition RightAdjointFunctor_ch (C D : Category)
        (ch : RightAdjChoice C D) : Opposite (LeftAdjCat C D) ⟶ [C, D] := {|
  fobj := fun x => adjobj_right (ch_obj ch x);
  fmap := fun x y f =>
    conj_mate (adjobj_adj (ch_obj ch x)) (adjobj_adj (ch_obj ch y)) (`1 f)
|}.
Next Obligation. intros f g Hfg; now apply conj_mate_respects. Qed.
Next Obligation. apply cm_id_fun. Qed.
Next Obligation. symmetry; apply cm_comp_fun. Qed.

Lemma raf_ch_fmap (C D : Category) (ch : RightAdjChoice C D)
      (x y : Opposite (LeftAdjCat C D)) (f : x ~> y) :
  fmap[RightAdjointFunctor_ch C D ch] f
    = conj_mate (adjobj_adj (ch_obj ch x)) (adjobj_adj (ch_obj ch y)) (`1 f).
Proof. reflexivity. Qed.

Definition ci_to (C D : Category) (ch ch' : RightAdjChoice C D)
           (x : LeftAdjCat C D) :
  adjobj_right (ch_obj ch x) ~{[C, D]}~> adjobj_right (ch_obj ch' x) :=
  conj_mate (adjobj_adj (ch_obj ch x)) (adjobj_adj (ch_obj ch' x))
            (@id ([D, C]) (`1 x)).

Definition ci_from (C D : Category) (ch ch' : RightAdjChoice C D)
           (x : LeftAdjCat C D) :
  adjobj_right (ch_obj ch' x) ~{[C, D]}~> adjobj_right (ch_obj ch x) :=
  conj_mate (adjobj_adj (ch_obj ch' x)) (adjobj_adj (ch_obj ch x))
            (@id ([D, C]) (`1 x)).

Program Definition ci_iso (C D : Category) (ch ch' : RightAdjChoice C D)
        (x : LeftAdjCat C D) :
  @Isomorphism ([C, D]) (adjobj_right (ch_obj ch x))
                        (adjobj_right (ch_obj ch' x)) := {|
  to := ci_to C D ch ch' x; from := ci_from C D ch ch' x
|}.
Next Obligation.
  unfold ci_to, ci_from.
  rewrite cm_comp_fun.
  transitivity (conj_mate (adjobj_adj (ch_obj ch' x))
                          (adjobj_adj (ch_obj ch' x)) (@id ([D, C]) (`1 x))).
  - apply conj_mate_respects; intro a; simpl; cat.
  - apply cm_id_fun.
Qed.
Next Obligation.
  unfold ci_to, ci_from.
  rewrite cm_comp_fun.
  transitivity (conj_mate (adjobj_adj (ch_obj ch x))
                          (adjobj_adj (ch_obj ch x)) (@id ([D, C]) (`1 x))).
  - apply conj_mate_respects; intro a; simpl; cat.
  - apply cm_id_fun.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ci_iso_to_eq (C D : Category) (ch ch' : RightAdjChoice C D)
      (x : LeftAdjCat C D) : to (ci_iso C D ch ch' x) = ci_to C D ch ch' x.
Proof. reflexivity. Qed.

Lemma ci_iso_from_eq (C D : Category) (ch ch' : RightAdjChoice C D)
      (x : LeftAdjCat C D) : from (ci_iso C D ch ch' x) = ci_from C D ch ch' x.
Proof. reflexivity. Qed.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem choice_independence (C D : Category) (ch ch' : RightAdjChoice C D) :
  RightAdjointFunctor_ch C D ch ≈ RightAdjointFunctor_ch C D ch'.
Proof.
  exists (ci_iso C D ch ch').
  intros x y f.
  rewrite ci_iso_to_eq, ci_iso_from_eq, !raf_ch_fmap.
  unfold ci_to, ci_from.
  rewrite cm_comp_fun.
  rewrite cm_comp_fun.
  apply conj_mate_respects.
  intro a; simpl; cat.
Qed.

(* (a) (b) at canonical choice: keep adjoint 对象
 already carries. The three projections return nose. （已译） *)
Definition ch_canonical (C D : Category) : RightAdjChoice C D := fun _ h => h.

Example ch_canonical_left (C D : Category) (x : LeftAdjCat C D) :
  adjobj_left (ch_obj (ch_canonical C D) x) = adjobj_left (x : AdjObj C D)
  := eq_refl.

Example ch_canonical_right (C D : Category) (x : LeftAdjCat C D) :
  adjobj_right (ch_obj (ch_canonical C D) x) = adjobj_right (x : AdjObj C D)
  := eq_refl.

Example ch_canonical_adj (C D : Category) (x : LeftAdjCat C D) :
  adjobj_adj (ch_obj (ch_canonical C D) x) = adjobj_adj (x : AdjObj C D)
  := eq_refl.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma two_arrows_agree {x y : TwoObj} (f g : TwoHom x y) : f = g.
Proof.
  destruct x, y;
    try (now rewrite (TwoHom_inv _ _ f), (TwoHom_inv _ _ g)).
  exact (False_rect _ (TwoHom_Y_X_absurd f)).
Qed.

Program Definition TwoConst (a : TwoObj) : _2 ⟶ _2 := {|
  fobj := fun _ => a;
  fmap := fun _ _ _ => @id _2 a
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. apply two_arrows_agree. Qed.

Definition two_to_Y (x : TwoObj) : x ~{_2}~> TwoY :=
  match x with TwoX => TwoXY | TwoY => TwoIdY end.

Definition two_from_X (y : TwoObj) : TwoX ~{_2}~> y :=
  match y with TwoX => TwoIdX | TwoY => TwoXY end.

#[local] Obligation Tactic := repeat intro; apply two_arrows_agree.

(* 相关说明。 （已译） *)
Program Definition two_const_hom_iso (x y : TwoObj) :
  @Isomorphism Sets
    {| carrier := @hom _2 (fobj[TwoConst TwoX] x) y
     ; is_setoid := @homset _2 (fobj[TwoConst TwoX] x) y |}
    {| carrier := @hom _2 x (fobj[TwoConst TwoY] y)
     ; is_setoid := @homset _2 x (fobj[TwoConst TwoY] y) |} := {|
  to   := {| morphism := fun _ => two_to_Y x |};
  from := {| morphism := fun _ => two_from_X y |}
|}.

#[local] Obligation Tactic := intros.

(* The 常值 函子 at TwoX 左伴随 常值 函子
 at TwoY -- 伴随 between two 函子 neither the
 恒等. （已译） *)
Definition two_const_adj : TwoConst TwoX ⊣ TwoConst TwoY.
Proof.
  apply (@Build_Adjunction' _2 _2 (TwoConst TwoX) (TwoConst TwoY)
                            two_const_hom_iso);
  intros; apply two_arrows_agree.
Defined.

Definition two_left_adjoint_object : LeftAdjCat _2 _2 :=
  (TwoConst TwoX; (TwoConst TwoY; two_const_adj)).

(* R at 对象 returns chosen 右伴随, nose. （已译） *)
Example two_raf_value :
  fobj[RightAdjointFunctor _2 _2] two_left_adjoint_object = TwoConst TwoY
  := eq_refl.

(* Not degenerate witness: two 常值 函子 differ, the
 左伴随 对象 not 恒等 函子. （已译） *)
Lemma two_const_functors_differ :
  fobj[TwoConst TwoX] TwoX = fobj[TwoConst TwoY] TwoX → False.
Proof. discriminate. Qed.

Lemma two_left_adjoint_not_identity :
  fobj[adjobj_left two_left_adjoint_object] TwoY = fobj[Id[_2]] TwoY → False.
Proof. discriminate. Qed.

(* PROPERNESS. The 常值 函子 at TwoY has no 右伴随: from
 伴随, inverse transpose 恒等 R(TwoX) an
 arrow TwoY ~> TwoX, there none. （已译） *)
Lemma two_const_Y_no_right_adjoint (R : _2 ⟶ _2)
      (A : TwoConst TwoY ⊣ R) : False.
Proof.
  exact (TwoHom_Y_X_absurd
           (from (@adj _2 _2 (TwoConst TwoY) R A (fobj[R] TwoX) TwoX)
                 (@id _2 (fobj[R] TwoX)))).
Qed.

Lemma two_left_adjoint_proper : HasRightAdjoint (TwoConst TwoY) → False.
Proof. intros [R A]; exact (two_const_Y_no_right_adjoint R A). Qed.
