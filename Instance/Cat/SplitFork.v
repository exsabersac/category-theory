Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Arrow.Functor.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.Terminal.
Require Import Category.Instance.StrictCat.ToCat.

Generalizable All Variables.

(* * * The fork C² ⇉ C → 1 Cat, split 终对象 C （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/split+coequalizer
 nLab: https://ncatlab.org/nlab/show/arrow+category
 nLab: https://ncatlab.org/nlab/show/terminal+category

   本文件给出 Cat 相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The fork, for C any category *)

(* e, unique 函子 C ⟶ 1, terminal map [Cat] of
 [StrictCat] alike. （已译） *)
Example arrow_fork_e_one@{o h +} (C : Category@{o h h}) :
  Erase C = @one Cat Cat_Terminal C := eq_refl.

Example arrow_fork_e_one_strict@{o h +} (C : Category@{o h h}) :
  Erase C = @one StrictCat StrictCat_Terminal C := eq_refl.

(* Law 1, e ∂₀ = e ∂₁: both sides are functors into 1, so they agree in
   either category of categories. *)
Lemma arrow_fork_law1@{o h +} (C : Category@{o h h}) :
  Erase C ∘[Cat] Arrow_dom ≈[Cat] Erase C ∘[Cat] Arrow_cod.
Proof. apply (@one_unique Cat Cat_Terminal). Qed.

Lemma arrow_fork_law1_strict@{o h +} (C : Category@{o h h}) :
  Erase C ∘[StrictCat] Arrow_dom ≈[StrictCat] Erase C ∘[StrictCat] Arrow_cod.
Proof. apply (@one_unique StrictCat StrictCat_Terminal). Qed.

(* ... nose, 对象 arrows. （已译） *)
Example arrow_fork_law1_obj@{o h +} (C : Category@{o h h}) (x : @Arrow C) :
  fobj[Erase C ◯ Arrow_dom] x = fobj[Erase C ◯ Arrow_cod] x := eq_refl.

Example arrow_fork_law1_map@{o h +} (C : Category@{o h h})
  {x y : @Arrow C} (f : x ~> y) :
  fmap[Erase C ◯ Arrow_dom] f = fmap[Erase C ◯ Arrow_cod] f := eq_refl.

(* * ** The splitting, given 终对象 a₀ C （已译） *)

(* s, 函子 1 ⟶ C sending 对象 1 a₀. （已译） *)
Example arrow_fork_s_obj@{o h +} {C : Category@{o h h}} `{T : @Terminal C}
  (x : _1) :
  fobj[Diagonal _1 (@terminal_obj C T)] x = @terminal_obj C T := eq_refl.

(* t, 函子 C ⟶ C² sending c 唯一箭头 c → a₀: the
 classifying 函子 唯一箭头 Id[C] terminal
 对象 [C, C], 常值 函子 at a₀. （已译） *)
Definition arrow_fork_t@{o h +} {C : Category@{o h h}} `{T : @Terminal C} :
  C ⟶ @Arrow C :=
  Arrow_intro (Id[C]; (Constant_Terminal_Functor T;
                        @one _ (Functor_Category_Terminal T) Id[C])).

Example arrow_fork_t_obj@{o h +} {C : Category@{o h h}} `{T : @Terminal C}
  (c : C) :
  fobj[arrow_fork_t] c = ((c, @terminal_obj C T); @one C T c) := eq_refl.

Example arrow_fork_t_map@{o h +} {C : Category@{o h h}} `{T : @Terminal C}
  {c d : C} (f : c ~> d) :
  `1 (fmap[arrow_fork_t] f) = (f, @id C (@terminal_obj C T)) := eq_refl.

(* Law 2, e s = 1: two functors into 1 again. *)
Lemma arrow_fork_law2_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Erase C ∘[StrictCat] Diagonal _1 (@terminal_obj C T)
    ≈[StrictCat] @id StrictCat _1.
Proof. apply (@one_unique StrictCat StrictCat_Terminal). Qed.

(* Law 3, ∂₀ t = 1, 对象 component [eq_refl]. （已译） *)
Lemma arrow_fork_law3_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_dom ∘[StrictCat] arrow_fork_t ≈[StrictCat] @id StrictCat C.
Proof. exists (fun _ => eq_refl). intros; simpl; reflexivity. Defined.

(* Law 4, ∂₁ t = s e, 对象 component [eq_refl]. （已译） *)
Lemma arrow_fork_law4_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_cod ∘[StrictCat] arrow_fork_t
    ≈[StrictCat] Diagonal _1 (@terminal_obj C T) ∘[StrictCat] Erase C.
Proof. exists (fun _ => eq_refl). intros; simpl; reflexivity. Defined.

(* ... and those object components, read back. *)
Example arrow_fork_law3_strict_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  projT1 (@arrow_fork_law3_strict C T) = fun _ => eq_refl := eq_refl.

Example arrow_fork_law4_strict_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  projT1 (@arrow_fork_law4_strict C T) = fun _ => eq_refl := eq_refl.

(* Law 2 nose at 对象 1 arrow; variable
 对象 arrow 1 it needs case analysis (see header). （已译） *)
Example arrow_fork_law2_obj@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  fobj[Erase C ◯ Diagonal _1 (@terminal_obj C T)] ttt = fobj[Id[_1]] ttt
  := eq_refl.

Example arrow_fork_law2_map@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  fmap[Erase C ◯ Diagonal _1 (@terminal_obj C T)] (@id _1 ttt)
    = fmap[Id[_1]] (@id _1 ttt) := eq_refl.

(* Laws 3 4 nose, 对象 arrows. （已译） *)
Example arrow_fork_law3_obj@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  fobj[Arrow_dom ◯ arrow_fork_t] c = fobj[Id[C]] c := eq_refl.

Example arrow_fork_law3_map@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} {c d : C} (f : c ~> d) :
  fmap[Arrow_dom ◯ arrow_fork_t] f = fmap[Id[C]] f := eq_refl.

Example arrow_fork_law4_obj@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  fobj[Arrow_cod ◯ arrow_fork_t] c
    = fobj[Diagonal _1 (@terminal_obj C T) ◯ Erase C] c := eq_refl.

Example arrow_fork_law4_map@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} {c d : C} (f : c ~> d) :
  fmap[Arrow_cod ◯ arrow_fork_t] f
    = fmap[Diagonal _1 (@terminal_obj C T) ◯ Erase C] f := eq_refl.

(* 相关说明。 （已译） *)
Definition arrow_fork_split_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @SplitCoequalizer StrictCat (@Arrow C) C Arrow_dom Arrow_cod :=
  @Build_SplitCoequalizer StrictCat (@Arrow C) C Arrow_dom Arrow_cod
    _1 (Erase C) (Diagonal _1 (@terminal_obj C T)) arrow_fork_t
    (arrow_fork_law1_strict C) arrow_fork_law2_strict
    arrow_fork_law3_strict arrow_fork_law4_strict.

(* The split fork Cat: one StrictCat, pushed along the
 comparison 函子 StrictCat ⟶ Cat, 恒等 对象
 arrows. （已译） *)
Definition arrow_fork_split@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @SplitCoequalizer Cat (@Arrow C) C Arrow_dom Arrow_cod :=
  functor_preserves_split StrictCat_to_Cat _ _ arrow_fork_split_strict.

(* 相关说明。 （已译） *)
Example arrow_fork_split_e@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_e arrow_fork_split = Erase C := eq_refl.

Example arrow_fork_split_s@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_s arrow_fork_split = Diagonal _1 (@terminal_obj C T) := eq_refl.

Example arrow_fork_split_t@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_t arrow_fork_split = arrow_fork_t := eq_refl.

(* 相关说明。 （已译） *)

(* Laws 2 to 4 proved in Cat itself, each natural isomorphism having
   identities for components; law 1 is [arrow_fork_law1]. *)
Lemma arrow_fork_law2_direct@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Erase C ∘[Cat] Diagonal _1 (@terminal_obj C T) ≈[Cat] @id Cat _1.
Proof.
  unshelve eexists.
  - intros []; exact iso_id.
  - intros [] [] []; simpl; reflexivity.
Defined.

Lemma arrow_fork_law3_direct@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_dom ∘[Cat] arrow_fork_t ≈[Cat] @id Cat C.
Proof. exists (fun _ => iso_id). intros; simpl; cat. Defined.

Lemma arrow_fork_law4_direct@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_cod ∘[Cat] arrow_fork_t
    ≈[Cat] Diagonal _1 (@terminal_obj C T) ∘[Cat] Erase C.
Proof. exists (fun _ => iso_id). intros; simpl; cat. Defined.

(* 相关说明。 （已译） *)
Example arrow_fork_law3_direct_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (@arrow_fork_law3_direct C T) c) = id := eq_refl.

Example arrow_fork_law4_direct_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (@arrow_fork_law4_direct C T) c) = id := eq_refl.

(* 相关说明。 （已译） *)
Definition arrow_fork_split_direct@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @SplitCoequalizer Cat (@Arrow C) C Arrow_dom Arrow_cod :=
  @Build_SplitCoequalizer Cat (@Arrow C) C Arrow_dom Arrow_cod
    _1 (Erase C) (Diagonal _1 (@terminal_obj C T)) arrow_fork_t
    (arrow_fork_law1 C) arrow_fork_law2_direct
    arrow_fork_law3_direct arrow_fork_law4_direct.

Example arrow_fork_split_direct_e@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_e arrow_fork_split_direct = Erase C := eq_refl.

Example arrow_fork_split_direct_s@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_s arrow_fork_split_direct = Diagonal _1 (@terminal_obj C T)
  := eq_refl.

Example arrow_fork_split_direct_t@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_t arrow_fork_split_direct = arrow_fork_t := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition arrow_fork_coequalizer_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @IsCoequalizer StrictCat _ _ Arrow_dom Arrow_cod _1 (Erase C) :=
  split_coequalizer_is_coequalizer _ _ arrow_fork_split_strict.

Definition arrow_fork_coequalizer@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @IsCoequalizer Cat _ _ Arrow_dom Arrow_cod _1 (Erase C) :=
  split_coequalizer_is_coequalizer _ _ arrow_fork_split.

(* ... every 函子 out StrictCat out Cat a
 D : Category@{do dh dh} o <= dh carries it coequalizer. （已译） *)
Definition arrow_fork_preserved_strict@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : StrictCat ⟶ D) :
  IsCoequalizer (fmap[F] Arrow_dom) (fmap[F] Arrow_cod)
    (F _1) (fmap[F] (Erase C)) :=
  split_coequalizer_preserved F _ _ arrow_fork_split_strict.

Definition arrow_fork_preserved@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : Cat ⟶ D) :
  IsCoequalizer (fmap[F] Arrow_dom) (fmap[F] Arrow_cod)
    (F _1) (fmap[F] (Erase C)) :=
  split_coequalizer_preserved F _ _ arrow_fork_split.

(* 相关说明。 （已译） *)
Definition arrow_fork_absolute_strict@{o h xo xh +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @AbsoluteCoequalizer@{_ _ xo xh _} StrictCat (@Arrow C) C Arrow_dom
    Arrow_cod _1 (Erase C) :=
  split_coequalizer_absolute arrow_fork_split_strict.

Definition arrow_fork_absolute@{o h xo xh +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @AbsoluteCoequalizer@{_ _ xo xh _} Cat (@Arrow C) C Arrow_dom Arrow_cod
    _1 (Erase C) :=
  split_coequalizer_absolute arrow_fork_split.

(* 相关说明。 （已译） *)
Example arrow_fork_preserved_absolute_strict@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : StrictCat ⟶ D) :
  @arrow_fork_preserved_strict C T D F = @arrow_fork_absolute_strict C T D F
  := eq_refl.

Example arrow_fork_preserved_absolute@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : Cat ⟶ D) :
  @arrow_fork_preserved C T D F = @arrow_fork_absolute C T D F := eq_refl.

(* 相关说明。 （已译） *)

(* If C has no 对象, neither has C², so 恒等 C coforks ∂₀
 ∂₁; were e coequalizer, it would descend through e 函子
 1 ⟶ C, whose value 对象 C. （已译） *)
Lemma arrow_fork_not_coequalizer@{o h +} (C : Category@{o h h})
  (empty : C → False) :
  @IsCoequalizer Cat _ _ Arrow_dom Arrow_cod _1 (Erase C) → False.
Proof.
  intros E.
  assert (H : @id Cat C ∘[Cat] Arrow_dom ≈[Cat] @id Cat C ∘[Cat] Arrow_cod).
  { unshelve eexists.
    - intros [[x y] f]. contradiction (empty x).
    - intros [[x y] f]. contradiction (empty x). }
  destruct (coeq_desc E (@id Cat C) H) as [u _ _].
  exact (empty (fobj[u] ttt)).
Qed.

(* The empty category is such a C. *)
Example arrow_fork_not_coequalizer_0 :
  @IsCoequalizer Cat _ _ Arrow_dom Arrow_cod _1 (Erase _0) → False :=
  arrow_fork_not_coequalizer _0 (fun x => match x with end).
