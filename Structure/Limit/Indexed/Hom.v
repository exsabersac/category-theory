Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/coproduct
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   本文件给出 hom 形式的伴随/同态。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

Definition iprod_hom_fam {C : Category} {A : Type} (f : A → C) (c : C) :
  A → obj[Sets] :=
  fun a => {| carrier := @hom C c (f a); is_setoid := @homset C c (f a) |}.

Program Definition iprod_hom_functor {C : Category} {A : Type} (f : A → C) :
  C^op ⟶ Sets := {|
  fobj := fun c => Sets_iprod_obj (iprod_hom_fam f c);
  fmap := fun c c' (h : c ~{C^op}~> c') =>
            {| morphism := fun fam => fun a : A => fam a ∘[C] h |}
|}.
Next Obligation.
  intros C A f c c' h fam fam' Hfam a; simpl in *; now rewrite (Hfam a).
Qed.
Next Obligation.
  intros C A f c c' h h' Hh fam a; simpl in *; now rewrite Hh.
Qed.
Next Obligation.
  intros C A f c fam a; simpl; apply id_right.
Qed.
Next Obligation.
  intros C A f x y z h k fam a; simpl; apply comp_assoc.
Qed.

(* 相关说明。 （已译） *)

Program Definition iprod_hom_transform {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) :
  @Transform (C^op) Sets (@Curried_CoHom C q) (iprod_hom_functor f) := {|
  transform := fun c => {| morphism := fun u => fun a : A => proj a ∘ u |}
|}.
Next Obligation.
  intros C A f q proj c u v Huv a; simpl in *; now rewrite Huv.
Qed.
Next Obligation.
  intros C A f q proj x y h u a; simpl; apply comp_assoc_sym.
Qed.
Next Obligation.
  intros C A f q proj x y h u a; simpl; apply comp_assoc.
Qed.

(* * ** The inverse, supplied 普遍性质 （已译） *)

Program Definition iprod_hom_inverse {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  @Transform (C^op) Sets (iprod_hom_functor f) (@Curried_CoHom C q) := {|
  transform := fun c => {| morphism := fun fam => unique_obj (iprod_desc H fam) |}
|}.
Next Obligation.
  intros C A f q proj H c fam fam' Hfam; simpl in *.
  symmetry.
  apply (uniqueness (iprod_desc H fam')).
  intros a.
  rewrite (unique_property (iprod_desc H fam) a).
  now rewrite (Hfam a).
Qed.
Next Obligation.
  intros C A f q proj H x y h fam; simpl in *.
  symmetry.
  apply (uniqueness (iprod_desc H (fun a => fam a ∘ h))).
  intros a.
  rewrite comp_assoc.
  now rewrite (unique_property (iprod_desc H fam) a).
Qed.
Next Obligation.
  intros C A f q proj H x y h fam; simpl in *.
  apply (uniqueness (iprod_desc H (fun a => fam a ∘ h))).
  intros a.
  rewrite comp_assoc.
  now rewrite (unique_property (iprod_desc H fam) a).
Qed.

Program Definition iprod_hom_iso {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C q) (iprod_hom_functor f) := {|
  to   := iprod_hom_transform f q proj;
  from := iprod_hom_inverse H
|}.
Next Obligation.
  intros C A f q proj H c fam a; simpl.
  rewrite id_right.
  apply (unique_property (iprod_desc H fam) a).
Qed.
Next Obligation.
  intros C A f q proj H c u; simpl.
  rewrite id_right.
  apply (uniqueness (iprod_desc H (fun a => proj a ∘ u))).
  intros a; reflexivity.
Qed.

(* * ** The converse: invertible comparison map 普遍性质 （已译） *)

Definition iprod_of_hom_iso {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a}
  (I : @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C q)
                      (iprod_hom_functor f) (iprod_hom_transform f q proj)) :
  IsIndexedProduct f q proj.
Proof.
  apply (@Build_IsIndexedProduct C A f q proj).
  intros c pi.
  unshelve eapply Build_Unique.
  - exact (transform (@two_sided_inverse _ _ _ _ I) c pi).
  - intros a.
    pose proof (@is_right_inverse _ _ _ _ I c pi a) as Hr; simpl in Hr.
    now rewrite id_right in Hr.
  - intros v Hv.
    pose proof (@is_left_inverse _ _ _ _ I c v) as Hl; simpl in Hl.
    rewrite id_right in Hl.
    transitivity (transform (@two_sided_inverse _ _ _ _ I) c
                    (fun a => proj a ∘ v)).
    + apply (proper_morphism (transform (@two_sided_inverse _ _ _ _ I) c)).
      intros a; symmetry; exact (Hv a).
    + exact Hl.
Defined.

Definition iprod_hom_IsIsomorphism {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C q) (iprod_hom_functor f)
                 (iprod_hom_transform f q proj).
Proof.
  exact (@Build_IsIsomorphism ([C^op, Sets])
           (@Curried_CoHom C q) (iprod_hom_functor f)
           (iprod_hom_transform f q proj) (iprod_hom_inverse H)
           (iso_to_from (iprod_hom_iso H)) (iso_from_to (iprod_hom_iso H))).
Defined.

Definition iprod_iff_hom_iso {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) :
  IsIndexedProduct f q proj ↔
  @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C q) (iprod_hom_functor f)
                 (iprod_hom_transform f q proj) :=
  (fun H => iprod_hom_IsIsomorphism H, fun I => iprod_of_hom_iso I).

(** ** Strict readings *)

Example iprod_hom_transform_computes {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) (c : C) (u : c ~> q) :
  transform (iprod_hom_transform f q proj) c u = fun a : A => proj a ∘ u
  := eq_refl.

Example iprod_hom_iso_to {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  to (iprod_hom_iso H) = iprod_hom_transform f q proj := eq_refl.

Example iprod_hom_iso_from {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  from (iprod_hom_iso H) = iprod_hom_inverse H := eq_refl.

Example iprod_hom_iso_from_is_desc {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj)
  (c : C) (fam : ∀ a : A, c ~> f a) :
  transform (from (iprod_hom_iso H)) c fam = unique_obj (iprod_desc H fam)
  := eq_refl.

(* 相关说明。 （已译） *)

Example iprod_iff_hom_iso_fst {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) :
  fst (iprod_iff_hom_iso f q proj)
  = fun H => @iprod_hom_IsIsomorphism C A f q proj H := eq_refl.

Example iprod_iff_hom_iso_snd {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) :
  snd (iprod_iff_hom_iso f q proj)
  = fun I => @iprod_of_hom_iso C A f q proj I := eq_refl.

(* * ** The coproduct side, 定义 at [C^op] （已译） *)

(* Every 常值 section product counterpart applied at
 [C^op], supplied [:=] no tactic; [icoprod_hom_functor_is_op]
 records reading [eq_refl]. （已译） *)

Definition icoprod_hom_fam {C : Category} {A : Type} (f : A → C) (c : C) :
  A → obj[Sets] :=
  @iprod_hom_fam (C^op) A f c.

Definition icoprod_hom_functor {C : Category} {A : Type} (f : A → C) :
  C ⟶ Sets :=
  @iprod_hom_functor (C^op) A f.

Definition icoprod_hom_transform {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) :
  @Transform C Sets (@Curried_Hom C p) (icoprod_hom_functor f) :=
  @iprod_hom_transform (C^op) A f p inj.

Definition icoprod_hom_inverse {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj) :
  @Transform C Sets (icoprod_hom_functor f) (@Curried_Hom C p) :=
  @iprod_hom_inverse (C^op) A f p inj H.

Definition icoprod_hom_iso {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C p) (icoprod_hom_functor f) :=
  @iprod_hom_iso (C^op) A f p inj H.

Definition icoprod_hom_IsIsomorphism {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj) :
  @IsIsomorphism ([C, Sets]) (@Curried_Hom C p) (icoprod_hom_functor f)
                 (icoprod_hom_transform f p inj) :=
  @iprod_hom_IsIsomorphism (C^op) A f p inj H.

Definition icoprod_of_hom_iso {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p}
  (I : @IsIsomorphism ([C, Sets]) (@Curried_Hom C p) (icoprod_hom_functor f)
                      (icoprod_hom_transform f p inj)) :
  IsIndexedCoproduct f p inj :=
  @iprod_of_hom_iso (C^op) A f p inj I.

Definition icoprod_iff_hom_iso {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) :
  IsIndexedCoproduct f p inj ↔
  @IsIsomorphism ([C, Sets]) (@Curried_Hom C p) (icoprod_hom_functor f)
                 (icoprod_hom_transform f p inj) :=
  @iprod_iff_hom_iso (C^op) A f p inj.

Example icoprod_hom_transform_computes {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) (c : C) (u : p ~> c) :
  transform (icoprod_hom_transform f p inj) c u = fun a : A => u ∘ inj a
  := eq_refl.

Example icoprod_iff_hom_iso_fst {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) :
  fst (icoprod_iff_hom_iso f p inj)
  = fun H => @icoprod_hom_IsIsomorphism C A f p inj H := eq_refl.

Example icoprod_iff_hom_iso_snd {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) :
  snd (icoprod_iff_hom_iso f p inj)
  = fun I => @icoprod_of_hom_iso C A f p inj I := eq_refl.

Example icoprod_hom_iso_to {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj) :
  to (icoprod_hom_iso H) = icoprod_hom_transform f p inj := eq_refl.

Example icoprod_hom_iso_from_is_desc {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj)
  (c : C) (fam : ∀ a : A, f a ~> c) :
  transform (from (icoprod_hom_iso H)) c fam = unique_obj (icoprod_desc H fam)
  := eq_refl.

(* 相关说明。 （已译） *)

Definition limit_hom_iso {C : Category} {A : Set} (f : A → C)
  (L : Limit (DiscreteCat_Functor f)) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C (iprod f L))
               (iprod_hom_functor f) :=
  iprod_hom_iso (limit_is_indexed_product f L).

Definition colimit_hom_iso {C : Category} {A : Set} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f)) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C (icoprod f L))
               (icoprod_hom_functor f) :=
  icoprod_hom_iso (colimit_is_indexed_coproduct f L).

Definition indexed_product_hom_iso {C : Category}
  {HP : @HasIndexedProducts C} {A : Type} (f : A → C) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C (indexed_product f))
               (iprod_hom_functor f) :=
  iprod_hom_iso (indexed_product_ump f).

Definition indexed_coproduct_hom_iso {C : Category}
  {HC : @HasIndexedCoproducts C} {A : Type} (f : A → C) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C (indexed_coproduct f))
               (icoprod_hom_functor f) :=
  icoprod_hom_iso (indexed_coproduct_ump f).

(* 相关说明。 （已译） *)

Example iprod_hom_functor_is_indexed_product {C : Category} {A : Type}
  (f : A → C) (c : C) :
  fobj[iprod_hom_functor f] c = indexed_product (iprod_hom_fam f c) := eq_refl.

Example icoprod_hom_functor_is_indexed_product {C : Category} {A : Type}
  (f : A → C) (c : C) :
  fobj[icoprod_hom_functor f] c = indexed_product (icoprod_hom_fam f c)
  := eq_refl.

Example icoprod_hom_functor_is_op {C : Category} {A : Type} (f : A → C) :
  icoprod_hom_functor f = @iprod_hom_functor (C^op) A f := eq_refl.

(* 相关说明。 （已译） *)

Definition Sets_iprod_hom_iso {A : Type} (F : A → obj[Sets]) :
  @Isomorphism ([Sets^op, Sets]) (@Curried_CoHom Sets (Sets_iprod_obj F))
               (iprod_hom_functor F) :=
  iprod_hom_iso (Sets_IsIndexedProduct F).

Definition Sets_icoprod_hom_iso {A : Type} (F : A → obj[Sets]) :
  @Isomorphism ([Sets, Sets]) (@Curried_Hom Sets (Sets_icoprod_obj F))
               (icoprod_hom_functor F) :=
  icoprod_hom_iso (Sets_IsIndexedCoproduct F).

Example Sets_iprod_hom_from_computes {A : Type} (F : A → obj[Sets])
  (c : obj[Sets]) (fam : ∀ a : A, c ~{Sets}~> F a) :
  transform (from (Sets_iprod_hom_iso F)) c fam = Sets_iprod_tuple F c fam
  := eq_refl.

Example Sets_icoprod_hom_from_computes {A : Type} (F : A → obj[Sets])
  (c : obj[Sets]) (fam : ∀ a : A, F a ~{Sets}~> c) :
  transform (from (Sets_icoprod_hom_iso F)) c fam = Sets_icoprod_case F c fam
  := eq_refl.

(* * ** The invertibility 假设 not vacuous （已译） *)

Definition Sets_const_true : Sets_bool ~{Sets}~> Sets_bool.
Proof.
  unshelve refine {| morphism := fun _ => true |}.
  all: intros x y Hxy; reflexivity.
Defined.

Definition Sets_bad_proj (a : poly_unit) :
  Sets_bool ~{Sets}~> (fun _ : poly_unit => Sets_bool) a := Sets_const_true.

Lemma Sets_bad_transform_not_iso :
  @IsIsomorphism ([Sets^op, Sets])
    (@Curried_CoHom Sets Sets_bool)
    (iprod_hom_functor (fun _ : poly_unit => Sets_bool))
    (iprod_hom_transform (fun _ : poly_unit => Sets_bool)
                         Sets_bool Sets_bad_proj) → False.
Proof.
  intros I.
  pose proof (@is_left_inverse _ _ _ _ I Sets_bool
                (@id Sets Sets_bool)) as H0.
  pose proof (@is_left_inverse _ _ _ _ I Sets_bool Sets_const_true) as H1.
  simpl in H0, H1.
  assert (Heq : transform (@two_sided_inverse _ _ _ _ I) Sets_bool
                  (fun _ : poly_unit => Sets_const_true ∘ @id Sets Sets_bool)
                ≈ transform (@two_sided_inverse _ _ _ _ I) Sets_bool
                  (fun _ : poly_unit => Sets_const_true ∘ Sets_const_true)).
  { apply (proper_morphism
             (transform (@two_sided_inverse _ _ _ _ I) Sets_bool)).
    intros a x; reflexivity. }
  specialize (Heq false).
  rewrite H0, H1 in Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

Definition Sets_bad_not_iprod :
  IsIndexedProduct (fun _ : poly_unit => Sets_bool) Sets_bool Sets_bad_proj
  → False :=
  fun H => Sets_bad_transform_not_iso (fst (iprod_iff_hom_iso _ _ _) H).

Definition Sets_bad_inj (a : poly_unit) :
  (fun _ : poly_unit => Sets_bool) a ~{Sets}~> Sets_bool := Sets_const_true.

Lemma Sets_bad_transform_not_iso_co :
  @IsIsomorphism ([Sets, Sets])
    (@Curried_Hom Sets Sets_bool)
    (icoprod_hom_functor (fun _ : poly_unit => Sets_bool))
    (icoprod_hom_transform (fun _ : poly_unit => Sets_bool)
                           Sets_bool Sets_bad_inj) → False.
Proof.
  intros I.
  pose proof (@is_left_inverse _ _ _ _ I Sets_bool
                (@id Sets Sets_bool)) as H0.
  pose proof (@is_left_inverse _ _ _ _ I Sets_bool Sets_const_true) as H1.
  simpl in H0, H1.
  assert (Heq : transform (@two_sided_inverse _ _ _ _ I) Sets_bool
                  (fun _ : poly_unit => @id Sets Sets_bool ∘ Sets_const_true)
                ≈ transform (@two_sided_inverse _ _ _ _ I) Sets_bool
                  (fun _ : poly_unit => Sets_const_true ∘ Sets_const_true)).
  { apply (proper_morphism
             (transform (@two_sided_inverse _ _ _ _ I) Sets_bool)).
    intros a x; reflexivity. }
  specialize (Heq false).
  rewrite H0, H1 in Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

Definition Sets_bad_not_icoprod :
  IsIndexedCoproduct (fun _ : poly_unit => Sets_bool) Sets_bool Sets_bad_inj
  → False :=
  fun H => Sets_bad_transform_not_iso_co (fst (icoprod_iff_hom_iso _ _ _) H).

(*
   本节说明 Hom 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example Sets_iprod_hom_iso_is_class {A : Type} (F : A → obj[Sets]) :
  @indexed_product_hom_iso Sets Sets_HasIndexedProducts A F
  = Sets_iprod_hom_iso F := eq_refl.

Example Sets_icoprod_hom_iso_is_class {A : Type} (F : A → obj[Sets]) :
  @indexed_coproduct_hom_iso Sets Sets_HasIndexedCoproducts A F
  = Sets_icoprod_hom_iso F := eq_refl.
