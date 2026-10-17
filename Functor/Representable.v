Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Representable functors. *)

(* nLab: https://ncatlab.org/nlab/show/representable+functor
   Wikipedia: https://en.wikipedia.org/wiki/Representable_functor

   函子 F : C ⟶ Sets 可表 (representable)，当它自然同构于某对象 A ∈ C 的共变
   hom 函子 Hom(A, ─)。库记号中该自然同构为

       [Hom A,─] ≅ F     （函子范畴 [C, Sets] 中的同构），

   故下文 [represented] 恰是 Wikipedia 的对 (A, Φ)：[repr_obj] 是 A，[represented]
   是自然同构 Φ : Hom(A, ─) ⟹ F。由 Yoneda 引理，此类 Φ 由 F(A) 的单个普遍元决定，
   即 Φ_A(id A)，且表示对象在（唯一）同构下唯一；普遍元半边在 Structure/UniversalProperty.v
   开发，唯一性半边是下文 [repr_unique_iso]，即本文件后半诱导箭头对应的 τ = id 情形。
   反变可表 G : C^op ⟶ Sets（预层）则自然同构于 Hom(─, A)；见 Functor/Hom.v 的
   [Hom ─,A]（Curried_CoHom）。 *)

(*
   Wikipedia: "Let C be a locally small category and let Set be the category

   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Representable `(F : C ⟶ Sets) := {
  repr_obj : C;                          (* the representing object A *)
  represented : [Hom repr_obj,─] ≅ F     (* natural iso Φ : Hom(A, ─) ⟹ F *)
}.

Coercion Representable_to_obj `(F : C ⟶ Sets) (R : Representable F) : C :=
  @repr_obj _ _ R.

(*
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   nLab: https://ncatlab.org/nlab/show/representable+functor
   nLab: https://ncatlab.org/nlab/show/Yoneda+embedding

   本节说明自然变换、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ReprInduced.

Universes o h.
Context (C : Category@{o h h}).

(*
   本节说明函子、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma hom_transform_precomp (r r' : C)
  (sigma : [Hom r,─] ~{[C, Sets]}~> [Hom r',─]) (d : C) (g : r ~> d) :
  transform[sigma] d g ≈ g ∘ transform[sigma] r id.
Proof.
  pose proof (@naturality _ _ _ _ sigma r d g id{C}) as N; simpl in N.
  rewrite id_right in N.
  now symmetry.
Qed.

Context {K K' : C ⟶ Sets}.
Context (R : Representable K) (R' : Representable K').

(* 相关说明。 （已译） *)
Definition repr_transport (tau : K ⟹ K')
  : [Hom (@repr_obj _ _ R),─] ~{[C, Sets]}~> [Hom (@repr_obj _ _ R'),─] :=
  from (@represented _ _ R') ∘[Fun] (tau ∘[Fun] to (@represented _ _ R)).

(* ...and arrow it names, value at 恒等 表示
 对象. Unfolded: ψ'⁻¹_r (τ_r (ψ_r id)), so universal element ψ_r id
 K where construction starts. （已译） *)
Definition repr_induced (tau : K ⟹ K') : @repr_obj _ _ R' ~> @repr_obj _ _ R :=
  transform[repr_transport tau] (@repr_obj _ _ R) id.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ReprCompatible (tau : K ⟹ K')
  (hh : @repr_obj _ _ R' ~> @repr_obj _ _ R) : Type :=
  to (@represented _ _ R') ∘[Fun] fmap[Curried_Hom C] (op hh)
    ≈[Fun] tau ∘[Fun] to (@represented _ _ R).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition repr_compatible_at {tau hh} (compat : ReprCompatible tau hh)
  (d : C) (g : @repr_obj _ _ R ~> d) :
  transform[to (@represented _ _ R')] d (g ∘ hh)
    ≈ transform[tau] d (transform[to (@represented _ _ R)] d g) := compat d g.

Definition repr_compatible_of_at {tau : K ⟹ K'}
  {hh : @repr_obj _ _ R' ~> @repr_obj _ _ R}
  (at_ : ∀ (d : C) (g : @repr_obj _ _ R ~> d),
       transform[to (@represented _ _ R')] d (g ∘ hh)
         ≈ transform[tau] d (transform[to (@represented _ _ R)] d g)) :
  ReprCompatible tau hh := at_.

(*
   本节说明 Representable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma repr_induced_compatible (tau : K ⟹ K') :
  ReprCompatible tau (repr_induced tau).
Proof.
  apply repr_compatible_of_at; intros d g.
  unfold repr_induced; simpl.
  rewrite <- (hom_transform_precomp _ _ (repr_transport tau) d g).
  pose proof (iso_to_from (@represented _ _ R') d
    (transform[tau] d (transform[to (@represented _ _ R)] d g))) as HH;
    simpl in HH; rewrite HH.
  srewrite (@fmap_id _ _ K' d); reflexivity.
Qed.

(* Uniqueness: compatible arrow determined condition at one
 place it can probed, 恒等 表示 对象. （已译） *)
Lemma repr_induced_unique (tau : K ⟹ K') hh :
  ReprCompatible tau hh → hh ≈ repr_induced tau.
Proof.
  intro compat.
  pose proof (repr_compatible_at compat (@repr_obj _ _ R) id) as E; simpl in E.
  unfold repr_induced; simpl.
  rewrite <- E.
  pose proof (iso_from_to (@represented _ _ R') (@repr_obj _ _ R)
                (id{C} ∘ hh)) as HH; simpl in HH; rewrite HH.
  now rewrite !id_left.
Qed.

(* The exercise one statement: unique compatible arrow between the
 表示 对象. （已译） *)
Program Definition repr_induced_universal (tau : K ⟹ K') :
  @Unique _ (@homset C (@repr_obj _ _ R') (@repr_obj _ _ R))
          (ReprCompatible tau) := {|
  unique_obj := repr_induced tau;
  unique_property := repr_induced_compatible tau
|}.
Next Obligation. symmetry; now apply repr_induced_unique. Qed.

Lemma repr_induced_respects (tau tau' : K ⟹ K') :
  tau ≈ tau' → repr_induced tau ≈ repr_induced tau'.
Proof.
  intro E; unfold repr_induced; simpl.
  apply proper_morphism, (E (@repr_obj _ _ R) _).
Qed.

End ReprInduced.

Arguments repr_transport {C K K'} R R' tau.
Arguments repr_induced {C K K'} R R' tau.
Arguments ReprCompatible {C K K'} R R' tau hh.
Arguments repr_compatible_at {C K K' R R' tau hh} compat d g.
Arguments repr_compatible_of_at {C K K' R R' tau hh} at_.
Arguments repr_induced_compatible {C K K'} R R' tau.
Arguments repr_induced_unique {C K K'} R R' tau hh.
Arguments repr_induced_universal {C K K'} R R' tau.
Arguments repr_induced_respects {C K K'} R R' tau tau'.

(** ** Functoriality *)

Section ReprInducedLaws.

Universes o h.
Context (C : Category@{o h h}).
Context {K K' K'' : C ⟶ Sets}.
Context (R : Representable K) (R' : Representable K') (R'' : Representable K'').

(* The identity transformation names the identity arrow.  [nat_id]'s component
   is [fmap[K] id] rather than [id] (Theory/Natural/Transformation.v), so
   [fmap_id] is spent once here and once in [repr_induced_compatible]. *)
Lemma repr_induced_id : repr_induced R R nat_id ≈ id.
Proof.
  unfold repr_induced, repr_transport; simpl.
  srewrite (@fmap_id _ _ K (@repr_obj _ _ R)).
  pose proof (iso_from_to (@represented _ _ R) (@repr_obj _ _ R) id{C})
    as HH; simpl in HH; rewrite HH.
  now rewrite id_left.
Qed.

(*
   本节说明 Representable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma repr_induced_comp (tau : K ⟹ K') (tau' : K' ⟹ K'') :
  repr_induced R R'' (tau' ∙ tau)
    ≈ repr_induced R R' tau ∘ repr_induced R' R'' tau'.
Proof.
  symmetry; apply repr_induced_unique.
  apply repr_compatible_of_at; intros d g; simpl.
  rewrite comp_assoc.
  rewrite (repr_compatible_at (repr_induced_compatible R' R'' tau') d _).
  now rewrite (repr_compatible_at (repr_induced_compatible R R' tau) d g).
Qed.

End ReprInducedLaws.

Arguments repr_induced_id {C K} R.
Arguments repr_induced_comp {C K K' K''} R R' R'' tau tau'.

(* 相关说明。 （已译） *)

Section ReprInducedIso.

Universes o h.
Context (C : Category@{o h h}).
Context {K K' : C ⟶ Sets}.
Context (R : Representable K) (R' : Representable K').

(* A natural 同构 已表示的 函子 induces 同构 of
 表示 对象; both triangle laws 复合 law followed
 恒等 law. （已译） *)
Program Definition repr_induced_iso (i : K ≅[Fun] K')
  : @repr_obj _ _ R' ≅ @repr_obj _ _ R := {|
  to   := repr_induced R R' (to i);
  from := repr_induced R' R (from i)
|}.
Next Obligation.
  rewrite <- repr_induced_comp.
  rewrite (repr_induced_respects R R (from i ∙ to i) nat_id).
  - now apply repr_induced_id.
  - apply (iso_from_to i).
Qed.
Next Obligation.
  rewrite <- repr_induced_comp.
  rewrite (repr_induced_respects R' R' (to i ∙ from i) nat_id).
  - now apply repr_induced_id.
  - apply (iso_to_from i).
Qed.

End ReprInducedIso.

Arguments repr_induced_iso {C K K'} R R' i.

Section ReprUnique.

Universes o h.
Context (C : Category@{o h h}).
Context {K : C ⟶ Sets}.
Context (R R' : Representable K).

(* Mac Lane's τ = id case: two representations ONE 函子 have
 canonically isomorphic 表示 对象. This [repr_induced_iso]
 at 恒等 同构; no separate 论元. （已译） *)
Definition repr_unique_iso : @repr_obj _ _ R' ≅ @repr_obj _ _ R :=
  repr_induced_iso R R' iso_id.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition repr_unique_iso_universal :
  @Unique _ (@homset C (@repr_obj _ _ R') (@repr_obj _ _ R))
          (ReprCompatible R R' nat_id) := {|
  unique_obj := to repr_unique_iso;
  unique_property := repr_induced_compatible R R' nat_id
|}.
Next Obligation. symmetry; now apply repr_induced_unique. Qed.

End ReprUnique.

Arguments repr_unique_iso {C K} R R'.
Arguments repr_unique_iso_universal {C K} R R'.

(* 相关说明。 （已译） *)

Section TautologicalRepresentation.

Universes o h.
Context (C : Category@{o h h}).

(* Hom(c, −) represents itself, 恒等 同构. Deliberately a
 plain [Definition] not [Instance]: see header. （已译） *)
Definition Hom_Representable (c : C) : Representable ([Hom c,─]) := {|
  repr_obj := c;
  represented := iso_id
|}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma repr_induced_hom (c c' : C) (f : c' ~> c) :
  repr_induced (Hom_Representable c) (Hom_Representable c')
    (fmap[Curried_Hom C] (op f)) ≈ f.
Proof.
  unfold repr_induced, repr_transport; simpl; unfold op.
  now rewrite !id_left.
Qed.

End TautologicalRepresentation.

Arguments Hom_Representable {C} c.
Arguments repr_induced_hom {C} c c' f.
