Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.

Generalizable All Variables.

(*
   * * Essential uniqueness of limits and colimits

   Riehl, "Category Theory in Context", 2nd ed., §3.1, Proposition
   3.1.7 (printed p. 84) [riehl:3.1:prop7]: any two limit cones over a
   common diagram are related by a UNIQUE isomorphism of apexes
   commuting with the legs.  Both cones are terminal objects of the
   category of cones, and terminal objects form a contractible
   groupoid; the apex may still have non-trivial automorphisms, but
   only the identity commutes with a fixed limit cone.
   nLab: https://ncatlab.org/nlab/show/limit

   The proof is the leg-level argument, taken DIRECTLY from the
   mediator calculus of Structure/Limit/Preservation.v —
   [limit_med] / [limit_med_commutes] / [limit_med_unique] /
   [limit_med_eq] — with no detour through representability: each
   witness's cone factors through the other by a mediator, the two
   composites agree with the identity on every leg and are therefore
   identities ([limit_med_eq]), and the leg-commutation equations are
   the mediators' own defining property.  Riehl's actual content is
   the UNIQUENESS CLAUSE: the isomorphism is unique among morphisms
   commuting with the two leg families ([limit_unique_iso_unique]),
   with the automorphism remark as its one-witness corollary
   ([limit_endo_id]).  The colimit statements are literal op-instances
   of the limit ones — each is the corresponding limit constant at
   (J^op, C^op, F^op), re-typed through Preservation.v's covariant
   [colimit_inj] vocabulary; the forward mediator is even
   definitionally the opposite side's backward one
   ([colimit_unique_to_is_op]).  Not a second proof.

   Downstream reconciliation lives in Structure/Limit/Unique/Compat.v:
   the shape-specific [equalizer_unique] (Structure/Equalizer/Fork.v)
   and [pullback_unique] (Structure/Pullback.v) agree with this
   theorem through the in-tree bridges, and the never-instantiated
   generic route [univ_property_unique_up_to_unique_iso] — in tree
   instantiated only at terminal/initial objects
   (Structure/UniversalProperty/Terminal.v) — is taken at
   [LimitIsUniversalProperty] there, its first instantiation at
   limits.  (Split into a satellite so this
   file stays importable from the elementary files' own dependency
   level.) 

   --------
   * * 极限和余极限的本质唯一性

   Riehl，《上下文中的范畴论》，第二版，第3.1节，命题3.1.7（印刷版第84页）[riehl:3.1:prop7]：任何两个针对同一图的极限锥，通过顶点之间的唯一同构相关联，并且与各腿交换。两个锥都是锥类别的终对象，而终对象形成一个可收缩的群组oid；顶点仍可能有非平凡的自同构，但只有恒等映射与固定的极限锥交换。
   nLab：https://ncatlab.org/nlab/show/limit证明是基于各个支的论证，直接取自 Structure/Limit/Preservation.v 的中介演算——[limit_med] / [limit_med_commutes] / [limit_med_unique] / [limit_med_eq]——没有经过可表示性的绕道：每个见证的锥通过一个中介因子化为另一个，中介的两个复合在每个支上与恒等映射一致，因此是恒等映射（[limit_med_eq]），而支交换方程是中介自身的定义性质。Riehl 的实际内容是唯一性条款：在与两个支族交换的态射中，该同构是唯一的（[limit_unique_iso_unique]），自动同构的注释是其单一见证推论（[limit_endo_id]）。余极限语句是极限语句的字面对偶实例——每一个都是在 (J^op, C^op, F^op) 上的对应极限常数，通过 Preservation.v 的协变 [colimit_inj] 词汇重新类型化；正向中介甚至在定义上是对侧的反向中介 ([colimit_unique_to_is_op])。不是第二个证明。下游对账存在于 Structure/Limit/Unique/Compat.v：
   特定于形状的 [equalizer_unique]（Structure/Equalizer/Fork.v）
   和 [pullback_unique]（Structure/Pullback.v）通过树内桥与该定理一致，
   而从未实例化过的通用路径 [univ_property_unique_up_to_unique_iso] —— 在树内
   仅在终端/初始对象处实例化（Structure/UniversalProperty/Terminal.v）—— 在那里取 [LimitIsUniversalProperty]，
   它在极限处的第一次实例化。（拆分为一个卫星模块，以便该文件仍可从基础文件自身的依赖层导入。）
*)

(* * ** A limit witness, read as a competing cone at its own apex / * ** 一个极限见证人，被读作在其自身顶点的竞争锥 *)

Definition alimit_cone `{F : J ⟶ C} {c : C} (H : IsALimit F c) : Cone F :=
  {| vertex_obj := c; coneFrom := @limit_acone _ _ _ _ H |}.

(* The legs of that cone are the limit legs, definitionally. / 那个圆锥的边是极限边，这是定义上的。 *)
Example alimit_cone_leg `{F : J ⟶ C} {c : C} (H : IsALimit F c) (x : J) :
  cone_leg (alimit_cone H) x = limit_leg H x := eq_refl.

Definition acolimit_cocone `{F : J ⟶ C} {c : C} (H : IsAColimit F c) :
  Cocone F :=
  @Build_Cone (J^op) (C^op) (F^op) c (@limit_acone _ _ _ _ H).

Example acolimit_cocone_inj `{F : J ⟶ C} {c : C} (H : IsAColimit F c)
  (x : J) : cocone_inj (acolimit_cocone H) x = colimit_inj H x := eq_refl.

(** ** Proposition 3.1.7, limits / ** 命题 3.1.7，极限 *)

Section LimitUnique.

Context {J : Category}.
Context {C : Category}.
Context {F : J ⟶ C}.
Context {c d : C}.
Context (Hc : IsALimit F c) (Hd : IsALimit F d).

Definition limit_unique_to : c ~{C}~> d := limit_med Hd (alimit_cone Hc).
Definition limit_unique_from : d ~{C}~> c := limit_med Hc (alimit_cone Hd).

Lemma limit_unique_to_legs (x : J) :
  limit_leg Hd x ∘ limit_unique_to ≈ limit_leg Hc x.
Proof. exact (limit_med_commutes Hd (alimit_cone Hc) x). Qed.

Lemma limit_unique_from_legs (x : J) :
  limit_leg Hc x ∘ limit_unique_from ≈ limit_leg Hd x.
Proof. exact (limit_med_commutes Hc (alimit_cone Hd) x). Qed.

Lemma limit_unique_from_to : limit_unique_from ∘ limit_unique_to ≈ id.
Proof.
  apply (limit_med_eq Hc (alimit_cone Hc)); intro x.
  - transitivity ((limit_leg Hc x ∘ limit_unique_from) ∘ limit_unique_to).
    { apply comp_assoc. }
    transitivity (limit_leg Hd x ∘ limit_unique_to).
    { now rewrite limit_unique_from_legs. }
    exact (limit_unique_to_legs x).
  - apply id_right.
Qed.

Lemma limit_unique_to_from : limit_unique_to ∘ limit_unique_from ≈ id.
Proof.
  apply (limit_med_eq Hd (alimit_cone Hd)); intro x.
  - transitivity ((limit_leg Hd x ∘ limit_unique_to) ∘ limit_unique_from).
    { apply comp_assoc. }
    transitivity (limit_leg Hc x ∘ limit_unique_from).
    { now rewrite limit_unique_to_legs. }
    exact (limit_unique_from_legs x).
  - apply id_right.
Qed.

(* The isomorphism of apexes... / 顶点的同构... *)
Definition limit_unique_iso : c ≅ d := {|
  to := limit_unique_to;
  from := limit_unique_from;
  iso_to_from := limit_unique_to_from;
  iso_from_to := limit_unique_from_to
|}.

(*
 ...carrying the leg-commutation equations in both directions — the
 isomorphism "commutes with the legs of the two limit cones", not a
 bare ≅. 

 --------
 ...在两个方向上传递腿换算方程——同构“与两个极限锥的腿交换”，而不是简单的 ≅。
*)
Definition limit_unique_iso_legs :
  (∀ x : J, limit_leg Hd x ∘ to limit_unique_iso ≈ limit_leg Hc x) *
  (∀ x : J, limit_leg Hc x ∘ from limit_unique_iso ≈ limit_leg Hd x) :=
  (limit_unique_to_legs, limit_unique_from_legs).

(*
 The uniqueness clause — Riehl's content: ANY morphism commuting with
 the two leg families is the isomorphism. 

 --------
 唯一性条款 — Riehl 的内容：任何与两个支族交换的态射都是同构。
*)
Theorem limit_unique_iso_unique (h : c ~{C}~> d) :
  (∀ x : J, limit_leg Hd x ∘ h ≈ limit_leg Hc x) →
  h ≈ to limit_unique_iso.
Proof.
  intro Hh; symmetry.
  exact (limit_med_unique Hd (alimit_cone Hc) h Hh).
Qed.

End LimitUnique.

(*
 The accompanying remark, at a single witness: the only endomorphism
 of the apex commuting with a fixed limit cone is the identity. 

 --------
 附带的备注，在单个证人处：与固定极限锥交换的顶点的唯一自同构是恒等映射。
*)
Theorem limit_endo_id `{F : J ⟶ C} {c : C} (H : IsALimit F c)
  (e : c ~{C}~> c) :
  (∀ x : J, limit_leg H x ∘ e ≈ limit_leg H x) → e ≈ id.
Proof.
  intro He.
  apply (limit_med_eq H (alimit_cone H)); intro x.
  - exact (He x).
  - apply id_right.
Qed.

(* * ** Proposition 3.1.7, colimits — op-instances of the above / * ** 命题 3.1.7，余极限——上述的对偶实例 *)

Section ColimitUnique.

Context {J : Category}.
Context {C : Category}.
Context {F : J ⟶ C}.
Context {c d : C}.
Context (Hc : IsAColimit F c) (Hd : IsAColimit F d).

Definition colimit_unique_to : c ~{C}~> d :=
  @limit_unique_from (J^op) (C^op) (F^op) c d Hc Hd.
Definition colimit_unique_from : d ~{C}~> c :=
  @limit_unique_to (J^op) (C^op) (F^op) c d Hc Hd.

(*
 The colimit mediator IS the opposite limit mediator, definitionally
 — the sense in which this section adds no proof content. 

 --------
 余极限中介者在定义上就是极限中介者的对偶——也就是说，本节在证明内容上没有增加任何东西。
*)
Example colimit_unique_to_is_op :
  colimit_unique_to = @limit_unique_from (J^op) (C^op) (F^op) c d Hc Hd
  := eq_refl.

Lemma colimit_unique_to_injs (x : J) :
  colimit_unique_to ∘ colimit_inj Hc x ≈ colimit_inj Hd x.
Proof. exact (@limit_unique_from_legs (J^op) (C^op) (F^op) c d Hc Hd x). Qed.

Lemma colimit_unique_from_injs (x : J) :
  colimit_unique_from ∘ colimit_inj Hd x ≈ colimit_inj Hc x.
Proof. exact (@limit_unique_to_legs (J^op) (C^op) (F^op) c d Hc Hd x). Qed.

Lemma colimit_unique_from_to :
  colimit_unique_from ∘ colimit_unique_to ≈ id.
Proof. exact (@limit_unique_from_to (J^op) (C^op) (F^op) c d Hc Hd). Qed.

Lemma colimit_unique_to_from :
  colimit_unique_to ∘ colimit_unique_from ≈ id.
Proof. exact (@limit_unique_to_from (J^op) (C^op) (F^op) c d Hc Hd). Qed.

Definition colimit_unique_iso : c ≅ d := {|
  to := colimit_unique_to;
  from := colimit_unique_from;
  iso_to_from := colimit_unique_to_from;
  iso_from_to := colimit_unique_from_to
|}.

Definition colimit_unique_iso_injs :
  (∀ x : J, to colimit_unique_iso ∘ colimit_inj Hc x ≈ colimit_inj Hd x) *
  (∀ x : J, from colimit_unique_iso ∘ colimit_inj Hd x ≈ colimit_inj Hc x) :=
  (colimit_unique_to_injs, colimit_unique_from_injs).

Theorem colimit_unique_iso_unique (h : c ~{C}~> d) :
  (∀ x : J, h ∘ colimit_inj Hc x ≈ colimit_inj Hd x) →
  h ≈ to colimit_unique_iso.
Proof.
  exact (@limit_unique_iso_unique (J^op) (C^op) (F^op) d c Hd Hc h).
Qed.

End ColimitUnique.

Theorem colimit_endo_id `{F : J ⟶ C} {c : C} (H : IsAColimit F c)
  (e : c ~{C}~> c) :
  (∀ x : J, e ∘ colimit_inj H x ≈ colimit_inj H x) → e ≈ id.
Proof. exact (@limit_endo_id (J^op) (C^op) (F^op) c H e). Qed.
