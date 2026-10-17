Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   nLab: https://ncatlab.org/nlab/show/essentially+surjective+functor
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   范畴等价 (equivalence of categories) 是函子 F : C ⟶ D 连同拟逆 G : D ⟶ C，
   其与 F 的复合自然同构于恒等函子。它是范畴同构的标准弱化，也是范畴「相同性」的
   正确概念：保持并反射一切范畴结构。

   本库中函子上的等价 [≈]（[Functor_Setoid]，Theory/Functor.v）是*捆绑的自然同构*：
   一族同构 [∀ x, F x ≅ G x] 加上态射上的共轭连贯条件。等价的两个比较胞因此直接用 [≈]
   陈述：

     equivalence_counit : F ◯ quasi_inverse ≈ Id[D]
     equivalence_unit   : Id[C] ≈ quasi_inverse ◯ F

   又因 [Cat]（Instance/Cat.v）的 hom-setoid 恰是 [Functor_Setoid]，Cat 中的同构*就是*
   范畴等价；下文桥 [Equivalence_to_Cat_Iso]/[Cat_Iso_to_Equivalence] 在两方向定义性
   重打包数据（由两往返推论在 [≈] 下见证）。两胞的捆绑 [≅[Fun]] 形式经
   [Functor_Setoid_Nat_Iso]（Instance/Fun.v）恢复：见一方向的
   [equivalence_counit_iso]/[equivalence_unit_iso] 与另一方向的 [Nat_Isos_to_Equivalence]。

   [EssentiallySurjective] 以分裂、携带选择的风格陈述（比较 Theory/Functor.v 中 [Full]
   的选定截面 [prefmap] 与 Lib/Setoid.v 的分裂 [surjective] 类）：对每个 [d : D] 选定
   原像对象 [eso_obj d]，并带见证同构 [eso_iso d]。经典刻画——满 + 忠实 + 本质满射
   等同于等价——在 Theory/Equivalence/FullFaithful.v；伴随等价在 Theory/Equivalence/Adjoint.v；
   沿等价的极限保持、反射与创造在 Theory/Equivalence/Limit.v；捆绑概念 [C ≃ D] 在
   Theory/Equivalence/Bundled.v。

   本文件*没有任何*内容注册供实例解析：拟逆是选择，绝不可由类型类搜索凭空产生
   （Construction/Opposite/Monoidal.v 的 [Monoidal_op] 约定）。下文所有构造都是普通
   Definition，在使用点显式传入。这也使桥转换的 Cat 层宇宙约束局部于实际使用处。 *)

(*
   nLab: https://ncatlab.org/nlab/show/T%C3%B4hoku
   nLab: https://ncatlab.org/nlab/show/principle+of+equivalence
   nLab: https://ncatlab.org/nlab/show/skeleton+of+a+category
   SEP:  https://plato.stanford.edu/entries/category-theory/

   本节说明自然变换、函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class EssentiallySurjective {C D : Category} (F : C ⟶ D) := {
  eso_obj : D → C;                     (* chosen preimage object *)
  eso_iso (d : D) : F (eso_obj d) ≅ d  (* its image is isomorphic to d *)
}.

(* F is an equivalence of categories when it has a quasi-inverse.  Both
   cells are natural isomorphisms, because [≈] on functors is
   [Functor_Setoid].  The orientation matches the adjunction every
   equivalence refines to (counit F ◯ G ⟹ Id[D], unit Id[C] ⟹ G ◯ F; see
   Theory/Equivalence/Adjoint.v). *)
Class EquivalenceOfCategories {C D : Category} (F : C ⟶ D) := {
  quasi_inverse : D ⟶ C;
  equivalence_counit : F ◯ quasi_inverse ≈ Id[D];
  equivalence_unit   : Id[C] ≈ quasi_inverse ◯ F
}.

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Equivalence_to_Cat_Iso {C D : Category} {F : C ⟶ D}
  (E : EquivalenceOfCategories F) : C ≅[Cat] D :=
  @Build_Isomorphism Cat C D F (@quasi_inverse C D F E)
    (@equivalence_counit C D F E)
    (symmetry (@equivalence_unit C D F E)).

(* ... and conversely: a Cat-isomorphism repacks definitionally as an
   equivalence of categories carried by its [to] functor, quasi-inverted by
   its [from] functor. *)
Definition Cat_Iso_to_Equivalence {C D : Category} (iso : C ≅[Cat] D) :
  EquivalenceOfCategories (to iso) :=
  @Build_EquivalenceOfCategories C D (to iso) (from iso)
    (iso_to_from iso)
    (symmetry (iso_from_to iso)).

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary Cat_Iso_to_Equivalence_to_Cat_Iso {C D : Category}
  (iso : C ≅[Cat] D) :
  Equivalence_to_Cat_Iso (Cat_Iso_to_Equivalence iso) ≈ iso.
Proof. split; reflexivity. Qed.

Corollary Equivalence_to_Cat_Iso_to_Equivalence {C D : Category}
  {F : C ⟶ D} (E : EquivalenceOfCategories F) :
  @quasi_inverse C D F (Cat_Iso_to_Equivalence (Equivalence_to_Cat_Iso E))
    ≈ @quasi_inverse C D F E.
Proof. reflexivity. Qed.

Section QuasiInverse.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context `{E : @EquivalenceOfCategories C D F}.

(* The counit and unit as bundled natural isomorphisms in the functor
   category — the [≈] to [≅[Fun]] direction of the round trip provided by
   [Functor_Setoid_Nat_Iso]. *)
Definition equivalence_counit_iso : F ◯ quasi_inverse ≅[Fun] Id[D] :=
  equiv_iso equivalence_counit.

Definition equivalence_unit_iso : Id[C] ≅[Fun] quasi_inverse ◯ F :=
  equiv_iso equivalence_unit.

(* Componentwise accessors: the pointwise isomorphism families carried by
   the two cells (their `1 projections). *)
Definition equivalence_counit_at (d : D) : F (quasi_inverse d) ≅ d :=
  `1 equivalence_counit d.

Definition equivalence_unit_at (x : C) : x ≅ quasi_inverse (F x) :=
  `1 equivalence_unit x.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma equivalence_unit_to_natural {x y : C} (f : x ~> y) :
  to (equivalence_unit_at y) ∘ f
    ≈ fmap[quasi_inverse] (fmap[F] f) ∘ to (equivalence_unit_at x).
Proof. exact (fun_equiv_to_fmap equivalence_unit x y f). Qed.

Lemma equivalence_unit_from_natural {x y : C} (f : x ~> y) :
  f ∘ from (equivalence_unit_at x)
    ≈ from (equivalence_unit_at y) ∘ fmap[quasi_inverse] (fmap[F] f).
Proof. exact (fun_equiv_fmap_from equivalence_unit x y f). Qed.

Lemma equivalence_counit_to_natural {x y : D} (g : x ~> y) :
  to (equivalence_counit_at y) ∘ fmap[F] (fmap[quasi_inverse] g)
    ≈ g ∘ to (equivalence_counit_at x).
Proof. exact (fun_equiv_to_fmap equivalence_counit x y g). Qed.

Lemma equivalence_counit_from_natural {x y : D} (g : x ~> y) :
  fmap[F] (fmap[quasi_inverse] g) ∘ from (equivalence_counit_at x)
    ≈ from (equivalence_counit_at y) ∘ g.
Proof. exact (fun_equiv_fmap_from equivalence_counit x y g). Qed.

(* The conjugation form of unit naturality: the composite functor
   [quasi_inverse ◯ F] acts on morphisms by conjugation with the unit
   components. *)
Lemma equivalence_unit_conjugate {x y : C} (f : x ~> y) :
  fmap[quasi_inverse] (fmap[F] f)
    ≈ to (equivalence_unit_at y) ∘ f ∘ from (equivalence_unit_at x).
Proof.
  rewrite equivalence_unit_to_natural.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

(* Symmetry: the quasi-inverse is itself an equivalence of categories,
   quasi-inverted by F.  The two cells swap roles, with their orientations
   flipped by symmetry of [≈]. *)
Definition EquivalenceOfCategories_sym :
  EquivalenceOfCategories quasi_inverse :=
  @Build_EquivalenceOfCategories D C quasi_inverse F
    (symmetry equivalence_unit)
    (symmetry equivalence_counit).

End QuasiInverse.

(*
   本节说明函子、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Nat_Isos_to_Equivalence {C D : Category} (F : C ⟶ D) (G : D ⟶ C)
  (counit_iso : F ◯ G ≅[Fun] Id[D]) (unit_iso : Id[C] ≅[Fun] G ◯ F) :
  EquivalenceOfCategories F :=
  @Build_EquivalenceOfCategories C D F G
    (Category.Instance.Fun.iso_equiv counit_iso)
    (Category.Instance.Fun.iso_equiv unit_iso).

(* The identity functor is an equivalence, quasi-inverse itself. *)
Definition EquivalenceOfCategories_Id {C : Category} :
  EquivalenceOfCategories Id[C] :=
  @Build_EquivalenceOfCategories C C Id[C] Id[C]
    (fun_equiv_id_left Id[C])
    (symmetry (fun_equiv_id_left Id[C])).

(*
   Book: Riehl, "Category Theory in Context", Dover 2016, §1.5,

   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Program Instance EssentiallySurjective_Compose
  {C D E : Category} (F : D ⟶ E) (G : C ⟶ D)
  `{@EssentiallySurjective D E F} `{@EssentiallySurjective C D G} :
  EssentiallySurjective (F ◯ G) := {|
  eso_obj := fun e => eso_obj (F:=G) (eso_obj (F:=F) e)
|}.
Next Obligation.
  exact (iso_compose (eso_iso (F:=F) d)
           (fobj_iso F _ _ (eso_iso (F:=G) (eso_obj (F:=F) d)))).
Defined.
