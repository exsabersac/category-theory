Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.

Generalizable All Variables.

(**
The counit/unit (natural-transformation) characterization of an
    adjunction. 

--------
的单位/单位（自然转化）表征
 附属物。 
*)

(*
nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   An adjunction F ⊣ U between F : D ⟶ C (the left adjoint) and U : C ⟶ D
   (the right adjoint) is given here in counit/unit form: a unit
   η : Id ⟹ U ◯ F and a counit ε : F ◯ U ⟹ Id satisfying the two triangle
   (zig-zag) identities. Componentwise these are

     ε (F X) ∘ fmap[F] (η X) ≈ id[F X]   (counit_fmap_unit), i.e. εF ∘ Fη = 1_F,
     fmap[U] (ε X) ∘ η (U X) ≈ id[U X]   (fmap_counit_unit), i.e. Uε ∘ ηU = 1_U.

   This is the data of an adjunction with which the hom-set form
   [Category.Adjunction.Hom] and the universal-morphism form
   [Category.Theory.Adjunction] are shown equivalent: the transposes of the
   identities recover η and ε, and conversely η, ε with these identities
   reconstruct the natural hom-set isomorphism. 

--------
nLab：https://ncatlab.org/nlab/show/adjoint+functor
 维基百科：https://en.wikipedia.org/wiki/Adjoint_functors

 F : D ⟶ C（左伴随）和 U : C ⟶ D 之间的附加 F ⊣ U
 （右伴随）在这里以单位/单位形式给出：一个单位
 η : Id ⟹ U ◯ F 和一个满足两个三角形的单位 ε : F ◯ U ⟹ Id
 （之字形）身份。 按组件来说，这些是

 ε (F X) ∘ fmap[F] (η X) ≈ id[F X] (counit_fmap_unit)，即 εF ∘ Fη = 1_F，
 fmap[U] (ε X) ∘ η (U X) ≈ id[U X] (fmap_counit_unit)，即 Uε ∘ ηU = 1_U。 

这是 hom-set 形式的附加词的数据
 [Category.Adjunction.Hom] 和全态射形式
 [Category.Theory.Adjunction] 显示为等价：
 恒等式恢复 η 和 ε，反之，用这些恒等式恢复 η, ε
 重建自然的 hom-set 同构。 
*)

Section AdjunctionTransform.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

(*
   【Class Adjunction_Transform 语法与字段展开】/ Syntax & field walkthrough
   （口吻对齐 Theory/Functor.v @ c826572；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      伴随的单位/余单位呈现：η : Id ⟹ U◯F 与 ε : F◯U ⟹ Id，加两条三角恒等式。
      Unit/counit presentation of an adjunction, plus triangle identities.
      Haskell 对照：某些 Adjunction 编码里的 unit/counit；与 Theory/Adjunction.v
      的 Hom-同构形式等价（互转见同目录 Universal 等）。
      Equivalent to the Hom-iso form in Theory/Adjunction.v.

   2) 数据字段 / Data fields
      - unit   : Id ⟹ U ◯ F   （η；分量是自然变换）
      - counit : F ◯ U ⟹ Id   （ε）
      二者是 Transform，故自带自然性方块（对 ≈）。
      Both are Transforms, so they carry naturality (up to ≈).

   3) 三角律（均对 ≈）/ Triangle laws (up to ≈)
      - counit_fmap_unit : ε(F X) ∘ F(η X) ≈ id
      - fmap_counit_unit : U(ε X) ∘ η(U X) ≈ id

   阅读顺序：unit → counit → 两条三角 → 与 Hom 形式对照。
   Reading order: unit → counit → triangles → compare with Hom form.
*)

Class Adjunction_Transform := {
  unit   : Id ⟹ U ◯ F;
  counit : F ◯ U ⟹ Id;

  counit_fmap_unit {X} :
    transform[counit] (F X) ∘ fmap[F] (transform[unit] X) ≈ id;
  fmap_counit_unit {X} :
    fmap[U] (transform[counit] X) ∘ transform[unit] (U X) ≈ id
}.

End AdjunctionTransform.

Arguments Adjunction_Transform {C D} F%_functor U%_functor.

Declare Scope adjunction_scope.
Declare Scope adjunction_type_scope.
Bind Scope adjunction_scope with Adjunction_Transform.
Delimit Scope adjunction_type_scope with adjunction_type.
Delimit Scope adjunction_scope with adjunction.
Open Scope adjunction_type_scope.
Open Scope adjunction_scope.

Notation "F ∹ G" := (@Adjunction_Transform _ _ F G)
  (at level 59) : adjunction_type_scope.

Notation "unit[ A ]" := (@unit _ _ _ _ A)
  (at level 9, format "unit[ A ]") : morphism_scope.
Notation "counit[ A ]" := (@counit _ _ _ _ A)
  (at level 9, format "counit[ A ]") : morphism_scope.
