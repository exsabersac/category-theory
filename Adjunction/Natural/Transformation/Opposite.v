Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Natural.Transformation.

Generalizable All Variables.

(** * The opposite (dual) of a unit/counit adjunction.  / * 单位/单位附加词的相反（对偶）。*)

(*
nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   Adjunctions dualize: from F ⊣ U (here [F ∹ U], with F : D ⟶ C the left
   adjoint and U : C ⟶ D the right adjoint) one obtains an adjunction in the
   opposite categories whose *left* adjoint is U^op and whose *right* adjoint is
   F^op, that is, U^op ⊣ F^op (here [U^op ∹ F^op] : C^op ⇄ D^op). The right
   adjoint U becomes the left adjoint after oppositization, and vice versa, as
   the hom-set bijection Hom_C(F d, c) ≅ Hom_D(d, U c) becomes, on reversing
   every hom-set, Hom_{C^op}(c, F^op d) ≅ Hom_{D^op}(U^op c, d), which is exactly
   the defining bijection of U^op ⊣ F^op.

   Under this duality the unit and counit swap roles: reversing 2-cells turns the
   original counit ε : F ◯ U ⟹ Id into the *unit* Id ⟹ F^op ◯ U^op of the
   opposite adjunction, and the original unit η : Id ⟹ U ◯ F into its *counit*
   U^op ◯ F^op ⟹ Id. Accordingly the new [unit] field is built from [counit]
   and the new [counit] field from [unit], with the two naturality orientations
   (naturality/naturality_sym) exchanged because op reverses naturality squares.
   The two triangle identities map onto each other in the same swapped way: the
   opposite adjunction's triangles are [fmap_counit_unit] and [counit_fmap_unit]
   of the original, reused on the nose. 

--------
nLab：https://ncatlab.org/nlab/show/adjoint+functor
 维基百科：https://en.wikipedia.org/wiki/Adjoint_functors

附加词对偶化：来自 F ⊣ U（此处为 [F ∹ U]，左侧为 F : D ⟶ C
 伴随词和 U : C ⟶ D 右伴随词) 得到一个伴随词
 相反类别，其*左*伴随词是 U^op，其*右*伴随词是
 F^op，即 U^op ⊣ F^op （此处 [U^op ∹ F^op] : C^op ⇄ D^op）。 右边的
 伴随 U 在对立后成为左伴随，反之亦然，如下
 hom 集双射 Hom_C(F d, c) ≅ Hom_D(d, U c) 在反转时变为
 每个 hom 集，Hom_{C^op}(c, F^op d) ≅ Hom_{D^op}(U^op c, d)，这正是
 U^op ⊣ F^op 的定义双射。

在这种二元性下，单位和单位互换角色：颠倒 2 单元就变成了
 原计数 ε : F ◯ U ⟹ Id 进入 *unit* Id ⟹ F^op ◯ U^op
 相反的附加词，并将原始单位 η : Id ⟹ U ◯ F 转换为它的 *counit*
 U^op ◯ F^op ⟹ 同上。 因此，新的 [unit] 字段是从 [counit] 构建的
 以及 [unit] 的新 [counit] 场，具有两个自然方向
 (naturality/naturality_sym) 被交换，因为 op 反转了自然性平方。 
两个三角形恒等式以相同的交换方式相互映射：
 对边附属三角形是 [fmap_counit_unit] 和 [counit_fmap_unit]
 原来的，重复使用在鼻子上。 
*)

Program Definition Opposite_Adjunction_Transform
        `(F : D ⟶ C) `(U : C ⟶ D) (A : F ∹ U) :
  U^op ∹ F^op := {|
  unit := _;
  counit := _
|}.
Next Obligation.
  transform; simpl; intros.
  - apply counit.
  - apply (@naturality_sym _ _ _ _ counit).
  - apply (@naturality _ _ _ _ counit).
Defined.
Next Obligation.
  transform; simpl; intros.
  - apply unit.
  - apply (@naturality_sym _ _ _ _ unit).
  - apply (@naturality _ _ _ _ unit).
Defined.
Next Obligation.
  apply fmap_counit_unit.
Defined.
Next Obligation.
  apply counit_fmap_unit.
Defined.

(*
Oppositization is involutive on adjunctions: applying it twice recovers the
   original [A] on the nose. This holds because (F^op)^op = F definitionally and
   the construction merely swaps the unit/counit and naturality fields, so a
   second swap restores them; hence the equality is provable by [reflexivity]. 

--------
对立在附加词上是内卷的：应用它两次可以恢复
 鼻子上原来的 [A]。 这成立是因为 (F^op)^op = F 定义上并且
 该结构仅交换单位/单位和自然场，因此
 第二次交换恢复它们； 因此，[reflexivity] 可以证明等式。 
*)

Corollary Opposite_Adjunction_Transform_invol
          `(F : D ⟶ C) `(U : C ⟶ D) (A : F ∹ U) :
  Opposite_Adjunction_Transform
    (U^op) (F^op) (Opposite_Adjunction_Transform F U A) = A.
Proof. reflexivity. Qed.
