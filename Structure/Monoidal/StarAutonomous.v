Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
 The homset isomorphisms of the closed structure live in [Sets], so
 [Instance/Sets] is in scope; suppress its product-monoidal instance as a
 typeclass hint so that `⨂` resolves to the ambient [SymMonClosed]/[Monoidal]
 structure on `C` rather than the tensor of [Sets].  Structure/Monoidal/Closed
 performs the same removal for exactly this reason. 

 --------
 闭结构的同构集同态存在于 [Sets]，因此 [Instance/Sets] 在作用域内；将其乘积-单态实例作为类型类提示抑制，以便 `⨂` 解析为 `C` 上的环境 [SymMonClosed] / [Monoidal] 结构，而不是 [Sets] 的张量。Structure/Monoidal/Closed 出于完全相同的原因执行相同的移除操作。
*)
Remove Hints Sets_Product_Monoidal : typeclass_instances.

(* * * Star-autonomous categories (definition level) / * * 星自律范畴（定义层面） *)

(*
 nLab:      https://ncatlab.org/nlab/show/star-autonomous+category
 nLab:      https://ncatlab.org/nlab/show/dualizing+object
 Wikipedia: https://en.wikipedia.org/wiki/Star-autonomous_category

 A *-autonomous (star-autonomous) category is a symmetric monoidal closed
 category C equipped with a DUALIZING OBJECT `⊥ : C` (here [dualizer]): an
 object such that the canonical map from every `x` into its double dual

 x ~> (x ⇒ ⊥) ⇒ ⊥

 is an isomorphism.  Writing the internal-hom into the dualizer as the
 contravariant DUAL functor

 (-)^*  :=  (- ⇒ ⊥)  :  C^op ⟶ C,

 the defining datum is a natural isomorphism `x ≅ x^*^*` together with the
 closed transpose `Hom(x ⨂ y, ⊥) ≅ Hom(x, y ⇒ ⊥)` exhibiting `y ⇒ ⊥` as the
 dual of `y`.  This is the categorical semantics of classical multiplicative
 linear logic: `⊗` is the multiplicative conjunction, the dual is linear
 negation, and the dualizing object is the unit `⊥` of the multiplicative
 disjunction `⅋`.

 BASE.  A *-autonomous category is symmetric monoidal CLOSED, so the base must
 supply a genuine internal hom over a possibly NON-cartesian tensor.  The
 library's [ClosedMonoidal] (Structure/Monoidal/Closed.v) bundles the
 genuinely cartesian [CartesianMonoidal]; but over a cartesian closed base a
 dualizing object forces the category to be a preorder (a standard no-go
 result), collapsing [StarAutonomous] to a vacuous predicate in every
 nondegenerate model and excluding the intended examples — the category `Rel`
 of relations, finite-dimensional vector spaces, coherence spaces.  We
 therefore introduce the general base [SymMonClosed] below: the internal hom
 `⇒`, the tensor-hom adjunction `exp_iso` in isomorphism-of-homsets form, and
 its universal property [ump_exponents], over an arbitrary [SymmetricMonoidal]
 structure.  [SymMonClosed] is [ClosedMonoidal] verbatim with the cartesian
 field replaced by a symmetric monoidal one, so every accessor name
 (`exponent_obj`, `exp_iso`, `eval'`, `ump_exponents'`) agrees and the
 cartesian [ClosedMonoidal] is exactly the special case where `⨂` is the
 categorical product.  We do NOT use Structure/Closed.v, an Eilenberg-Kelly
 closed placeholder carrying no tensor-hom adjunction.

 SCOPE (ledger 4).  This file is definition-level only.  The multiplicative
 disjunction `⅋` (par), the linear-distributivity / linearly-distributed
 structure relating `⨂` and `⅋`, and any coherence beyond the three fields of
 [StarAutonomous] are OUT of scope and go to ledger entry 4.  No concrete
 instance is constructed here.

 PRECISION (necessary vs. sufficient — ledger 4).  The three fields make
 [StarAutonomous C] a condition that every genuine *-autonomous category
 satisfies, but NOT yet a sufficient one.  [star_double_dual] posits SOME
 natural isomorphism `x ≅ (x ⇒ ⊥) ⇒ ⊥` as data, rather than requiring the
 CANONICAL dualization map — the transpose of `eval'` through the symmetric
 braid — to be invertible; a model could in principle meet the field with an
 incidental iso that is not the canonical map.  Likewise [star_transpose] is
 definitionally `exp_iso` at the dualizer, so it records data every
 [SymMonClosed] already supplies and constrains no model.  Pinning
 [star_double_dual] to the canonical map and requiring it to be an
 isomorphism (equivalently, the Barr coherence tying the iso to the closed
 structure) is the star-autonomous coherence deferred to ledger entry 4.

 DEVIATION (transpose used for the dual functor).  The monoidal
 [ump_exponents'] field is stated in existence-and-uniqueness form,
 `∃! h, f ≈ eval' ∘ (h ⨂ id)`, and is NOT wired to `curry := to exp_iso`.
 Consequently the beta law `eval' ∘ (curry f ⨂ id) ≈ f` for the packaged
 `curry` is not derivable from the class fields alone.  We therefore transpose
 with the UMP WITNESS itself, [dcur] below, whose defining beta law [dcur_beta]
 and uniqueness [dcur_uniq] come straight from [ump_exponents]; this makes the
 dual functor's [fmap_comp] provable with no additional assumptions. 

 --------
 nLab:       https://ncatlab.org/nlab/show/star-autonomous+category 
 nLab:       https://ncatlab.org/nlab/show/dualizing+object 
 Wikipedia:  https://en.wikipedia.org/wiki/Star-autonomous_category 

 *-自治（星自治）范畴是一个配备有对偶化对象 `⊥ : C`（这里是 [dualizer] ）的对称幺半闭范畴 C：一个对象，使得从每个 `x` 到其双对偶的典型映射

 x ~> (x ⇒ ⊥) ⇒ ⊥

 是同构。将内函数对象映射到对偶器中记作逆变对偶函子

 (-)^*  :=  (- ⇒ ⊥)  :  C^op ⟶ C,定义的数据是一个自然同构 `x ≅ x^*^*`，以及闭转置 `Hom(x ⨂ y, ⊥) ≅ Hom(x, y ⇒ ⊥)`，它将 `y ⇒ ⊥` 显示为 `y` 的对偶。这是经典乘法线性逻辑的范畴语义：`⊗` 是乘法合取，对偶是线性否定，且对偶对象是乘法析取 `⅋` 的单位 `⊥`。基础。一个 *-自冗余类别是对称幺半闭的，因此基础必须提供一个在可能非笛卡尔张量上的真实内部 Hom。库中的 [ClosedMonoidal] (Structure/Monoidal/Closed.v) 打包了真正的笛卡尔 [CartesianMonoidal]；但是在一个笛卡尔闭基础上，一个对偶化对象会迫使类别成为一个偏序集（一个标准的不可能结果），将 [StarAutonomous] 在每个非退化模型中折叠为一个空洞谓词，并排除预期的例子——关系、有限维向量空间、一致性空间组成的类别 `Rel`。因此，我们在下面引入一般基础 [SymMonClosed]：内部 Hom `⇒`，在 Hom 集同构形式下的张量-Hom 对偶 `exp_iso`，以及它的普遍性质 [ump_exponents]，在任意 [SymmetricMonoidal] 结构上。[SymMonClosed] 是 [ClosedMonoidal] 的逐字对应，只不过将笛卡尔场替换为对称幺半群场，因此每个访问器名称（`exponent_obj`、`exp_iso`、`eval'`、`ump_exponents'`）都一致，而笛卡尔 [ClosedMonoidal] 则恰好是 `⨂` 是范畴积的特殊情况。我们不使用 Structure/Closed.v，这是一个 Eilenberg-Kelly 闭占位符，不携带张量-同构伴随。

 范围 (账本 4)。此文件仅涉及定义层面。乘法析取 `⅋`（par）、线性分配/线性分布结构关联 `⨂` 和 `⅋`，以及超出 [StarAutonomous] 三个字段之外的任何相干性均不在范围内，应记录在账本条目 4。本处未构造任何具体实例。精确性（必要 vs. 充分 — 账簿 4）。这三个领域使得 [StarAutonomous C] 成为每个真正的 *-自律范畴都满足的条件，但尚不是充分条件。[star_double_dual] 假设某些自然同构 `x ≅ (x ⇒ ⊥) ⇒ ⊥` 作为数据，而不是要求 CANONICAL 对偶映射——通过对称编织的 `eval'` 的转置——是可逆的；原则上，一个模型可以通过一个偶然的同构而不是标准映射来满足该领域。同样地，[star_transpose] 在双子器处在定义上等于 `exp_iso`，因此它记录了每个 [SymMonClosed] 已经提供的数据，并且对模型没有约束。固定 [star_double_dual] 到典型映射并要求它成为同构（等价地，将同构绑到封闭结构的巴尔一致性）是推迟到账目条目 4 的星自反一致性。

 偏差（复合用于对偶函子）。单体 [ump_exponents'] 域以存在性和唯一性形式 `∃! h, f ≈ eval' ∘ (h ⨂ id)` 表示，且未连接到 `curry := to exp_iso`。因此，打包的 `curry` 的 beta 法则 `eval' ∘ (curry f ⨂ id) ≈ f` 无法仅从类域推导。因此，我们用 UMP 证人本身 [dcur] 做转置，其定义的 beta 法则 [dcur_beta] 和唯一性 [dcur_uniq] 直接来自 [ump_exponents]；这使得对偶函子 [fmap_comp] 可在无需额外假设的情况下证明。
*)

(*
   * ** The genuine symmetric monoidal closed base

   [SymMonClosed] is [ClosedMonoidal] (Structure/Monoidal/Closed.v) verbatim
   except that the underlying `⨂`-structure is an arbitrary [SymmetricMonoidal]
   rather than the [CartesianMonoidal] bundled there.  It packages the internal
   hom `⇒`, the tensor-hom adjunction `exp_iso` in the isomorphism-of-homsets
   form `x ⨂ y ~> z ≊ x ~> y ⇒ z`, and the universal property [ump_exponents']
   in existence-and-uniqueness form.  Keeping the field names identical to
   [ClosedMonoidal] lets the dual functor and the star-autonomous class below
   read exactly as over the cartesian base, now with non-cartesian models
   available. 

   --------
   * ** 真正的对称单体闭基

   [SymMonClosed] 是 [ClosedMonoidal]（Structure/Monoidal/Closed.v）逐字
   除了其底层的 `⨂`-结构是任意的 [SymmetricMonoidal]，
   而不是那里捆绑的 [CartesianMonoidal]。它封装了内部
   同态 `⇒`、张量-同态伴随 `exp_iso` 在同态集合
   同构形式 `x ⨂ y ~> z ≊ x ~> y ⇒ z` 下，以及存在唯一性形式的普遍性质 [ump_exponents']。
   保持字段名称与 [ClosedMonoidal] 相同，使得下面的对偶函子和星自发类
   能够像在笛卡尔基底上一样精确地读取，现在可用非笛卡尔模型。
*)

Section SMClosed.

Context {C : Category}.

Reserved Infix "⇒" (at level 30, right associativity).

Class SymMonClosed := {
  smc_is_symmetric : @SymmetricMonoidal C;   (* the underlying ⨂-structure / 基础 ⨂-结构 *)

  exponent_obj : obj → obj → obj    (* internal hom; x ⇒ y = exponent_obj x y / 内部同态；x ⇒ y = 指数对象 x y *)
    where "x ⇒ y" := (exponent_obj x y);

  exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z;

  curry'   {x y z} : x ⨂ y ~> z → x ~> y ⇒ z := to (@exp_iso x y z);
  uncurry' {x y z} : x ~> y ⇒ z → x ⨂ y ~> z := from (@exp_iso x y z);

  eval' {x y} : (x ⇒ y) ⨂ x ~> y := @uncurry' _ _ _ id;

  ump_exponents' {x y z} (f : x ⨂ y ~> z) :
    ∃! h : x ~> y ⇒ z, f ≈ eval' ∘ (h ⨂ id)
}.
#[export] Existing Instance smc_is_symmetric.

Coercion smc_is_symmetric : SymMonClosed >-> SymmetricMonoidal.

Notation "x ⇒ y" := (exponent_obj x y)
  (at level 30, right associativity) : object_scope.

Context `{SymMonClosed}.

Definition ump_exponents {x y z} (f : x ⨂ y ~> z) :
  ∃! h : x ~> y ⇒ z, f ≈ eval' ∘ (h ⨂ id) := @ump_exponents' _ x y z f.

Arguments eval' {_ _ _} /.

End SMClosed.

Notation "x ⇒ y" := (exponent_obj x y)
  (at level 30, right associativity) : category_scope.

Section StarAutonomous.

Context {C : Category}.
Context `{@SymMonClosed C}.

#[local] Obligation Tactic := idtac.

(*
   * ** The UMP transpose

   [dcur f] is the unique transpose supplied by [ump_exponents]; unlike the
   packaged `curry` (which is `to exp_iso` and is not, over this class, known
   to satisfy the beta law), [dcur] carries the beta law [dcur_beta] and the
   uniqueness principle [dcur_uniq] definitionally. 

   --------
   * ** UMP 转置

   [dcur f] 是由 [ump_exponents] 提供的唯一转置；与打包的 `curry`（它是 `to exp_iso`，并且在此类上尚不为人知满足 β 律）不同，[dcur] 从定义上承载了 β 律 [dcur_beta] 和唯一性原则 [dcur_uniq]。
*)

Definition dcur {x y z : C} (f : x ⨂ y ~> z) : x ~> y ⇒ z :=
  unique_obj (ump_exponents f).

Lemma dcur_beta {x y z : C} (f : x ⨂ y ~> z) :
  f ≈ eval' ∘ (dcur f ⨂ id).
Proof. exact (unique_property (ump_exponents f)). Qed.

Lemma dcur_uniq {x y z : C} (f : x ⨂ y ~> z) (v : x ~> y ⇒ z) :
  f ≈ eval' ∘ (v ⨂ id) -> dcur f ≈ v.
Proof. exact (uniqueness (ump_exponents f) v). Qed.

#[local] Program Instance dcur_respects {x y z : C} :
  Proper (equiv ==> equiv) (@dcur x y z).
Next Obligation.
  proper.
  apply dcur_uniq.
  match goal with [ Heq : _ ≈ _ |- _ ] => rewrite Heq end.
  apply dcur_beta.
Qed.

(*
   * Two bookkeeping slides for the tensor bifunctor, factoring a joint action
   `u ⨂ v` through the two one-sided actions in either order. 

   --------
   * 关于张量双函子的两个记账幻灯片，通过两个单边作用的任意顺序，将联合作用 `u ⨂ v` 分解。
*)

Lemma bimap_slide_l {a a' b b' : C} (u : a ~> a') (v : b ~> b') :
  u ⨂ v ≈ (u ⨂ id) ∘ (id ⨂ v).
Proof.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Lemma bimap_slide_r {a a' b b' : C} (u : a ~> a') (v : b ~> b') :
  u ⨂ v ≈ (id ⨂ v) ∘ (u ⨂ id).
Proof.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(*
   * ** The dual (linear-negation) functor `(- ⇒ d) : C^op ⟶ C`

   Contravariant in its argument: a morphism `f : y ~> x` in C is a morphism
   `x ~> y` in `C^op`, and is sent to the precomposition-in-the-exponent map
   `(x ⇒ d) ~> (y ⇒ d)`. 

   --------
   * ** 双（线性否定）函子  `(- ⇒ d) : C^op ⟶ C`

   对其参数是逆变的：在 C 中的态射  `f : y ~> x`  是  `C^op` 中的态射  `x ~> y` ，并被映射到指数中的前合成映射  `(x ⇒ d) ~> (y ⇒ d)` 。
*)

Lemma dual_hom_comp (d : C) {x y z : C} (f : z ~> y) (g : y ~> x) :
  dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ (g ∘ f)))
    ≈ dcur (eval' ∘ (@id _ (y ⇒ d) ⨂ f))
        ∘ dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g)).
Proof.
  apply dcur_uniq.
  transitivity (eval' ∘ (dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g)) ⨂ f)).
  - (* left leg: fold `g`'s beta law back into `id ⨂ (g ∘ f)` / 左腿：将 `g` 的 β 法则折回到 `id ⨂ (g ∘ f)` *)
    symmetry.
    rewrite (bimap_slide_l (dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g))) f).
    rewrite comp_assoc.
    rewrite <- (dcur_beta (eval' ∘ (@id _ (x ⇒ d) ⨂ g))).
    rewrite <- comp_assoc.
    rewrite <- bimap_comp_id_left.
    reflexivity.
  - (* right leg: fold `f`'s beta law back into `dcur (…g…) ⨂ f` / 右腿：将 `f` 的 β 法则折回到 `dcur (…g…) ⨂ f` *)
    rewrite (bimap_comp_id_right
               (dcur (eval' ∘ (@id _ (y ⇒ d) ⨂ f)))
               (dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g)))).
    rewrite comp_assoc.
    rewrite <- (dcur_beta (eval' ∘ (@id _ (y ⇒ d) ⨂ f))).
    rewrite <- comp_assoc.
    rewrite <- (bimap_slide_r (dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g))) f).
    reflexivity.
Qed.

Program Definition dual (d : C) : C^op ⟶ C := {|
  fobj := fun x => @exponent_obj C _ x d;
  fmap := fun x y f => dcur (eval' ∘ (id ⨂ (f : y ~{C}~> x)))
|}.
Next Obligation.
  (* fmap respects ≈ / fmap 遵守 ≈ *)
  proper.
  apply dcur_respects.
  match goal with [ Heq : _ ≈ _ |- _ ] => now rewrite Heq end.
Qed.
Next Obligation.
  (* fmap preserves identities / fmap 保持恒等式 *)
  intros.
  apply dcur_uniq.
  reflexivity.
Qed.
Next Obligation.
  (* fmap preserves composition / fmap 保持组合性 *)
  intros.
  apply dual_hom_comp.
Qed.

(** The double-dual endofunctor `(-)^*^* : C ⟶ C`. / 双对偶自函子 `(-)^*^* : C ⟶ C` 。 *)
Definition double_dual (d : C) : C ⟶ C := dual d ◯ (dual d)^op.

(*
   * ** Star-autonomous structure

   The three defining fields over the closed monoidal base: a dualizing object,
   the closed transpose exhibiting `y ⇒ ⊥` as the dual of `y` (this is
   `exp_iso` at the dualizer, recorded here as data), and the double-dual
   isomorphism together with its naturality. 

   --------
   * ** 星自治结构

   在闭单体基上的三个定义字段：一个对偶化对象，
   闭转置展示了 `y ⇒ ⊥` 作为 `y` 的对偶（这是在对偶化器处的 `exp_iso`，在此作为数据记录），以及双对偶同构及其自然性。
*)

Class StarAutonomous : Type := {
  dualizer : C;

  (* `Hom(x ⨂ y, ⊥) ≅ Hom(x, y ⇒ ⊥)`, the closed transpose at the dualizer. / `Hom(x ⨂ y, ⊥) ≅ Hom(x, y ⇒ ⊥)` ，在二重化器处的闭合转置。 *)
  star_transpose {x y : C} :
    (x ⨂ y ~> dualizer) ≊ (x ~> dual dualizer y);

  (* the double-dual isomorphism `x ≅ x^*^*` / 双重对偶同构 `x ≅ x^*^*` *)
  star_double_dual {x : C} :
    x ≅ double_dual dualizer x;

  (* naturality of the double-dual isomorphism / 双重对偶同构的自然性 *)
  star_natural {a b : C} (f : a ~> b) :
    to (star_double_dual (x:=b)) ∘ f
      << a ~~> double_dual dualizer b >>
    fmap[double_dual dualizer] f ∘ to (star_double_dual (x:=a))
}.

End StarAutonomous.

Arguments dcur {C _ x y z} f.
Arguments dual {C _} d.
Arguments double_dual {C _} d.
Arguments StarAutonomous C {_}.
Arguments dualizer {C _ _}.
