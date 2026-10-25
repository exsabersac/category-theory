Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.

Generalizable All Variables.

(* * * The category of commutative monoids / * * 交换幺半群的范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/CMon
 nLab:      https://ncatlab.org/nlab/show/commutative+monoid
 Wikipedia: https://en.wikipedia.org/wiki/Monoid#Commutative_monoid

 [CMon] is the category of commutative monoids over [Sets]: an object is a
 setoid carrying a commutative, associative binary operation [cmon_plus]
 with unit [cmon_zero], whose `≈` is PROPOSITIONAL ([cmon_prop]); a morphism
 is a setoid map preserving both; two morphisms are equivalent when their
 underlying maps agree pointwise.

 An earlier revision of this paragraph named only the operation, the unit and
 the laws.  Since the PR "algebraic carriers are sets" (2026-09-17) the record
 carries a fourth kind of datum, the field [cmon_prop] of
 Lib/Setoid/Propositional.v's class [PropEquiv]: a [Prop]-valued relation on
 the carrier that holds exactly when `≈` does.  A commutative monoid in this
 library is therefore a commutative monoid on a SET in Bishop's sense, not on
 an arbitrary proof-relevant setoid.  Lib/Setoid/Propositional.v's header says
 why -- a type of congruences on a carrier is carrier-sized exactly when the
 congruences are [Prop]-valued, which is what the solution-set condition of
 Mac Lane's general adjoint functor theorem needs at a concrete algebraic
 category.  The whole tower over [CMon] -- [Ab], [RMod R], and everything
 coerced into them -- inherits the field through [ab_cmon] and [rm_ab], and
 [RigObject] carries the twin field [rig_prop] (Theory/Algebra/Rig.v), since
 [rig_cmon] builds a [CMonObject] out of a rig's own carrier setoid.

 The in-tree alternative — commutative monoid OBJECTS in a symmetric
 monoidal category (Theory/Algebra/CommutativeMonoid.v, instantiable at
 [Sets_Product_Monoidal], with the hom-category pattern of
 Theory/Algebra/Monoid/Hom.v) — is deliberately not taken here: the
 biproduct/preadditive development (Instance/CMon/Biproduct.v) wants
 direct carrier-level access to [cmon_plus] and [cmon_zero], without the
 monoidal-object indirection.  Since [Mon] already names the internal
 monoid category of Theory/Algebra/Monoid/Hom.v, the vocabulary here is
 [CMonObject], [CMonHom], [CMon]. 

 --------
 nLab:       https://ncatlab.org/nlab/show/CMon 
 nLab:       https://ncatlab.org/nlab/show/commutative+monoid 
 Wikipedia:  https://en.wikipedia.org/wiki/Monoid#Commutative_monoid 

 [CMon] 是 [Sets] 上交换幺半群的范畴：一个对象是携带一个交换且结合的二元运算 [cmon_plus] 的集合类，单位为 [cmon_zero]，其 `≈` 是命题性的 ([cmon_prop])；一个态射是保持两者的集合类映射；当两个态射的基础映射在每一点上都相同时，它们被认为是等价的。这一段的早期修订版本仅提到了运算、单位元和公理。自从PR“代数载体是集合”（2026-09-17）之后，记录增加了第四种数据类型，即Lib/Setoid/Propositional.v中类[PropEquiv]的字段[cmon_prop]：一个以[Prop]为值的关系，仅当`≈`成立时该关系成立。因此，该库中的交换幺半群在Bishop的意义上是一个SET上的交换幺半群，而不是任意的具有证明相关性的集合体。Lib/Setoid/Propositional.v的标题说明了原因——当同余类为[Prop]值时，载体上的同余类型的大小正好与载体相同，这恰好满足Mac Lane的一般伴随函子定理在具体代数范畴中所需的解集条件。整个塔从 [CMon] -- [Ab]、[RMod R] 以及所有被强制归入它们的东西 -- 通过 [ab_cmon] 和 [rm_ab] 继承了该域，[RigObject] 携带双重域 [rig_prop]（理论/代数/架.v），因为 [rig_cmon] 使用一个架自身的承载集合体构建了一个 [CMonObject]。树内的替代方案——对称幺半群范畴中的交换幺半群对象（Theory/Algebra/CommutativeMonoid.v，可在 [Sets_Product_Monoidal] 上实例化，具有 Theory/Algebra/Monoid/Hom.v 的同态范畴模式）——在这里故意没有采用：双积/预加性的发展（Instance/CMon/Biproduct.v）需要对 [cmon_plus] 和 [cmon_zero] 进行直接载体层访问，而不通过幺半群对象间接访问。由于 [Mon] 已经命名了 Theory/Algebra/Monoid/Hom.v 中的内部幺半群范畴，这里的词汇是 [CMonObject]、[CMonHom]、[CMon]。
*)

(*
 A commutative monoid: a setoid whose `≈` is propositional, together with a
 unit element and a binary operation that respects `≈` and satisfies the
 commutative monoid laws up to `≈`.

 [cmon_prop] is the LAST field deliberately.  Every construction site in the
 tree writes the record with named fields under [Program], and [Program]
 emits its obligations in field order; putting the new field last leaves the
 numbering of every existing obligation alone and adds one at the end. 

 --------
 交换幺半群：一个集合论，其中 `≈` 是命题性的，同时具有一个单位元和一个遵守 `≈` 的二元运算，并且满足交换幺半群定律直到 `≈`。

 [cmon_prop] 是特意放在最后的字段。树中的每一个构造现场都在 [Program] 下以命名字段的形式写入记录，而 [Program] 以字段顺序发布其义务；将新字段放在最后不会改变现有所有义务的编号，只会在最后增加一个。
*)
Record CMonObject := {
  cmon_setoid :> SetoidObject;

  cmon_zero : carrier cmon_setoid;
  cmon_plus : carrier cmon_setoid → carrier cmon_setoid → carrier cmon_setoid;

  cmon_plus_respects : Proper (equiv ==> equiv ==> equiv) cmon_plus;

  cmon_plus_assoc : ∀ a b c,
    cmon_plus (cmon_plus a b) c ≈ cmon_plus a (cmon_plus b c);
  cmon_plus_comm : ∀ a b, cmon_plus a b ≈ cmon_plus b a;
  cmon_plus_zero_l : ∀ a, cmon_plus cmon_zero a ≈ a;

  (*
 The carrier is a SET: its `≈` is logically equivalent to a [Prop]-valued
 relation.  See Lib/Setoid/Propositional.v. 

 --------
 载体是一个集合：它的 `≈` 在逻辑上等价于一个取值为 [Prop] 的关系。请参见 Lib/Setoid/Propositional.v。
*)
  cmon_prop : PropEquiv (is_setoid cmon_setoid)
}.

#[export] Existing Instance cmon_plus_respects.
#[export] Existing Instance cmon_prop.

(* The right unit law follows from the left one by commutativity. / 右单位律可以通过交换律由左单位律得出。 *)
Corollary cmon_plus_zero_r (M : CMonObject) (a : carrier (cmon_setoid M)) :
  cmon_plus M a (cmon_zero M) ≈ a.
Proof.
  rewrite cmon_plus_comm.
  apply cmon_plus_zero_l.
Qed.

(* A homomorphism of commutative monoids: a setoid map on the carriers that preserves the unit and the operation. / 交换幺半群的同态：作用在载体上的集合映射，保持单位元和运算。 *)
Record CMonHom (M N : CMonObject) := {
  cmon_map :> SetoidMorphism (cmon_setoid M) (cmon_setoid N);

  cmon_map_zero : cmon_map (cmon_zero M) ≈ cmon_zero N;
  cmon_map_plus : ∀ a b,
    cmon_map (cmon_plus M a b) ≈ cmon_plus N (cmon_map a) (cmon_map b)
}.

Arguments cmon_map {M N} _.
Arguments cmon_map_zero {M N} _.
Arguments cmon_map_plus {M N} _ _ _.

#[local] Obligation Tactic := idtac.

(* The hom-setoid: homomorphisms are compared by their underlying maps, pointwise up to the codomain's `≈` (as in [Sets]). / 同态集: 同态通过其底层映射进行比较，在值域的 `≈` 上逐点比较（如 [Sets] 所示）。 *)
#[export]
Program Instance CMonHom_Setoid {M N : CMonObject} : Setoid (CMonHom M N) := {|
  equiv := fun f g => ∀ a, cmon_map f a ≈ cmon_map g a
|}.
Next Obligation.
  intros M N.
  constructor.
  - intros f a.
    reflexivity.
  - intros f g Hfg a.
    symmetry.
    apply Hfg.
  - intros f g h Hfg Hgh a.
    transitivity (cmon_map g a).
    + apply Hfg.
    + apply Hgh.
Qed.

(*
 L1: the hom-setoid is propositional, pointwise into the CODOMAIN's own
 [cmon_prop].  The domain needs nothing -- the relation quantifies over its
 carrier but never compares two of its elements.  This is the same shape as
 [hom_PropEquiv] (Instance/Sets/Propositional.v), restated here because
 [CMonHom_Setoid] is a setoid on [CMonHom M N] rather than on
 [SetoidMorphism]s, and the two records are not convertible.

 Measured (About under Set Printing Universes):

 CMonHom_PropEquiv@{u} :
 ∀ {M N : CMonObject@{u u u}}, PropEquiv@{u u} CMonHom_Setoid@{u}
 ( * u |=  * )

 -- one universe and no constraint: the transport neither raises the level
 nor pins it. 

 --------
 L1: hom-集合体是命题性的，逐点映入到余域自身的 [cmon_prop]。域无需任何操作——该关系对其承载体进行量化，但从不比较其两个元素。这与 [hom_PropEquiv]（Instance/Sets/Propositional.v）的形状相同，在此重述因为 [CMonHom_Setoid] 是 [CMonHom M N] 上的一个集合体，而不是 [SetoidMorphism] 上的，并且这两个记录不可转换。

 关于集合打印宇宙的度量：

 CMonHom_PropEquiv@{u} :
 ∀ {M N : CMonObject@{u u u}}, PropEquiv@{u u} CMonHom_Setoid@{u}
 ( * u |=  * )

 -- 一个宇宙且没有约束：传输既不提高等级，也不固定它。
*)
#[export] Instance CMonHom_PropEquiv {M N : CMonObject} :
  PropEquiv (@CMonHom_Setoid M N).
Proof.
  unshelve refine
    {| pequiv := fun f g : CMonHom M N =>
                   forall a : carrier (cmon_setoid M),
                     @pequiv _ _ (cmon_prop N) (cmon_map f a) (cmon_map g a) |}.
  - intros f g H a; exact (pequiv_to _ _ (H a)).
  - intros f g H a; exact (pequiv_from _ _ (H a)).
Defined.

(*
 The identity homomorphism: the identity setoid map, which preserves the
 unit and the operation on the nose. 

 --------
 恒等同态：恒等集合商映射，严格保持单位元和运算。
*)
Program Definition cmon_hom_id {M : CMonObject} : CMonHom M M := {|
  cmon_map := setoid_morphism_id
|}.
Next Obligation.
  intros M; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros M a b; simpl.
  reflexivity.
Qed.

(*
 Composition of homomorphisms: composition of the underlying setoid maps;
 preservation of unit and operation composes. 

 --------
 同态的复合：底层集合等价映射的复合；单位和运算的保持性质也会复合。
*)
Program Definition cmon_hom_compose {M N P : CMonObject}
        (f : CMonHom N P) (g : CMonHom M N) : CMonHom M P := {|
  cmon_map := setoid_morphism_compose (cmon_map f) (cmon_map g)
|}.
Next Obligation.
  intros M N P f g; simpl.
  unfold Basics.compose.
  rewrite (cmon_map_zero g).
  apply (cmon_map_zero f).
Qed.
Next Obligation.
  intros M N P f g a b; simpl.
  unfold Basics.compose.
  rewrite (cmon_map_plus g).
  apply (cmon_map_plus f).
Qed.

Lemma cmon_hom_compose_respects {M N P : CMonObject} :
  Proper (equiv ==> equiv ==> equiv) (@cmon_hom_compose M N P).
Proof.
  intros f f' Hf g g' Hg a; simpl.
  unfold Basics.compose.
  rewrite (Hg a).
  apply Hf.
Qed.

(*
 The category of commutative monoids.

 objects: commutative monoids over setoids
 arrows: unit- and operation-preserving setoid maps
 identity: the identity setoid map
 composition: composition of setoid maps 

 --------
 交换幺半群的范畴。

 对象：集合等价类上的交换幺半群
 态射：保持单位元和运算的集合等价类映射
 恒等：恒等集合等价类映射
 复合：集合等价类映射的复合
*)
(*
 The universes are pinned by hand.  [CMonObject]'s sort is
 [Type@{max(Set+1,s,o+1,p+1)}] once [cmon_prop] is a field -- the [Set+1] is
 the sort of [Prop] and enters through [PropEquiv] -- and left to itself the
 elaborator will not identify the record's own sort variable [s] with the
 category's object universe, so [CMon] acquires a third, redundant universe
 and every `CMon@{u o}` annotation in the tree is refused for arity.  Naming
 [Category@{u p p}] and every field's instance keeps the arity at two,
 exactly as before the field landed; measured after the change,
 [CMon@{u p} : Category@{u p p}] with the single new constraint [Set < u],
 which [Unset Universe Minimization ToSet] (Lib.v) makes harmless. 

 --------
 宇宙是手动固定的。[CMonObject] 的类型是 [Type@{max(Set+1,s,o+1,p+1)}]，一旦 [cmon_prop] 是一个字段——[Set+1] 是 [Prop] 的类型并通过 [PropEquiv] 进入——如果不加干预，概念化器将不会将记录自身的类型变量 [s] 识别为该类别的对象宇宙，因此 [CMon] 会获得第三个冗余的宇宙，并且树中的每个 `CMon@{u o}` 注解都会因元数不符而被拒绝。命名 [Category@{u p p}] 以及每个字段的实例可保持元数为二，正如字段出现之前一样；在变更后测量，[CMon@{u p} : Category@{u p p}] 具有单一的新约束 [Set < u]，而 [Unset Universe Minimization ToSet]（Lib.v）使其无害。
*)
Program Definition CMon@{u p} : Category@{u p p} := {|
  obj     := CMonObject@{p p p};
  hom     := CMonHom@{p};
  homset  := @CMonHom_Setoid@{p};
  id      := @cmon_hom_id@{p};
  compose := @cmon_hom_compose@{u p};

  compose_respects := @cmon_hom_compose_respects@{u p}
|}.
Next Obligation.
  intros x y f a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y f a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y z w f g h a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y z w f g h a; simpl.
  reflexivity.
Qed.

(*
 [CMon] is therefore locally propositional: its hom-setoid IS
 [CMonHom_Setoid].  This is what lets Theory/Algebra/Rig.v's [EndRig] -- the
 endomorphism rig of an object of a preadditive category, which since the PR
 "algebraic carriers are sets" (2026-09-17) asks its ambient category for a
 [Prop] equality on homs -- be applied at [CMon] itself
 (Theory/Algebra/Rig/Connections.v). 

 --------
 因此，[CMon] 是局部命题性的：它的同态集等价关系是 [CMonHom_Setoid]。这使得 Theory/Algebra/Rig.v 中的 [EndRig] ——一个预加性范畴对象的自同态环，由于 PR“代数载体是集合”（2026-09-17）要求其所在范畴在 Hom 上有 [Prop] 的等式——能够在 [CMon] 本身上应用（Theory/Algebra/Rig/Connections.v）。
*)
#[export] Instance CMon_LocallyPropositional : LocallyPropositional CMon.
Proof.
  constructor.
  intros M N.
  exact (@CMonHom_PropEquiv M N).
Defined.

(*
 The forgetful functor to [Sets], dropping the monoid structure.  It is
 faithful by construction, since equivalence of homomorphisms in [CMon] is
 equivalence of the underlying setoid maps. 

 --------
 忘记函子到 [Sets]，舍弃单体结构。它是由构造决定的忠实函子，因为在 [CMon] 中同态的等价性就是底层集合等价映射的等价性。
*)
Program Definition CMon_Forget : CMon ⟶ Sets := {|
  fobj := fun M => cmon_setoid M;
  fmap := fun _ _ f => cmon_map f
|}.
Next Obligation.
  intros M N f g Hfg a.
  exact (Hfg a).
Qed.
Next Obligation.
  intros M a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros M N P f g a; simpl.
  reflexivity.
Qed.
