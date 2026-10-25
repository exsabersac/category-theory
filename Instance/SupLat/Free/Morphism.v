Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.Cat.
Require Import Category.Instance.SupLat.
Require Import Category.Instance.SupLat.Free.

Generalizable All Variables.

(* * * θ* between #466's two power-set monads / * * θ* 在 #466 的两个幂集单子之间 *)

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, §VI.2 Exercise 3, printed p. 142 (PDF
 p. 151) — maclane:VI.2:ex3; with Exercise 1(d) on the same page
 — maclane:VI.2:ex1
 nLab: https://ncatlab.org/nlab/show/suplattice
 nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of
 monads")

 WHAT THIS FILE DOES.  Instance/SupLat/Free.v (#466) has two power-set
 monads on Sets with the same functor data: Instance/Sets/Powerset/
 Monad.v's [Powerset_Monad], whose join is the union ⋃, and
 [SL_induced], the monad of the free complete semilattice adjunction
 [SL_adj], whose join is ⋃ ∘ P id and so agrees with ⋃ at ≈ only
 ([SL_induced_join_equiv]).  Free.v read an algebra of [SL_induced] as
 one of [Powerset_Monad] ([SL_induced_repack], proving the action law
 again) and says, under NOT DELIVERED, "No functor between the
 Eilenberg–Moore categories of [SL_induced] and of [Powerset_Monad] is
 built: the tree has no morphisms of monads, and [SL_induced_repack] is
 the object part of one."  This file builds that functor as Mac Lane's
 θ*, from Monad/Morphism.v's record and Monad/Morphism/Algebra.v's
 construction.  Free.v is not changed.

 THE MORPHISM.  [SL_theta : MonadHom Powerset_Monad SL_induced] has
 the identity of Sets as every component ([SL_theta_component],
 [eq_refl]).  Its naturality and unit law hold pointwise by
 reflexivity; its multiplication law is [SL_induced_join_equiv] after
 Instance/Sets/Powerset.v's [Powerset_Prop_map_id], which removes the
 direct image under the identity.  [SL_theta_inv] is the morphism the
 other way, again with identity components ([SL_theta_inv_component],
 [eq_refl]), its multiplication law the same two steps in the other
 order; [SL_theta_iso]: the two are inverse in Monad/Morphism.v's
 [Monads Sets], componentwise by reflexivity, so the two power-set
 monads are isomorphic objects of the category of monads.  With T =
 [Powerset_Monad] and T' = [SL_induced], θ* runs from the algebras of
 [SL_induced] to those of [Powerset_Monad], the direction of
 [SL_induced_repack].

 θ*.  [SL_EM_theta] is mh_EM SL_theta, the functor Free.v lists as not
 delivered.  On one algebra β, θ*'s structure map agrees with
 [SL_induced_repack β]'s as a function, at [eq_refl]
 ([SL_theta_alg_fun], and [SL_EM_theta_alg_fun] on objects), and the
 carrier is kept ([SL_EM_theta_carrier]).  Free.v's
 [EM_induced_to_SupLat], its functor from the algebras of
 [SL_induced] to complete semilattices, factors through θ* and
 Instance/SupLat.v's [EM_to_SupLat] (Mac Lane's Exercise 1(d) on the
 algebras of [Powerset_Monad]): [SL_factor] states EM_to_SupLat ◯
 SL_EM_theta ≈ EM_induced_to_SupLat at Cat's ≈, with identity
 components.  On objects the two agree at [eq_refl] in the carrier
 setoid ([SL_factor_set]), the order ([SL_factor_le]) and the supremum
 as a function ([SL_factor_sup_fun]), and on arrows in the underlying
 map ([SL_factor_map]).

 STRENGTHS.  By [eq_refl]: [SL_theta_component],
 [SL_theta_inv_component], [SL_theta_alg_fun], [SL_EM_theta_carrier],
 [SL_EM_theta_alg_fun] and the four [SL_factor] readbacks.  At ≈: the
 laws of [SL_theta] and [SL_theta_inv], [SL_theta_iso], and
 [SL_factor].  Refused at [eq_refl], by conversion, each pinned in
 Test/ProbeMonadMorphism468.v with its positive controls:
 - θ*'s structure map as a setoid morphism, against
 [SL_induced_repack]'s (R15; control C34); and the supremum of the
 two semilattices as a setoid morphism (R16; control C35);
 - the two semilattices, as whole objects (R17; controls C35 and
 C36).
 Controls C61, C45 and C62 restate [SL_theta_component],
 [SL_theta_inv_component] and [SL_EM_theta_carrier].
 θ* writes the structure map h as h ∘ id, a composite in Sets (Monad/
 Morphism/Algebra.v's [mh_EM_alg]), where [SL_induced_repack] keeps h,
 and [EM_to_SupLat] takes the supremum to be the structure map.  The
 first two refusals are opacity outside the tree, as for Instance/Fun/
 Action/Monad/BG/Morphism.v: Instance/Sets.v's [setoid_morphism_compose]
 and [setoid_morphism_id] carry properness proofs built from opaque
 CMorphisms lemmas, and in a copy of the probe's dependency closure in
 which only those two fields are written as terms both hold at
 [eq_refl]; with either field alone written so, both are still refused,
 and turning every [Qed] of the closure into [Defined] (Instance/
 Sets.v, Structure/Cartesian/Closed.v, Instance/Grp.v and Instance/
 Grp/Free.v keeping theirs) changes neither.  The whole-object refusal
 is not opacity, argued from the terms and not measured further (no
 copy made Instance/Sets.v transparent): it stands in all three
 copies, and in the one with
 both changes the unit law [t_id] and the action law [t_action] of the
 two algebras are each refused alone, [SL_induced_repack] keeping
 β's unit law and proving its action law again, θ* rebuilding both
 through [mh_ret] and [mh_join].
 CORRECTION (#1347): the copy in which only those two fields are
 written as terms is now the tree: the first two refusals, R15 and R16,
 hold at [eq_refl] and are controls of the probe, and their attribution
 to the standard library's opacity was right; the whole-object refusal,
 R17, still stands.

 UNIVERSES, read off [About].  Every constant binds [@{o so}] with
 Set < o and o < so, except [SL_theta_iso], which adds the object and
 hom levels m1 and m2 of [Monads@{so o m1 m2} Sets], at or above so,
 and the caps of the sigma objects of [Monads], and [SL_factor], which
 adds c with o < c and so < c, the levels of [Cat@{c so so so o}],
 first carried by Instance/Cat.v's [Cat].  [SL_theta], [SL_theta_inv],
 their component readbacks and [SL_theta_alg_fun] have exactly the
 block of [SL_induced]: Set < o, first carried by
 Instance/Sets/Powerset.v's [Powerset_Prop_truth_equiv], the relation
 on Prop (Prop : Type@{Set+1}), as Instance/SupLat.v and
 Instance/Sets/Powerset/Monad.v attribute it; o < so, first carried by
 Instance/Sets.v's [Sets]; and the stdlib caps that Free.v's UNIVERSES
 paragraph attributes.  [SL_EM_theta] and the constants that name it
 have exactly the block of [EM_induced_to_SupLat], which adds o <=
 Projections.u1 and so <= Projections.u0 from [EilenbergMoore]'s sigma
 objects.  No equation occurs.

 NOT DELIVERED.  Free.v is not rewired: its [SL_induced_repack] and
 [EM_induced_to_SupLat] keep their own structure maps, which θ* would
 replace by h ∘ id.  The isomorphism in Cat between the two
 Eilenberg–Moore categories that Monad/Morphism/Algebra.v's
 [Monads_EM] makes of [SL_theta_iso] is not stated. 

 --------
 书籍：Mac Lane，《为在职数学家准备的范畴论》，第2版，Springer GTM 5，1998年，第VI.2节 练习3，印刷版第142页（PDF第151页）—— maclane:VI.2:ex3；同页练习1(d) —— maclane:VI.2:ex1
 nLab: https://ncatlab.org/nlab/show/suplattice
 nLab: https://ncatlab.org/nlab/show/monad（章节“单子（monads）的2-范畴”）这个文件的功能。Instance/SupLat/Free.v (#466) 在集合上有两个幂集单子，它们具有相同的函子数据：Instance/Sets/Powerset/Monad.v 的 [Powerset_Monad]，其联结为并集 ⋃，以及 [SL_induced]，自由完备半格伴随的单子 [SL_adj]，其联结为 ⋃ ∘ P id，因此在 ≈ 上仅与 ⋃ 一致 ([SL_induced_join_equiv])。Free.v 将 [SL_induced] 的代数读取为 [Powerset_Monad] ([SL_induced_repack]，再次证明作用律) 并且在 NOT DELIVERED 下表示，“在 [SL_induced] 和 [Powerset_Monad] 的 Eilenberg–Moore 范畴之间没有建立函子：树中没有单子态射，而 [SL_induced_repack] 是其中一个的对象部分。” 该文件将该函子建立为 Mac Lane 的 θ*，来源于 Monad/Morphism.v 的记录和 Monad/Morphism/Algebra.v 的构造。Free.v 没有修改。态射。[SL_theta : MonadHom Powerset_Monad SL_induced] 具有集合的恒等作为每个分量（[SL_theta_component]，[eq_refl]）。其自然性和单位律通过自反性逐点成立；其乘法律是 [SL_induced_join_equiv] ，在 Instance/Sets/Powerset.v 的 [Powerset_Prop_map_id] 之后，该操作移除了恒等下的直接像。[SL_theta_inv] 是反向的态射，同样具有恒等分量（[SL_theta_inv_component]，[eq_refl]），其乘法律为相同的两步但顺序相反；[SL_theta_iso] ：这两者在 Monad/Morphism.v 的 [Monads Sets] 中互为逆元，分量上通过自反性，因此两个幂集单子是单子范畴中的同构对象。取 T = [Powerset_Monad] 和 T' = [SL_induced]，θ* 从 [SL_induced] 的代数到 [Powerset_Monad] 的代数运行，其方向为 [SL_induced_repack]。θ*。[SL_EM_theta] 是 mh_EM SL_theta，函子 Free.v 列为未提供。在一个代数 β 上，θ* 的结构映射作为函数与 [SL_induced_repack β] 一致，在 [eq_refl]（[SL_theta_alg_fun] 和 [SL_EM_theta_alg_fun] 在对象上），并且保持承载 ([SL_EM_theta_carrier])。Free.v 的 [EM_induced_to_SupLat]，其从 [SL_induced] 的代数到完备半格的函子，通过 θ* 和 Instance/SupLat.v 的 [EM_to_SupLat] 因式分解（Mac Lane 关于 [Powerset_Monad] 的代数的练习 1(d)）：[SL_factor] 表示 EM_to_SupLat ◯ SL_EM_theta ≈ EM_induced_to_SupLat 在 Cat 的 ≈ 上，具有恒等组件。在对象上，这两者在承载集类 ([SL_factor_set])、序 ([SL_factor_le]) 和作为函数的上确界 ([SL_factor_sup_fun]) 在 [eq_refl] 上一致，并且在底层映射的箭头上 ([SL_factor_map]) 也一致。优势。作者：[eq_refl]：[SL_theta_component]，[SL_theta_inv_component]，[SL_theta_alg_fun]，[SL_EM_theta_carrier]，[SL_EM_theta_alg_fun] 以及四个 [SL_factor] 回读。在 ≈ 时：[SL_theta] 和 [SL_theta_inv]、[SL_theta_iso] 以及 [SL_factor] 的定律。在 [eq_refl] 被拒绝，通过转换，每个都在 Test/ProbeMonadMorphism468.v 中固定其阳性对照：
 - θ* 的结构映射作为集合等价态态射，与 [SL_induced_repack] 的（R15；对照 C34）相对；以及两个半格的上确界作为集合等价态态射（R16；对照 C35）；
 - 两个半格，作为整体对象（R17；对照 C35 和 C36）。C61，C45 和 C62 对 [SL_theta_component]，[SL_theta_inv_component] 和 [SL_EM_theta_carrier] 进行了重述。θ* 将结构映射 h 写作 h ∘ id，在 Sets（Monad/Morphism/Algebra.v 的 [mh_EM_alg]）中为复合，其中 [SL_induced_repack] 保持 h，而 [EM_to_SupLat] 将上确界作为结构映射。前两个拒绝是树外的不透明性，对于 Instance/Fun/Action/Monad/BG/Morphism.v: Instance/Sets.v 的 [setoid_morphism_compose] 和 [setoid_morphism_id] 携带由不透明 CMorphisms 引理构建的适当性证明，并且在探针依赖闭包的副本中，其中只有这两个字段被作为项写入时，它们在 [eq_refl] 处仍然成立；即使只写入其中一个字段，仍然会被拒绝，并且将闭包中的每个 [Qed] 变为 [Defined]（Instance/Sets.v、Structure/Cartesian/Closed.v、Instance/Grp.v 和 Instance/Grp/Free.v 保留它们各自的）也没有改变。整体对象拒绝并不是不透明的，这是从术语上提出的，而没有进一步测量（没有复制 Instance/Sets.v 为透明）：它在所有三个副本中都存在，并且在同时进行了两项更改的副本中，两个代数的单位律 [t_id] 和作用律 [t_action] 都被单独拒绝，[SL_induced_repack] 保留了 β 的单位律并再次证明其作用律，θ* 通过 [mh_ret] 和 [mh_join] 重建两者。更正（#1347）：现在仅将那两个字段写为术语的副本是树：前两个拒绝，R15 和 R16，在 [eq_refl] 上成立，并且是探针的控制，它们归因于标准库的不透明性是正确的；整体对象拒绝，R17，仍然有效。UNIVERSES，读出 [About]。每个常量将 [@{o so}] 与 Set < o 和 o < so 绑定，除了 [SL_theta_iso]，它添加了 [Monads@{so o m1 m2} Sets] 的对象和同态层 m1 和 m2，位于或高于 so，以及 [Monads] 的 sigma 对象的上界，以及 [SL_factor]，它添加了 c，使 o < c 并且 so < c，ZW79WZZ 的层，由 Instance/Cat.v 的 [Cat] 首次承载。ZW81WZZ，ZW82WZZ，它们的组件回读和 [SL_theta_alg_fun] 恰好具有 [SL_induced] 的区块：Set < o，由 Instance/Sets/Powerset.v 的 [Powerset_Prop_truth_equiv] 首次承载，对 Prop (Prop : Type@{Set+1}) 的关系，如 Instance/SupLat.v 和 Instance/Sets/Powerset/Monad.v 所标注；o < so，由 Instance/Sets.v 的 [Sets] 首次承载；以及 stdlib 上界，由 Free.v 的 UNIVERSES 段落标注。[SL_EM_theta] 及命名它的常数
 拥有与 [EM_induced_to_SupLat] 完全相同的块，后者添加了 o <=
 Projections.u1 并且所以 <= Projections.u0 来自 [EilenbergMoore] 的 sigma
 对象。没有方程出现。

 未交付。Free.v 未重新接线：它的 [SL_induced_repack] 和
 [EM_induced_to_SupLat] 保持各自的结构映射，而 θ* 会
 被 h ∘ id 替换。在范畴论中，Monad/Morphism/Algebra.v 的
 [Monads_EM] 对 [SL_theta_iso] 所做的两个 Eilenberg–Moore 范畴之间的同构
 并未说明。
*)

(* * ** θ : Powerset_Monad ⟶ SL_induced, identity components / * ** θ ：Powerset_Monad ⟶ SL_induced，恒等分量 *)

Definition SL_theta@{o so | Set < o, o < so +} :
  MonadHom@{so o} Powerset_Monad@{o so} SL_induced@{o so}.
Proof.
  unshelve refine
    (@Build_MonadHom Sets@{o so} Powerset_Prop@{o so}
       (SL_Forget@{o so} ◯ SL_Free@{o so})
       Powerset_Monad@{o so} SL_induced@{o so}
       (Build_Transform'@{so o o so o o}
          (F:=Powerset_Prop@{o so}) (G:=SL_Forget@{o so} ◯ SL_Free@{o so})
          (fun X => @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X)) _) _ _).
  - intros X Y f S. reflexivity.
  - intros X x. reflexivity.
  - intros X SS.
    symmetry.
    etransitivity;
      [ exact (SL_induced_join_equiv X (fmap[Powerset_Prop@{o so}] id SS)) | ].
    apply (proper_morphism (@join _ _ Powerset_Monad@{o so} X)).
    exact (@Powerset_Prop_map_id@{o} (Powerset_Prop_obj@{o} X) SS).
Defined.

Example SL_theta_component@{o so | Set < o, o < so +} (X : SetoidObject@{o o}) :
  mh_transform SL_theta@{o so} X
    = @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X) := eq_refl.

(* θ* on one algebra against [SL_induced_repack], as a function. / θ* 在一个代数上针对 [SL_induced_repack]，作为一个函数。 *)

Example SL_theta_alg_fun@{o so | Set < o, o < so +} {X : SetoidObject@{o o}}
  (β : @TAlgebra Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so})
         SL_induced@{o so} X) :
  (fun S => @t_alg _ _ _ _ (mh_algebra SL_theta@{o so} β) S)
    = (fun S => @t_alg _ _ _ _ (SL_induced_repack@{o so} β) S) := eq_refl.

(* * ** θ⁻¹ : SL_induced ⟶ Powerset_Monad, identity components / * ** θ⁻¹ : SL_induced ⟶ 幂集单子，恒等分量 *)

Definition SL_theta_inv@{o so | Set < o, o < so +} :
  MonadHom@{so o} SL_induced@{o so} Powerset_Monad@{o so}.
Proof.
  unshelve refine
    (@Build_MonadHom Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so})
       Powerset_Prop@{o so}
       SL_induced@{o so} Powerset_Monad@{o so}
       (Build_Transform'@{so o o so o o}
          (F:=SL_Forget@{o so} ◯ SL_Free@{o so}) (G:=Powerset_Prop@{o so})
          (fun X => @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X)) _) _ _).
  - intros X Y f S. reflexivity.
  - intros X x. reflexivity.
  - intros X SS.
    etransitivity; [ exact (SL_induced_join_equiv X SS) | ].
    apply (proper_morphism (@join _ _ Powerset_Monad@{o so} X)).
    symmetry.
    exact (@Powerset_Prop_map_id@{o} (Powerset_Prop_obj@{o} X) SS).
Defined.

Example SL_theta_inv_component@{o so | Set < o, o < so +}
  (X : SetoidObject@{o o}) :
  mh_transform SL_theta_inv@{o so} X
    = @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X) := eq_refl.

(* The two are inverse in [Monads Sets]. / 这两者在 [Monads Sets] 中是相反的。 *)

Definition SL_theta_iso@{o so m1 m2 |
  Set < o, o < so, o <= m1, o <= m2, so <= m1, so <= m2 +} :
  @Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (Powerset_Prop@{o so}; Powerset_Monad@{o so})
    (SL_Forget@{o so} ◯ SL_Free@{o so}; SL_induced@{o so}).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (Powerset_Prop@{o so}; Powerset_Monad@{o so})
    (SL_Forget@{o so} ◯ SL_Free@{o so}; SL_induced@{o so})
    SL_theta@{o so} SL_theta_inv@{o so} _ _).
  - intros X S. reflexivity.
  - intros X S. reflexivity.
Defined.

(* * ** θ* : the functor Free.v lists as NOT DELIVERED / * ** θ* ：函子 Free.v 列为未交付 *)

Definition SL_EM_theta@{o so | Set < o, o < so +} :
  @EilenbergMoore@{so so so o} Sets@{o so}
    (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}
  ⟶ @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
      Powerset_Monad@{o so} :=
  mh_EM@{so o so so} SL_theta@{o so}.

Example SL_EM_theta_carrier@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  `1 (fobj[SL_EM_theta@{o so}] x) = `1 x := eq_refl.

Example SL_EM_theta_alg_fun@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  (fun S => @t_alg _ _ _ _ (`2 (fobj[SL_EM_theta@{o so}] x)) S)
    = (fun S => @t_alg _ _ _ _ (SL_induced_repack@{o so} (`2 x)) S)
  := eq_refl.

(** ** [EM_induced_to_SupLat] factors through θ* / ** [EM_induced_to_SupLat] 通过 θ 因子分解* *)

Example SL_factor_set@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  sl_set (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
    = sl_set (fobj[EM_induced_to_SupLat@{o so}] x) := eq_refl.

Example SL_factor_le@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  sl_le (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
    = sl_le (fobj[EM_induced_to_SupLat@{o so}] x) := eq_refl.

Example SL_factor_sup_fun@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  (fun S => sl_sup (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x) S)
    = (fun S => sl_sup (fobj[EM_induced_to_SupLat@{o so}] x) S) := eq_refl.

Example SL_factor_map@{o so | Set < o, o < so +}
  (x y : @EilenbergMoore@{so so so o} Sets@{o so}
           (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
  (f : x ~> y) :
  slh_map (fmap[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] f)
    = slh_map (fmap[EM_induced_to_SupLat@{o so}] f) := eq_refl.

Definition SL_factor@{o so c | Set < o, o < so, o < c, so < c +} :
  @equiv _
    (@homset Cat@{c so so so o}
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
       SupLat@{o so})
    (EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}) EM_induced_to_SupLat@{o so}.
Proof.
  unshelve eexists.
  - intros x.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + unshelve refine
        (@Build_SupLatHom@{o}
           (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
           (fobj[EM_induced_to_SupLat@{o so}] x) (@id Sets@{o so} _) _).
      intros S.
      apply (proper_morphism (@t_alg _ _ _ _ (projT2 x))).
      symmetry. exact (@Powerset_Prop_map_id@{o} _ S).
    + unshelve refine
        (@Build_SupLatHom@{o}
           (fobj[EM_induced_to_SupLat@{o so}] x)
           (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
           (@id Sets@{o so} _) _).
      intros S.
      apply (proper_morphism (@t_alg _ _ _ _ (projT2 x))).
      symmetry. exact (@Powerset_Prop_map_id@{o} _ S).
    + intros z. reflexivity.
    + intros z. reflexivity.
  - intros x y f z. reflexivity.
Defined.
