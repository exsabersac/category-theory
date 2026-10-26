Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.
Require Import Category.Functor.Product.Internal.
Require Import Category.Functor.Diagonal.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Product.

Set Universe Polymorphism.

Generalizable All Variables.

(** * A worked example of the General Adjoint Functor Theorem  / * 一般伴随定理的一个例子*)

(*
This file exercises [GAFT_from_initials] (Adjunction/GAFT.v) end to end on a
   concrete, non-degenerate adjunction: the binary diagonal / product adjunction

       Δ ⊣ (×)

   on any cartesian category [C].  Feeding a genuine comma-category initial
   object to the universal-arrow half of GAFT reproduces this known adjunction,
   validating that the GAFT plumbing composes with the universal-arrow bridge of
   [Theory/Universal/Arrow.v].

   VARIANCE (donor-signature deviation, recorded honestly).  [GAFT_from_initials]
   consumes [forall d, @Initial (=(d) ↓ U)] for a functor [U : C ⟶ D] and yields
   a *left* adjoint [F ⊣ U].  For the diagonal / product pair, [Δ] is the *left*
   adjoint and [(×)] the *right* adjoint (the general triangle is
   [(+) ⊣ Δ ⊣ (×)]).  So the functor that must play the role of [U] — the one
   fed to GAFT — is the product bifunctor

       ×(C) : C ∏ C ⟶ C   (Functor/Product/Internal.v, [InternalProductFunctor]),

   and the produced left adjoint [F : C ⟶ C ∏ C] is the diagonal.  The initial
   object of the comma [=(d) ↓ ×(C)] is [((d, d), δ)] with the diagonal
   [δ := id △ id : d ~> d × d] as its universal arrow (this is the classical
   “a product is a universal arrow out of the diagonal”, read for the binary
   diagonal).  Taking [U := ×(C)] rather than the literal symbol [Δ] is forced by
   the *direction* GAFT produces; feeding [Δ] itself to GAFT would instead
   reconstruct the coproduct adjunction [(+) ⊣ Δ], a different, equally genuine
   left adjoint; that adjunction is now in the tree, supplied directly rather
   than through GAFT, as Adjunction/Diagonal/Coproduct.v's
   [Diagonal_Coproduct_Adjunction], with sanity instantiations at [Coq] and
   [Sets] at the end of that file -- reconstructing it through GAFT is not
   undertaken in this file.  The conclusion delivered here is the full, honest
   adjunction
   [F ⊣ ×(C)] with no hypothesis weakened; the produced [F] is opaque (GAFT ends
   in [Qed]) and only *provably* the diagonal, so this file also exhibits, as
   [diagonal_product_via_gaft_is_diagonal], the natural isomorphism [F ≅ Δ] that
   makes it genuinely [Δ ⊣ (×)] (uniqueness of left adjoints, [left_adjoint_iso]). 

--------
该文件在 a 上端到端地练习 [GAFT_from_initials] (Adjunction/GAFT.v)
 具体的、非简并附加：二元对角线/乘积附加

Δ ⊣ (×)

在任何笛卡尔类别 [C] 上。 提供真正的逗号类别首字母
 对 GAFT 通用箭头一半的反对再现了这个已知的附加，
 验证 GAFT 管道与通用箭头桥组成
 [Theory/Universal/Arrow.v]。

方差（捐赠者签名偏差，如实记录）。 保护3X
 为函子 [U : C ⟶ D] 消耗 [forall d, @Initial (=(d) ↓ U)] 并产生
 *左*伴随 [F ⊣ U]。 对于对角线/乘积对，[Δ] 是*左*
 伴随和 [(×)] *右*伴随（一般三角形是
 [(+) ⊣ Δ ⊣ (×)]）。 因此，必须扮演 [U] 角色的函子 - 函子
 馈送到 GAFT — 是乘积双函子

×(C) : C ∏ C ⟶ C （函子/产品/内部.v，[InternalProductFunctor]），

生成的左伴随 [F : C ⟶ C ∏ C] 是对角线。 最初的
 逗号 [=(d) ↓ ×(C)] 的对象是带有对角线的 [((d, d), δ)]
 [δ := id △ id : d ~> d × d] 作为其通用箭头（这是经典的
 “产品是对角线外的通用箭头”，阅读二进制
 对角线）。 采用 [U := ×(C)] 而不是文字符号 [Δ] 是由于
 GAFT 产生的*方向*； 将 [Δ] 本身输入 GAFT 会
 重建副产品附件 [(+) ⊣ Δ]，一个不同的，同样真实的
 左伴随； 该附加项现在位于树中，直接提供而不是
 而不是通过 GAFT，如 Adjunction/Diagonal/Coproduct.v 的
 [Diagonal_Coproduct_Adjunction]，在 [Coq] 上具有健全的实例化和
 [Sets] 在该文件的末尾 - 通过 GAFT 重建它不是
 在此文件中进行。
这里得出的结论是完整、诚实的
 附属物
 [F ⊣ ×(C)] 无假设减弱； 生产的 [F] 是不透明的（GAFT 端
 在 [Qed] 中）并且仅“可证明”对角线，因此该文件也显示为
 [diagonal_product_via_gaft_is_diagonal]，自然同构 [F ≅ Δ]
 使其成为真正的 [Δ ⊣ (×)]（左伴随的唯一性，[left_adjoint_iso]）。 
*)

Section GAFTExample.

Context `{C : Category}.
Context `{@Cartesian C}.

(*
The universal mapping property of the diagonal, in the exact shape consumed
   by [universal_arrow_from_UMP]: for [d : C] the object [(d, d) : C ∏ C]
   together with the diagonal [id △ id : d ~> d × d] is a universal arrow from
   [d] to the product bifunctor [×(C)].  Any [f : d ~> a × b] factors uniquely
   through the diagonal, the factorization being the pair of projections
   [(exl ∘ f, exr ∘ f)] read as a morphism [(d, d) ~> (a, b)] of [C ∏ C]. 

--------
对角线的通用映射属性，以所消耗的确切形状
 通过 [universal_arrow_from_UMP]：对于 [d : C] 对象 [(d, d) : C ∏ C]
 与对角 [id △ id : d ~> d × d] 一起是一个通用箭头
 [d] 到乘积双函子 [×(C)]。 任何 [f : d ~> a × b] 因素都有独特之处
 通过对角线，分解是一对投影
 [(exl ∘ f, exr ∘ f)] 读作 [C ∏ C] 的态射 [(d, d) ~> (a, b)]。 
*)
#[local] Obligation Tactic := idtac.

Program Definition diagonal_unique (d : C) (d' : C ∏ C)
  (f : d ~> InternalProductFunctor C d') :
  ∃! g : (d, d) ~{ C ∏ C }~> d',
    f ≈ fmap[InternalProductFunctor C] g ∘ (id[d] △ id[d]) :=
  {| unique_obj := (exl ∘ f, exr ∘ f) |}.
Next Obligation.
  (* existence: the projection pair factors [f] through the diagonal  / 存在性：投影对通过对角线因式分解 [f]*)
  intros d d' f; simpl.
  assert (PFf : f ≈ (exl ∘ f) △ (exr ∘ f))
    by (apply ump_products; split; reflexivity).
  rewrite PFf at 1.
  symmetry.
  apply ump_products; split.
  - rewrite exl_fork_comp, <- comp_assoc, exl_fork, id_right; reflexivity.
  - rewrite exr_fork_comp, <- comp_assoc, exr_fork, id_right; reflexivity.
Qed.
Next Obligation.
  (* uniqueness: any factorizer [(v1, v2)] agrees with the projection pair  / 唯一性：任何因子分解器 [(v1, v2)] 都与投影对一致*)
  intros d d' f [v1 v2] Hv.
  simpl in Hv.
  assert (Hf : f ≈ (v1 △ v2)).
  { rewrite Hv.
    apply ump_products; split.
    - rewrite exl_fork_comp, <- comp_assoc, exl_fork, id_right; reflexivity.
    - rewrite exr_fork_comp, <- comp_assoc, exr_fork, id_right; reflexivity. }
  simpl; split.
  - rewrite Hf, exl_fork; reflexivity.
  - rewrite Hf, exr_fork; reflexivity.
Qed.

(*
Packaged as a [UniversalArrow], whose [arrow_initial] projection is exactly
   the comma-category initial object [GAFT_from_initials] wants. 

--------
封装为 [UniversalArrow]，其 [arrow_initial] 投影正好是
 [GAFT_from_initials] 想要的逗号类别初始对象。 
*)
Definition diagonal_UA (d : C) : UniversalArrow d (InternalProductFunctor C) :=
  universal_arrow_from_UMP d (InternalProductFunctor C) (d, d)
    (id[d] △ id[d]) (diagonal_unique d).

(*
The example: run [GAFT_from_initials] on the product bifunctor, supplying at
   each [d] the initial object of [=(d) ↓ ×(C)] produced above.  The result is a
   genuine left adjoint [F ⊣ ×(C)], produced purely through the GAFT machinery.
   Because [GAFT_from_initials] is [Qed]-opaque, this [F] is not *definitionally*
   the diagonal [Δ]; it is a left adjoint to [×(C)], necessarily isomorphic to
   [Δ] by uniqueness of left adjoints.  That isomorphism is exhibited just below,
   in [diagonal_product_via_gaft_is_diagonal]. 

--------
示例：在产品双函子上运行 [GAFT_from_initials]，提供
 每个 [d] 都是上面生成的 [=(d) ↓ ×(C)] 的初始对象。 结果是
 正品左伴 [F ⊣ ×(C)]，完全通过 GAFT 机械生产。 
因为 [GAFT_from_initials] 是 [Qed] 不透明的，所以 [F] *绝对不是*
 对角 [Δ]； 它是 [×(C)] 的左伴随，必然同构于
 [Δ] 通过左伴随的唯一性。 下面展示了同构，
 在 [diagonal_product_via_gaft_is_diagonal] 中。 
*)
Definition diagonal_product_via_gaft :
  { F : C ⟶ C ∏ C & F ⊣ InternalProductFunctor C } :=
  GAFT_from_initials (InternalProductFunctor C)
    (fun d => arrow_initial (UniversalArrow := diagonal_UA d)).

(*
The GAFT-produced left adjoint is naturally isomorphic to the concrete binary
   diagonal [Diagonal_Product C].  Left adjoints to a fixed functor are unique up
   to natural isomorphism ([Theory/Adjunction.v], [left_adjoint_iso]); pitting the
   opaque GAFT adjunction [projT2 diagonal_product_via_gaft] against the concrete
   diagonal–product adjunction [Diagonal_Product_Adjunction] over their common
   right adjoint [×(C)] delivers that isomorphism.  So the [F] above, though
   opaque, is provably (naturally isomorphic to) the diagonal — the
   reconstruction of [Δ ⊣ (×)] is genuine, not merely asserted. 

--------
GAFT 生成的左伴随自然与具体的二进制同构
 对角 [Diagonal_Product C]。 固定函子的左伴随物是唯一的
 自然同构（[Theory/Adjunction.v]、[left_adjoint_iso]）； 坑的
 不透明 GAFT 附加物 [projT2 diagonal_product_via_gaft] 针对混凝土
 对角-乘积附加 [Diagonal_Product_Adjunction] 优于其常见的
 右伴随 [×(C)] 提供了这种同构。 所以上面的 [F] 不过
 不透明，可证明（自然同构）对角线 -
 [Δ ⊣ (×)] 的重建是真实的，而不仅仅是断言。 
*)
Definition diagonal_product_via_gaft_is_diagonal :
  projT1 diagonal_product_via_gaft ≈ Diagonal_Product C :=
  left_adjoint_iso (InternalProductFunctor C)
    (projT1 diagonal_product_via_gaft) (Diagonal_Product C)
    (projT2 diagonal_product_via_gaft)
    (Diagonal_Product_Adjunction C).

End GAFTExample.
