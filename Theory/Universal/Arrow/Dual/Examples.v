Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Product.Internal.
Require Import Category.Functor.Diagonal.
Require Import Category.Adjunction.Diagonal.Product.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Set Universe Polymorphism.

Generalizable All Variables.

(*
[=( c )] lives in functor_scope (Functor/Diagonal.v); this file does not
   import any module that opens it as a side effect, so it is opened here.

--------
[=( c )] 位于 functor_scope (Functor/Diagonal.v)；该文件没有导入任何会作为副作用打开它的模块，所以它在这里被打开。
*)
Open Scope functor_scope.

(** * A worked example of the couniversal-arrow assembly / * 一个关于共用箭头组件的工作示例 *)

(*
This file is the mirror image of Adjunction/GAFT/Examples.v, and is meant to
   be read beside it.  There, a family of UNIVERSAL arrows into the product
   bifunctor ×(C) reconstructs the binary diagonal as a LEFT adjoint,

       diagonal_UA d : UniversalArrow d (×(C))     ⟹     F ⊣ ×(C),  F ≅ Δ.

   Here, a family of COUNIVERSAL arrows out of the binary diagonal
   Δ = Diagonal_Product C reconstructs the product bifunctor as a RIGHT
   adjoint,

       product_CUA p : CouniversalArrow p Δ        ⟹     Δ ⊣ R,   R ≅ ×(C).

   The same classical adjunction Δ ⊣ ×, approached from the two opposite
   sides -- which is the point of the exercise: it demonstrates
   [AdjunctionFromCouniversalArrows] end to end on a non-degenerate example
   rather than merely typechecking it.

   The example is the classical one, and Functor/Diagonal.v already quotes it
   verbatim (from Wikipedia, "Diagonal functor"): "a product a × b is a
   universal arrow from Δ to ⟨a, b⟩.  The arrow comprises the projection
   maps."  An arrow FROM a functor TO an object is Mac Lane's couniversal one,
   so that sentence is exactly [product_CUA] below.  The couniversal morphism
   is the PROJECTION PAIR (exl, exr), and the mediating factorization is
   [fork], so the entire universal-property content of
   [product_couniversal_unique] is [ump_products] (Structure/Cartesian.v) with
   nothing added.

   ONE STRENGTH DIFFERENCE FROM THE PRIMAL EXAMPLE, worth recording because it
   runs the other way.  [GAFT_from_initials] ends in [Qed], so the left adjoint
   the primal file produces is opaque and only PROVABLY the diagonal; that file
   must exhibit a natural isomorphism to say so.  The assembly here is
   transparent all the way down, so the object action of the produced right
   adjoint reduces to the product on the nose --
   [product_via_couniversal_obj] closes by [eq_refl].  The natural isomorphism
   to ×(C) is still supplied ([product_via_couniversal_is_product]), because
   the ARROW action is a chosen unique factorization and there is no reason for
   it to reduce to ×(C)'s [fmap]; but the object half needs no argument at all.

   The concrete instantiation at [Sets] closes the file, so the family is
   inhabited by something other than a variable.

--------
此文件是 Adjunction/GAFT/Examples.v 的镜像，并且旨在与其一起阅读。在那里，进入乘积双函子 ×(C) 的一族 UNIVERSAL 箭头重新构造了二元对角作为左伴随。

diagonal_UA d : UniversalArrow d (×(C))     ⟹     F ⊣ ×(C),  F ≅ Δ.

在这里，一族 COUNIVERSAL 箭头从二元对角线 Δ = 对角线乘积 C 指出，将乘积双函子重构为右伴随。

product_CUA p : CouniversalArrow p Δ        ⟹     Δ ⊣ R,   R ≅ ×(C).

同一个经典的伴随 Δ ⊣ ×，从两个相反的方向来处理——这正是练习的重点：它展示了 [AdjunctionFromCouniversalArrows] 在非退化示例上的端到端，而不仅仅是类型检查它。

这个例子是经典的例子，而 Functor/Diagonal.v 已经逐字引用了它（来自维基百科，“对角函子”）：“一个积 a × b 是从 Δ 到 ⟨a, b⟩ 的一个通用箭头。这个箭头包括投影映射。” 从一个函子到一个对象的箭头是 Mac Lane 的共通用箭头，因此那句话正好是下面的 [product_CUA]。共通用态射是投影对 (exl, exr)，中介分解是 [fork]，因此 [product_couniversal_unique] 的整个通用性质内容就是 [ump_products]（Structure/Cartesian.v），没有添加任何内容。

与原始示例相比只有一个强度差异，值得记录，因为它运行的方向相反。[GAFT_from_initials] 以 [Qed] 结束，所以原始文件生成的左伴随是不可见的，并且只能被证明是对角线；该文件必须显示自然同构才能说明这一点。这里的组合从头到尾是透明的，因此生成的右伴随的对象作用直接归约为直积——[product_via_couniversal_obj] 以 [eq_refl] 结束。到 ×(C) 的自然同构仍然提供（[product_via_couniversal_is_product]），因为 ARROW 作用是一个选定的唯一因式分解，并且没有理由将其归约为 ×(C) 的 [fmap]；但对象部分完全不需要任何论证。

在 [Sets] 的具体实例化会关闭文件，因此该族由变量以外的东西组成。
*)

Section CouniversalExample.

Context `{C : Category}.
Context `{@Cartesian C}.

(*
The projection pair, typed as a morphism of C ∏ C out of the diagonal.
   The ascription is load-bearing: as a bare pair the elaborator cannot see
   which category's composition the couniversal equation is asking for.

--------
投影对，类型为从对角线出的 C ∏ C 的态射。  
这个指定是关键的：作为一个裸对，展开器无法看到  
反通用方程要求的是哪一个范畴的复合。
*)
Definition proj_pair (p : C ∏ C) :
  Diagonal_Product C (fst p × snd p) ~{C ∏ C}~> p :=
  (@exl C _ (fst p) (snd p), @exr C _ (fst p) (snd p)).

(*
The couniversal mapping property of the projection pair, in the exact shape
   consumed by [couniversal_arrow_from_UMP]: for p : C ∏ C the object
   fst p × snd p together with (exl, exr) : Δ (fst p × snd p) ~> p is a
   couniversal arrow from Δ to p.  Any f : Δ d' ~> p -- that is, any pair of
   morphisms (f₁ : d' ~> fst p, f₂ : d' ~> snd p) -- factors uniquely through
   the projections, the factorization being the fork f₁ △ f₂.

--------
投影对的余泛映射性质，在 [couniversal_arrow_from_UMP] 使用的精确形式下：对于 p : C ∏ C，对象 fst p × snd p 连同 (exl, exr) : Δ (fst p × snd p) ~> p 是从 Δ 到 p 的余通箭。任何 f : Δ d' ~> p —— 即任何一对态射 (f₁ : d' ~> fst p, f₂ : d' ~> snd p) —— 都可以唯一地通过投影分解，这种分解就是叉 f₁ △ f₂。
*)
#[local] Obligation Tactic := idtac.

Program Definition product_couniversal_unique (p : C ∏ C) (d' : C)
  (f : Diagonal_Product C d' ~{C ∏ C}~> p) :
  ∃! g : d' ~{C}~> (fst p × snd p),
    f ≈ proj_pair p ∘ fmap[Diagonal_Product C] g :=
  {| unique_obj := fst f △ snd f |}.
Next Obligation.
  (* existence: the fork factors both components through the projections / 存在性：分叉通过投影将两个分量相互联系 *)
  intros p d' f; simpl; split.
  - now rewrite exl_fork.
  - now rewrite exr_fork.
Qed.
Next Obligation.
  (* uniqueness: any factorizer agrees with the fork, by [ump_products] / 唯一性：任何分解器都与分叉一致，由 [ump_products] 提供 *)
  intros p d' f v [Hv1 Hv2]; simpl in *.
  symmetry.
  apply ump_products; split.
  - now symmetry.
  - now symmetry.
Qed.

(*
Packaged as a [CouniversalArrow]: Mac Lane's "a product is a couniversal
   arrow from the diagonal".

--------
作为 [CouniversalArrow] 打包：Mac Lane 的“一个积是从对角线的一个通用箭头”.
*)
Definition product_CUA (p : C ∏ C) :
  CouniversalArrow p (Diagonal_Product C) :=
  couniversal_arrow_from_UMP p (Diagonal_Product C) (fst p × snd p)
    (proj_pair p)
    (product_couniversal_unique p).

(*
The couniversal object is the product, and the couniversal arrow is the
   projection pair -- both by convertibility, since
   [couniversal_arrow_from_UMP] is [Defined].

--------
余宇对象是积对象，余宇箭头是投影对——两者都通过可互换性，因为 [couniversal_arrow_from_UMP] 是 [Defined]。
*)
Corollary product_CUA_obj (p : C ∏ C) :
  coarrow_obj (product_CUA p) = (fst p × snd p).
Proof. reflexivity. Qed.

Corollary product_CUA_arrow (p : C ∏ C) :
  coarrow (product_CUA p) = proj_pair p.
Proof. reflexivity. Qed.

(** ** The terminal-object reading, exercised / ** 终端对象读取，已执行 *)

(*
[couniversal_arrow_terminal] applied to a real couniversal arrow: the
   product, with its projections, is a TERMINAL object of the comma category
   Δ ↓ =(p) -- Mac Lane's §III.1 Definition 3 read at his own example.

--------
[couniversal_arrow_terminal] 应用于一个真实的通用箭头：积及其投射是逗号范畴 Δ ↓ =(p) 的终端对象 —— 根据 Mac Lane §III.1 定义 3，并结合他自己的例子阅读。
*)
Definition product_terminal (p : C ∏ C) :
  @Terminal (Diagonal_Product C ↓ =(p)) :=
  couniversal_arrow_terminal (product_CUA p).

Corollary product_terminal_obj (p : C ∏ C) :
  `1 (@terminal_obj _ (product_terminal p)) = (fst p × snd p, ttt).
Proof. reflexivity. Qed.

(* ... and the passage back keeps both the object and the arrow. / ... 回程既保留物体也保留箭头。 *)
Corollary product_terminal_round (p : C ∏ C) :
  coarrow (couniversal_arrow_of_terminal (product_terminal p))
    = coarrow (product_CUA p).
Proof. reflexivity. Qed.

(** ** The adjunction / ** 附属物 *)

(*
Run [AdjunctionFromCouniversalArrows] on that family.  The result is a
   genuine adjunction Δ ⊣ R, produced entirely through the couniversal-arrow
   machinery of Theory/Universal/Arrow/Dual.v.

--------
在那个族上运行 [AdjunctionFromCouniversalArrows]。结果是一个真正的余挨 Δ ⊣ R，完全通过 Theory/Universal/Arrow/Dual.v 的余普遍箭头机制产生。
*)
Definition product_via_couniversal_functor : C ∏ C ⟶ C :=
  RightAdjointFunctorFromCouniversalArrows (Diagonal_Product C) product_CUA.

Definition product_via_couniversal :
  Diagonal_Product C ⊣ product_via_couniversal_functor :=
  AdjunctionFromCouniversalArrows (Diagonal_Product C) product_CUA.

(*
The object action of the produced right adjoint IS the product, on the nose
   -- the strength the primal GAFT example cannot state, its own functor being
   [Qed]-opaque.

--------
生成的右伴随的对象作用确实是乘积——确切地说
   ——原始 GAFT 示例无法说明其强度，因为它自身的函子是 [Qed] 不透明的。
*)
Corollary product_via_couniversal_obj (p : C ∏ C) :
  fobj[product_via_couniversal_functor] p = (fst p × snd p).
Proof. reflexivity. Qed.

(*
... and its counit is the projection pair, up to `≈` (see the second
   boundary recorded in the header of Theory/Universal/Arrow/Dual.v: the
   transpose leaves a [fmap_id]/[id_right] residue).

--------
... 它的余单位是投影对，直到 `≈`（参见 Theory/Universal/Arrow/Dual.v 头文件中记录的第二个边界：转置会留下 [fmap_id]/[id_right] 残留物）。
*)
Corollary product_via_couniversal_counit (p : C ∏ C) :
  @counit (C ∏ C) C (Diagonal_Product C) product_via_couniversal_functor
          product_via_couniversal p
    ≈ proj_pair p.
Proof. exact (counit_couniversal (Diagonal_Product C) product_CUA p). Qed.

(*
The arrow action is a chosen unique factorization, so nothing forces it to
   reduce to ×(C)'s [fmap]; what does hold is that the two functors are
   naturally isomorphic, right adjoints to a fixed functor being unique up to
   natural isomorphism ([right_adjoint_iso], Theory/Adjunction.v).  Pitting the
   couniversally assembled adjunction against the concrete
   [Diagonal_Product_Adjunction] over their common left adjoint Δ delivers it,
   dually to [diagonal_product_via_gaft_is_diagonal].

--------
箭头作用是一个选定的唯一分解，所以没有任何东西迫使它归约到 ×(C) 的 [fmap]；真正成立的是，这两个函子是自然同构的，固定函子的右伴随在自然同构下是唯一的（[right_adjoint_iso]，Theory/Adjunction.v）。将共宇组装的伴随与它们在共同左伴随 Δ 上的具体 [Diagonal_Product_Adjunction] 对比可以得到它，这与 [diagonal_product_via_gaft_is_diagonal] 是对偶的。
*)
Definition product_via_couniversal_is_product :
  product_via_couniversal_functor ≈ ×(C) :=
  right_adjoint_iso (Diagonal_Product C)
    product_via_couniversal_functor (×(C))
    product_via_couniversal
    (Diagonal_Product_Adjunction C).

End CouniversalExample.

(** ** A concrete instantiation / ** 一个具体实例 *)

(*
The family above is inhabited by something other than a variable: [Sets] is
   cartesian, so every pair of setoids has its couniversal arrow from the
   diagonal, and the assembled adjunction is an adjunction of [Sets].

--------
上面的族由除变量以外的东西组成：[Sets] 是笛卡尔的，所以每对集合等价类都有来自对角线的余普遍箭头，并且组装起来的伴随是 [Sets] 的一个伴随。
*)

Definition Sets_product_CUA (p : Sets ∏ Sets) :
  CouniversalArrow p (Diagonal_Product Sets) :=
  @product_CUA Sets Sets_Cartesian p.

Definition Sets_product_via_couniversal :
  Diagonal_Product Sets ⊣ @product_via_couniversal_functor Sets Sets_Cartesian :=
  @product_via_couniversal Sets Sets_Cartesian.

Corollary Sets_product_via_couniversal_obj (p : Sets ∏ Sets) :
  fobj[@product_via_couniversal_functor Sets Sets_Cartesian] p
    = @product_obj Sets Sets_Cartesian (fst p) (snd p).
Proof. reflexivity. Qed.
