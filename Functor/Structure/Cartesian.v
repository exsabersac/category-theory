Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cartesian.

Generalizable All Variables.

(** Cartesian (product-preserving) functors.  / 笛卡尔（乘积保持）函子。*)

(*
nLab: https://ncatlab.org/nlab/show/product-preserving+functor
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

   A cartesian functor F : C ⟶ D between cartesian categories preserves
   finite (here binary) products. Concretely, for every pair of objects the
   canonical comparison map

       φ : F (x × y) ~> F x × F y,     φ = ⟨fmap exl, fmap exr⟩,

   built from the universal property of F x × F y applied to the images of
   the projections, is required to be an isomorphism. This is recorded as the
   field [fobj_prod_iso : F (x × y) ≅ F x × F y]; its forward direction [to]
   is φ ([prod_out]) and its inverse [from] is φ⁻¹ ([prod_in]). A functor
   preserves the product exactly when this comparison is invertible, so a
   cartesian functor is the same data as a strong monoidal functor for the
   cartesian monoidal structures (tensor = ×, unit = the terminal object).

   The remaining fields fix the comparison and pin down [fmap] on the
   universal operations. [fmap_exl] and [fmap_exr] state that φ ([prod_out])
   is indeed ⟨fmap exl, fmap exr⟩, since exl ∘ φ ≈ fmap exl and
   exr ∘ φ ≈ fmap exr. [fmap_fork] states the dual coherence that F carries
   pairing to pairing up to the comparison, fmap ⟨f, g⟩ ≈ φ⁻¹ ∘ ⟨fmap f, fmap
   g⟩, equivalently φ ∘ fmap ⟨f, g⟩ ≈ ⟨fmap f, fmap g⟩.

   This class axiomatizes only the binary-product comparison. Preservation of
   the nullary product, i.e. of the terminal object F 1 ≅ 1 (the empty
   product), is the separate concern [TerminalFunctor]; the two together give
   the full strong monoidal (cartesian) functor. The dual notion, a functor
   preserving binary coproducts, is named [CocartesianFunctor] below via the
   opposite functor F^op, following the library's built-in duality. 

--------
nLab：https://ncatlab.org/nlab/show/product-preserving+functor
 维基百科：https://en.wikipedia.org/wiki/Limit_(category_theory)

笛卡尔范畴之间的笛卡尔函子 F : C ⟶ D 保留
 有限（此处为二进制）乘积。 具体来说，对于每对对象
 规范比较图

φ : F (x × y) ~> F x × F y, φ = ⟨fmap exl, fmap exr⟩,

根据应用于图像的 F x × F y 的通用属性构建
 的投影，要求是同构的。 这被记录为
 [fobj_prod_iso : F (x × y) ≅ F x × F y] 字段； 其前进方向 [to]
 是 φ ([prod_out])，其逆 [from] 是 φ⁻1 ([prod_in])。 函子
 当比较可逆时准确地保留乘积，因此
 笛卡尔函子与强幺半群函子的数据相同
 笛卡尔幺半群结构（张量 = ×，单位 = 终端对象）。

其余字段修复比较并固定 [fmap]
 通用操作。 [fmap_exl] 和 [fmap_exr] 指出 φ ([prod_out])
 确实是 ⟨fmap exl, fmap exr⟩，因为 exl ∘ φ ≈ fmap exl 并且
 exr ∘ φ ≈ fmap exr。 [fmap_fork] 陈述 F 携带的双重相干性
 配对到配对到比较， fmap ⟨f, g⟩ ≈ φ⁻¹ ∘ ⟨fmap f, fmap
 g⟩，相当于 φ ∘ fmap ⟨f，g⟩ ≈ ⟨fmap f，fmap g⟩。

此类仅将二元乘积比较公理化。 保存
 零乘积，即最终对象 F 1 ≅ 1（空
 产品），是单独关注的 [TerminalFunctor]； 两者一起给予
 完整的强幺半群（笛卡尔）函子。 对偶概念，函子
 保留二元余积，在下面被命名为 [CocartesianFunctor]
 相反的函子 F^op，遵循库的内置对偶性。 
*)

Section CartesianFunctor.

Context `{F : C ⟶ D}.
Context `{@Cartesian C}.
Context `{@Cartesian D}.

Class CartesianFunctor := {
  (* the comparison iso F (x × y) ≅ F x × F y witnessing product preservation  / 比较 iso F(x × y) ≅ F x × F y 见证产品保存*)
  fobj_prod_iso {x y : C} : F (x × y) ≅ F x × F y;

  prod_in  := fun x y => from (@fobj_prod_iso x y);  (* φ⁻¹ : F x × F y ~> F (x × y) *)
  prod_out := fun x y => to   (@fobj_prod_iso x y);  (* φ   : F (x × y) ~> F x × F y *)

  fmap_exl {x y : C} : fmap (@exl C _ x y) ≈ exl ∘ prod_out _ _;  (* exl ∘ φ ≈ fmap exl *)
  fmap_exr {x y : C} : fmap (@exr C _ x y) ≈ exr ∘ prod_out _ _;  (* exr ∘ φ ≈ fmap exr *)

  (* F carries pairing to pairing up to φ⁻¹: fmap ⟨f, g⟩ ≈ φ⁻¹ ∘ ⟨fmap f, fmap g⟩  / F 进行配对至 φ⁻1 为止的配对： fmap ⟨f, g⟩ ≈ φ⁻1 ∘ ⟨fmap f, fmap g⟩*)
  fmap_fork {x y z : C} (f : x ~> y) (g : x ~> z) :
    fmap (f △ g) ≈ prod_in _ _ ∘ fmap f △ fmap g
}.

Arguments prod_in {_ _ _} /.
Arguments prod_out {_ _ _} /.

Context `{@CartesianFunctor}.

Corollary prod_in_out (x y : C) :
  prod_in ∘ prod_out ≈ @id _ (F (x × y)).
Proof.
  intros.
  exact (iso_from_to fobj_prod_iso).
Qed.

#[local] Hint Rewrite @prod_in_out : functors.

Corollary prod_out_in (x y : C) :
  prod_out ∘ prod_in ≈ @id _ (F x × F y).
Proof.
  intros.
  exact (iso_to_from fobj_prod_iso).
Qed.

#[local] Hint Rewrite @prod_out_in : functors.

Corollary prod_in_inj {x y z : C} (f g : F x ~> F y × F z) :
  prod_in ∘ f ≈ prod_in ∘ g ↔ f ≈ g.
Proof.
  split; intros Hprod.
  - rewrite <- id_left.
    rewrite <- prod_out_in.
    rewrite <- comp_assoc.
    rewrite Hprod.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  - subst.
    rewrite Hprod.
    reflexivity.
Qed.

Corollary prod_out_inj {x y z : C} (f g : F x ~> F (y × z)) :
  prod_out ∘ f ≈ prod_out ∘ g ↔ f ≈ g.
Proof.
  split; intros Hprod.
  - rewrite <- id_left.
    rewrite <- prod_in_out.
    rewrite <- comp_assoc.
    rewrite Hprod.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  - subst.
    rewrite Hprod.
    reflexivity.
Qed.

End CartesianFunctor.

Arguments prod_in {_ _ _ _ _ _ _ _} /.
Arguments prod_out {_ _ _ _ _ _ _ _} /.

#[export] Hint Rewrite @prod_in_out : functors.
#[export] Hint Rewrite @prod_out_in : functors.

(*
A cocartesian functor preserves binary coproducts. Rather than restate the
   dual class, it is defined by reusing [CartesianFunctor] on the opposite
   functor F^op (coproducts in C are products in C^op), exploiting the
   library's built-in duality. The first notation infers the categories; the
   second names them explicitly, requiring C, D and F at object level. 

--------
余笛卡尔函子保留二元余积。 而不是重述
 双类，它是通过在相反的位置重用 [CartesianFunctor] 来定义的
 函子 F^op（C 中的余积是 C^op 中的积），利用
 库的内置二元性。 第一个符号推断类别； 的
 第二个明确地命名它们，要求在对象级别上使用 C、D 和 F。 
*)
Notation "'CocartesianFunctor' F" := (@CartesianFunctor _ _ (F^op) _ _)
  (at level 9) : category_theory_scope.
Notation "@CocartesianFunctor C D F" :=
  (@CartesianFunctor (C^op) (D^op) (F^op) _ _)
  (at level 9) : category_theory_scope.
