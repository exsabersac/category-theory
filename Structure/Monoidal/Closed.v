Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Export Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Section Closed.

Context {C : Category}.

(*
 nLab: https://ncatlab.org/nlab/show/closed+monoidal+category
 nLab: https://ncatlab.org/nlab/show/internal+hom
 Wikipedia: https://en.wikipedia.org/wiki/Closed_monoidal_category

 A closed monoidal category is a monoidal category in which every functor
 - ⨂ y has a right adjoint y ⇒ -, the internal hom. Equivalently, for all
 objects y, z there is an internal hom object y ⇒ z equipped with an
 evaluation map

 eval : (y ⇒ z) ⨂ y ~> z

 that is universal: for every f : x ⨂ y ~> z there is a unique transpose
 (the curry) curry f : x ~> y ⇒ z with eval ∘ (curry f ⨂ id) ≈ f.

 Packaged as an adjunction, the universal property is the tensor-hom
 bijection

 Hom(x ⨂ y, z) ≅ Hom(x, y ⇒ z)         ([exp_iso])

 natural in x, y and z, expressing (- ⨂ y) ⊣ (y ⇒ -). Currying is the
 left-to-right direction, uncurrying its inverse, and eval is the image of
 the identity on y ⇒ z (the counit of the adjunction). Because the right
 tensor factor - ⨂ y is the one given the right adjoint, this is the
 right-closed structure; when C is braided the two tensorings agree and
 [flip] transports the transpose across the braiding.

 This file requires the cartesian (in fact biproduct-style) monoidal
 structure of [CartesianMonoidal] rather than bare [Monoidal], so that the
 pairing used by the substitution lemmas below is available. 

 --------
 nLab:  https://ncatlab.org/nlab/show/closed+monoidal+category 
 nLab:  https://ncatlab.org/nlab/show/internal+hom 
 维基百科:  https://en.wikipedia.org/wiki/Closed_monoidal_category 

 闭单类范畴是指在每个函子
 - ⨂ y 都有一个右伴随 y ⇒ -（即内部 Hom）的单类范畴。等价地，对于所有对象 y, z，存在一个内部 Hom 对象 y ⇒ z，并配备一个评估映射

 eval : (y ⇒ z) ⨂ y ~> z

 它是普遍的：对于每个 f : x ⨂ y ~> z，存在唯一的转置（Curry）curry f : x ~> y ⇒ z，使得 eval ∘ (curry f ⨂ id) ≈ f。

 作为伴随来封装时，这一普遍性质就是张量-Hom 双射

 Hom(x ⨂ y, z) ≅ Hom(x, y ⇒ z)         ( [exp_iso] )在 x、y 和 z 中是自然的，表示 (- ⨂ y) ⊣ (y ⇒ -)。柯里化是从左到右的方向，非柯里化是它的逆，而 eval 是 y ⇒ z 上恒等映射的像（伴随的余单位）。因为右侧的张量因子 - ⨂ y 是给定右伴随的那个，这是右闭结构；当 C 是带状结构时，两种张量方式一致，并且 [flip] 将转置通过编织传输。

 此文件需要 [CartesianMonoidal] 的笛卡尔（事实上是双积样式）单体结构，而不是单纯的 [Monoidal]，从而以下替换引理使用的配对是可用的。
*)

Reserved Infix "⇒" (at level 30, right associativity).

Class ClosedMonoidal := {
  closed_is_cartesian : @CartesianMonoidal C;   (* the underlying ⨂-structure / 基础 ⨂-结构 *)

  exponent_obj : obj → obj → obj    (* internal hom; x ⇒ y = exponent_obj x y / 内部同态；x ⇒ y = 指数对象 x y *)
    where "x ⇒ y" := (exponent_obj x y);

  (*
 The tensor-hom adjunction (- ⨂ y) ⊣ (y ⇒ -), as the natural isomorphism
 Hom(x ⨂ y, z) ≅ Hom(x, y ⇒ z).  This is the closed UMP in packaged form:
 the iso bundles existence and uniqueness of the transpose, and naturality
 recovers the substitution laws below. 

 --------
 张量-同构伴随关系 (- ⨂ y) ⊣ (y ⇒ -)，作为自然同构
 Hom(x ⨂ y, z) ≅ Hom(x, y ⇒ z)。这是封装形式的闭合UMP：
 该同构包含了转置的存在性和唯一性，自然性
 恢复了下面的代入法则。
*)
  exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z;

  curry'   {x y z} : x ⨂ y ~> z → x ~> y ⇒ z := to (@exp_iso x y z);    (* transpose: x⨂y~>z to x~>y⇒z / 转置：x⨂y~>z 到 x~>y⇒z *)
  uncurry' {x y z} : x ~> y ⇒ z → x ⨂ y ~> z := from (@exp_iso x y z);  (* inverse transpose / 逆转置 *)

  eval' {x y} : (x ⇒ y) ⨂ x ~> y := @uncurry' _ _ _ id;   (* evaluation; counit, = uncurry id / 求值；余单位 = uncurry id *)

  (*
 UMP existence-and-uniqueness: the unique transpose h = curry f satisfies
 the beta law f ≈ eval ∘ (h ⨂ id).  Uniqueness is also guaranteed by
 [exp_iso] being an isomorphism (see [uncurry_curry]). 

 --------
 UMP 存在性与唯一性：唯一的转置 h = curry f 满足 β 律 f ≈ eval ∘ (h ⨂ id)。 唯一性也由 [exp_iso] 是同构保证（参见 [uncurry_curry]）。
*)
  ump_exponents' {x y z} (f : x ⨂ y ~> z) :
    ∃! h : x ~> y ⇒ z, f ≈ eval' ∘ (h ⨂ id)
}.
#[export] Existing Instance closed_is_cartesian.

Coercion closed_is_cartesian : ClosedMonoidal >-> CartesianMonoidal.

Notation "x ⇒ y" := (exponent_obj x y)
  (at level 30, right associativity) : object_scope.

Context `{ClosedMonoidal}.

Definition curry   {x y z} : x ⨂ y ~> z → x ~> y ⇒ z := @curry' _ x y z.
Definition uncurry {x y z} : x ~> y ⇒ z → x ⨂ y ~> z := @uncurry' _ x y z.
Arguments curry' {_ _ _ _} /.
Arguments uncurry' {_ _ _ _} /.

Definition eval {x y} : (x ⇒ y) ⨂ x ~> y := uncurry id.
Arguments eval' {_ _ _} /.

Remove Hints Sets_Product_Monoidal : typeclass_instances.

Definition ump_exponents {x y z} (f : x ⨂ y ~> z) :
  ∃! h : x ~> y ⇒ z, f ≈ eval' ∘ (h ⨂ id) := @ump_exponents' _ x y z f.

#[export] Program Instance curry_respects (a b c : C) :
  Proper (equiv ==> equiv) (@curry a b c).
Next Obligation.
  proper.
  unfold curry; simpl in *.
  destruct exp_iso; simpl in *.
  destruct to; simpl in *.
  rewrites; reflexivity.
Qed.

#[export] Program Instance uncurry_respects (a b c : C) :
  Proper (equiv ==> equiv) (@uncurry a b c).
Next Obligation.
  proper.
  unfold uncurry; simpl in *.
  destruct exp_iso; simpl in *.
  destruct from; simpl in *.
  rewrites; reflexivity.
Qed.

Corollary curry_uncurry {x y z} (f : x ~> y ⇒ z) :
  curry (uncurry f) ≈ f.
Proof.
  sapply (iso_to_from (@exp_iso _ x y z)).
Qed.

Corollary uncurry_curry {x y z} (f : x ⨂ y ~> z) :
  uncurry (curry f) ≈ f.
Proof.
  sapply (iso_from_to (@exp_iso _ x y z)).
Qed.

#[local] Hint Rewrite @curry_uncurry : categories.
#[local] Hint Rewrite @uncurry_curry : categories.
#[local] Hint Rewrite @ump_exponents : categories.

(* Swap the two transposed arguments through the braiding: given a transpose of an x⨂y map, produce the transpose of the corresponding y⨂x map. / 通过编织交换两个转置的参数：给定一个 x⨂y 映射的转置，生成相应 y⨂x 映射的转置。 *)
Definition flip `{@BraidedMonoidal C} {x y z : C} `(f : x ~> y ⇒ z) :
  y ~> x ⇒ z := curry (uncurry f ∘ braid).

Corollary curry_eval {x y : C} :
  curry eval ≈ @id _ (x ⇒ y).
Proof.
  intros; unfold eval; simpl; cat.
Qed.

#[local] Hint Rewrite @curry_eval : categories.

Corollary curry_inj {x y z : C} (f g : x ⨂ y ~> z) :
  curry f ≈ curry g → f ≈ g.
Proof.
  intros.
  rewrite <- (uncurry_curry f).
  rewrite <- (uncurry_curry g).
  rewrites; reflexivity.
Qed.

Corollary uncurry_inj {x y z : C} (f g : x ~> y ⇒ z) :
  uncurry f ≈ uncurry g → f ≈ g.
Proof.
  intros.
  rewrite <- (curry_uncurry f).
  rewrite <- (curry_uncurry g).
  rewrites; reflexivity.
Qed.

End Closed.

Notation "x ⇒ y" := (exponent_obj x y)
  (at level 30, right associativity) : category_scope.

#[export] Hint Rewrite @curry_uncurry : categories.
#[export] Hint Rewrite @uncurry_curry : categories.
#[export] Hint Rewrite @ump_exponents : categories.
#[export] Hint Rewrite @curry_eval : categories.
