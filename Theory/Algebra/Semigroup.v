Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.

Generalizable All Variables.

(** * Internal semigroups in a monoidal category, and the category Smgrp / * 幺半群范畴中的内部半群，以及范畴 Smgrp *)

(*
nLab: https://ncatlab.org/nlab/show/semigroup
   nLab: https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
   Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
         Springer GTM 5, 1998, §VI.4, printed p. 144 (PDF p. 153) —
         maclane:VI.4:construction1

   Mac Lane opens §VI.4, from the page image: “A semigroup is a set S
   equipped with an associative binary operation ν: S × S → S”, and he
   writes Smgrp for “the category of all small semigroups”, with the
   forgetful functor G : Smgrp → Set.  This file states the definition
   internally, as Theory/Algebra/Monoid.v states monoids: a semigroup on
   an object X of a monoidal category (C, ⨂, I) is a multiplication
   smu : X ⨂ X ~> X with

     associativity  smu ∘ (smu ⨂ id) ≈ smu ∘ (id ⨂ smu) ∘ α

   (α = to tensor_assoc) and nothing more: no unit, so no unitor.
   [SemigroupHom] asks of f : x ~> y the multiplication square
   f ∘ smu ≈ smu ∘ (f ⨂ f) alone.  [Smgrp C] packages the semigroups and
   their homomorphisms with sigma objects and homs, arrows compared by
   their underlying arrows, exactly as Theory/Algebra/Monoid/Hom.v
   packages [Mon C]; [Smgrp_Forget] projects, faithfully by construction
   ([Smgrp_Forget_Faithful]).  [Mon_Smgrp] : Mon C ⟶ Smgrp C forgets the
   unit; after the two forgetful functors it is [Mon_Forget] on objects
   and on arrows at [eq_refl] ([Mon_Smgrp_Forget_obj],
   [Mon_Smgrp_Forget_map]).  Mac Lane's Smgrp is [Smgrp] at (Sets, ×),
   Instance/Smgrp.v's [SmgrpSets]; the free semigroup, the word monad W
   and the monadicity of Smgrp over Set are Instance/Smgrp.v and
   Instance/Smgrp/Word.v.

   NAMES.  The class [Semigroup] is the sibling of Theory/Algebra/
   Monoid.v's [Monoid], internal to an arbitrary monoidal category, and
   not of Structure/Monoid.v's cartesian [MonoidObject], from which
   Structure/Lattice.v builds its lattice objects.  It shares its short
   name with Theory/Coq/Semigroup.v's ops-only class, as [Monoid] shares
   its name with Theory/Coq/Monoid.v's; no file of the tree requires
   both.  No [PropEquiv] is asked (Lib/Setoid/Propositional.v's regime
   is that of the algebraic records CMon, Grp and the rest): [Mon] does
   not carry it either, and no adjoint functor theorem is involved here.

   STRENGTHS.  The two readbacks hold at [eq_refl], and
   Test/ProbeWord470.v restates them (C1, C2).  The laws of the category
   and of the two functors are the [Program] obligations of [Smgrp],
   [Smgrp_Forget] and [Mon_Smgrp], twelve, closed by the ambient tactic as
   in Theory/Algebra/Monoid/Hom.v; the four lemmas end [Qed], and no proof
   ends [Defined] (counted by token).  Nothing here is refused.

   UNIVERSES, read off [About].  [Smgrp@{u u0 u1 u2}],
   [Smgrp_Forget_Faithful] and the two readbacks have exactly the block of
   [Mon@{u u0 u1 u2}] (u0 < u2, u <= u1, u0 <= u1, with the caps of the
   standard library's sigma and pair projections), and [Smgrp_Forget],
   [Mon_Smgrp] and their six obligations that of [Mon_Forget] (u0 < u1,
   u <= u2, u0 <= u2, with those caps).  The class, the homomorphism
   record, their constructors and fields, the three homomorphism lemmas,
   [Monoid_Semigroup], [MonoidHom_SemigroupHom] and four of [Smgrp]'s six
   obligations bind @{u u0} with caps only; the other two bind @{u u0 u1}
   with u0 < u1.  No [Set] and no equation.  On Coq 8.20.1 every constant
   here has the same binder and the same constraints between bound
   levels; on Coq 8.19.2 so does every constant but the six obligations
   of [Smgrp], which bind one or two levels more (compared by script,
   the names of the standard library's caps differing by version).

   NOT DELIVERED.  Free semigroups, limits and colimits of semigroups in
   this generality; commutative semigroups; the semigroup of a lax
   monoidal functor; the unit-free variant of Structure/Lattice.v's
   lattice objects.

--------
nLab: https://ncatlab.org/nlab/show/semigroup
nLab: https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
书籍: Mac Lane，《为工作数学家准备的范畴论》，第2版，
      Springer GTM 5, 1998, §VI.4, 印刷页 144（PDF 页 153）—
      maclane:VI.4:construction1

Mac Lane 在 §VI.4 中这样开头，在页面图像上写道：“半群是一个集合 S，配备了一个结合的二元运算 ν: S × S → S”，并且他将 Smgrp 写作“所有小半群的范畴”，带有遗忘函子 G : Smgrp → Set。该文件在内部给出了定义，就像 Theory/Algebra/Monoid.v 定义幺半群一样：在一个幺半范畴 (C, ⨂, I) 的对象 X 上的半群是一个乘法 smu : X ⨂ X ~> X，

结合性  smu ∘ (smu ⨂ id) ≈ smu ∘ (id ⨂ smu) ∘ α

(α = 对应于 tensor_assoc) 就没有其他内容：没有单位，因此也没有单位同态。   
[SemigroupHom] 对 f : x ~> y 提出乘法方格 f ∘ smu ≈ smu ∘ (f ⨂ f) 本身。[Smgrp C] 将半群及其同态与 sigma 对象和同态打包，箭头通过其基础箭头比较，正如 Theory/Algebra/Monoid/Hom.v 打包 [Mon C] 一样；[Smgrp_Forget] 通过构造忠实地投射 ([Smgrp_Forget_Faithful])。[Mon_Smgrp] : Mon C ⟶ Smgrp C 忘记单位；在经历两个遗忘函子之后，它在对象上对应 [Mon_Forget]，在箭头上对应 [eq_refl] ([Mon_Smgrp_Forget_obj], [Mon_Smgrp_Forget_map])。Mac Lane 的 Smgrp 是 (Sets, ×) 上的 [Smgrp]，Instance/Smgrp.v 的 [SmgrpSets]；自由半群、单词单子 W 以及 Smgrp 对 Set 的单子性都是 Instance/Smgrp.v 和 Instance/Smgrp/Word.v。

名称。类 [Semigroup] 是 Theory/Algebra/Monoid.v 的 [Monoid] 的姊妹类，属于任意幺半群范畴的内部类，而不是 Structure/Monoid.v 的笛卡尔 [MonoidObject]，Structure/Lattice.v 的格对象就是从它构建的。它的简称与 Theory/Coq/Semigroup.v 的仅操作类相同，就像 [Monoid] 与 Theory/Coq/Monoid.v 的名称相同；树中的任何文件都不需要同时使用两者。没有要求 [PropEquiv]（Lib/Setoid/Propositional.v 的机制是代数记录 CMon、Grp 等）；[Mon] 也没有包含它，这里也没有涉及伴随定理。

优势。两个回读保持在 [eq_refl]，Test/ProbeWord470.v 重申它们（C1, C2）。该范畴以及这两个函子的法律是 [Program] 对 [Smgrp]、[Smgrp_Forget] 和 [Mon_Smgrp] 的义务，共有十二个，通过环境策略封闭，如 Theory/Algebra/Monoid/Hom.v 中所示；四个引理以 [Qed] 结束，没有证明以 [Defined] 结束（按标记计数）。此处没有被拒绝的内容。

宇宙，读取 [About]。[Smgrp@{u u0 u1 u2}]、[Smgrp_Forget_Faithful] 和两个回读拥有完全相同的 [Mon@{u u0 u1 u2}] 块（u0 < u2，u <= u1，u0 <= u1，使用标准库的 sigma 和 pair 投影的上限），而 [Smgrp_Forget]、[Mon_Smgrp] 及其六个义务则拥有 [Mon_Forget] 的块（u0 < u1，u <= u2，u0 <= u2，带有那些上限）。类、同态记录、它们的构造函数和字段、三个同态引理、[Monoid_Semigroup]、[MonoidHom_SemigroupHom] 以及 [Smgrp] 的六个义务中的四个仅绑定 @{u u0} 并有上限；另外两个绑定 @{u u0 u1} 并满足 u0 < u1。没有 [Set]，也没有方程。在 Coq 8.20.1 中，所有常量具有相同的绑定器以及绑定级别之间相同的约束；在 Coq 8.19.2 中，所有常量也如此，但 [Smgrp] 的六个义务绑定了一个或两个额外级别（通过脚本比较，标准库的上限名称因版本不同而异）。

未交付。一般性下的自由半群、半群的极限与余极限；交换半群；松弛幺半单范畴的半群；Structure/Lattice.v 的无单位版本的格对象。
*)

Section Semigroup.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Semigroup (X : C) : Type := {
  smu : X ⨂ X ~> X;             (* multiplication ν : X ⨂ X ~> X / 乘法 ν : X ⨂ X ~> X *)

  (* associativity: smu ∘ (smu ⨂ id) ≈ smu ∘ (id ⨂ smu) ∘ α / 结合性：smu ∘ (smu ⨂ id) ≈ smu ∘ (id ⨂ smu) ∘ α *)
  smu_assoc :
    smu ∘ bimap smu id[X]
      ≈ smu ∘ bimap id[X] smu ∘ to tensor_assoc
}.

End Semigroup.

Arguments smu {C M X _}.

Notation "'smu[' Sg ]" := (@smu _ _ _ Sg)
  (at level 9, format "'smu[' Sg ]") : morphism_scope.

Section SemigroupHom.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class SemigroupHom {x y : C} (Sx : Semigroup x) (Sy : Semigroup y)
      (f : x ~> y) : Type := {
  (* f preserves multiplication: f ∘ smu[Sx] ≈ smu[Sy] ∘ (f ⨂ f) / f 保持乘法：f ∘ smu[Sx] ≈ smu[Sy] ∘ (f ⨂ f) *)
  shom_mu : f ∘ smu[Sx] ≈ smu[Sy] ∘ (f ⨂ f)
}.

(* The identity is a semigroup homomorphism. / 该恒等映射是半群同态。 *)
Lemma SemigroupHom_id {x} (Sx : Semigroup x) : SemigroupHom Sx Sx id.
Proof. constructor; cat. Qed.

(*
Semigroup homomorphisms compose: paste the two preservation squares,
   fusing (f ⨂ f) ∘ (g ⨂ g) into (f ∘ g) ⨂ (f ∘ g) by [bimap_comp].

--------
半群同态可以组合：将两个保持图粘贴在一起，通过 [bimap_comp] 将 (f ⨂ f) ∘ (g ⨂ g) 融合为 (f ∘ g) ⨂ (f ∘ g)。
*)
Lemma SemigroupHom_comp {x y z} {Sx : Semigroup x} {Sy : Semigroup y}
      {Sz : Semigroup z} {f : y ~> z} {g : x ~> y} :
  SemigroupHom Sy Sz f → SemigroupHom Sx Sy g → SemigroupHom Sx Sz (f ∘ g).
Proof.
  intros F G.
  constructor.
  rewrite <- comp_assoc.
  rewrite (@shom_mu _ _ _ _ _ G).
  rewrite comp_assoc.
  rewrite (@shom_mu _ _ _ _ _ F).
  rewrite <- comp_assoc.
  now rewrite <- bimap_comp.
Qed.

(* Being a semigroup homomorphism transports along ≈. / 作为半群同态沿 ≈ 进行传输。 *)
Lemma SemigroupHom_equiv {x y} {Sx : Semigroup x} {Sy : Semigroup y}
      {f g : x ~> y} :
  f ≈ g → SemigroupHom Sx Sy f → SemigroupHom Sx Sy g.
Proof.
  intros E F.
  constructor.
  rewrite <- E.
  apply (@shom_mu _ _ _ _ _ F).
Qed.

(*
The category Smgrp(C) of internal semigroups in C, packaged with sigma
   objects and homs exactly as Theory/Algebra/Monoid/Hom.v packages Mon(C):
   morphism equivalence is equivalence of the underlying C-morphisms.

--------
在 C 中的内部半群范畴 Smgrp(C)，按 Theory/Algebra/Monoid/Hom.v 打包 Mon(C) 的方式打包 σ 对象和同态：态射等价是底层 C 态射的等价。
*)
Program Definition Smgrp : Category := {|
  obj     := { x : C & Semigroup x };
  hom     := fun X Y => { f : `1 X ~> `1 Y & SemigroupHom `2 X `2 Y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun X => (id; SemigroupHom_id `2 X);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; SemigroupHom_comp `2 f `2 g)
|}.

(*
The forgetful functor Smgrp(C) ⟶ C projects out the underlying object
   and morphism.

--------
忘记函子 Smgrp(C) ⟶ C 投射出其底层对象和态射。
*)
Program Definition Smgrp_Forget : Smgrp ⟶ C := {|
  fobj := fun X => `1 X;
  fmap := fun _ _ f => `1 f
|}.

(* Faithful by construction, as [Mon_Forget_Faithful] is. / 天生可靠，就像 [Mon_Forget_Faithful] 一样。 *)
#[export] Instance Smgrp_Forget_Faithful : Faithful Smgrp_Forget.
Proof.
  constructor.
  intros X Y f g E.
  exact E.
Qed.

(* Every internal monoid is an internal semigroup: forget the unit. / 每一个内部幺半群都是一个内部半群：忽略单位元。 *)
Definition Monoid_Semigroup {x : C} (Mx : Monoid x) : Semigroup x :=
  {| smu := mu[Mx]; smu_assoc := @mu_assoc _ _ _ Mx |}.

(* Every monoid homomorphism is a semigroup homomorphism. / 每个幺半群同态都是半群同态。 *)
Definition MonoidHom_SemigroupHom {x y : C} {Mx : Monoid x} {My : Monoid y}
           {f : x ~> y} (H : MonoidHom Mx My f) :
  SemigroupHom (Monoid_Semigroup Mx) (Monoid_Semigroup My) f :=
  @Build_SemigroupHom _ _ (Monoid_Semigroup Mx) (Monoid_Semigroup My) f
    (@hom_mu _ _ _ _ _ _ _ H).

(* The functor Mon(C) ⟶ Smgrp(C) that forgets the unit. / 将单位忘掉的函子 Mon(C) ⟶ Smgrp(C)。 *)
Program Definition Mon_Smgrp : Mon C ⟶ Smgrp := {|
  fobj := fun X => (`1 X; Monoid_Semigroup `2 X);
  fmap := fun _ _ f => (`1 f; MonoidHom_SemigroupHom `2 f)
|}.

(* Forgetting the unit and then the multiplication is forgetting both. / 忘记了单位，然后忘记乘法就是把两者都忘了。 *)
Example Mon_Smgrp_Forget_obj (X : Mon C) :
  fobj[Smgrp_Forget] (fobj[Mon_Smgrp] X) = fobj[Mon_Forget] X := eq_refl.

Example Mon_Smgrp_Forget_map {X Y : Mon C} (f : X ~> Y) :
  fmap[Smgrp_Forget] (fmap[Mon_Smgrp] f) = fmap[Mon_Forget] f := eq_refl.

End SemigroupHom.

Arguments Smgrp C {M}.
