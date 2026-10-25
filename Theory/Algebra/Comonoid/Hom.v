Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Comonoid.

Generalizable All Variables.

(** * Comonoid homomorphisms and the category of internal comonoids / * 余单体同态与内部余单体的范畴 *)

(*
nLab: https://ncatlab.org/nlab/show/comonoid

   Given internal comonoids (x, delta[Cx], epsilon[Cx]) and
   (y, delta[Cy], epsilon[Cy]) in a monoidal category (C, ⨂, I), a morphism
   f : x ~> y is a comonoid homomorphism when it commutes with the
   comultiplications and counits:

     comultiplication square   delta[Cy] ∘ f ≈ (f ⨂ f) ∘ delta[Cx]
     counit triangle           epsilon[Cy] ∘ f ≈ epsilon[Cx]

   This is the exact arrow-reversed mirror of [MonoidHom] in
   Theory/Algebra/Monoid/Hom.v.  Comonoid homomorphisms contain the
   identities and are closed under composition, so internal comonoids and
   their homomorphisms form a category Comon(C), packaged with sigma objects
   and homs exactly as [Mon] is — morphism equivalence is equivalence of the
   underlying C-morphisms — and projecting out the underlying object and
   morphism gives the forgetful functor Comon(C) ⟶ C, faithful by
   construction ([Comon_Forget_Faithful]).

   Beyond its algebraic role, this class is the predicate behind
   *determinism* in categorical probability: in a category where every
   object carries a canonical copy/discard comonoid (the CD-categories of
   Cho–Jacobs, arXiv:1709.00322 §2), a morphism is called deterministic
   (Fritz, arXiv:1908.07021, Definition 10.1; the condition goes back to
   Carboni–Walters) precisely when it is a comonoid homomorphism between
   the canonical comonoids — copying the output of f is the same as
   running f twice on a copied input, and discarding the output is the
   same as discarding the input.
   Structure/Monoidal/CopyDiscard/Deterministic.v instantiates this class at
   those canonical comonoids.

   The [Comonoid_Iso] transport at the end moves a comonoid structure across
   an isomorphism i : x ≅ y by conjugation; both components of i then become
   comonoid homomorphisms — with respect to the TRANSPORTED structure on the
   codomain.  It is provided as standalone infrastructure and currently has
   no in-tree consumer.  In particular,
   Structure/Monoidal/CopyDiscard/Deterministic.v does NOT use it: the
   determinism of the structural isomorphisms demands a [ComonoidHom]
   between the canonical comonoids at BOTH endpoints, whereas the transport
   only yields homomorphisms into [Comonoid_Iso i Cx], so those lemmas are
   proved there by direct coherence chases at the canonical supply.

--------
nLab：https://ncatlab.org/nlab/show/comonoid

在一个幺半群范畴 (C, ⨂, I) 中，给定内部余单子 (x, delta[Cx], epsilon[Cx]) 和 (y, delta[Cy], epsilon[Cy])，当一个态射 f : x ~> y 与余乘法和余单位交换时，它是一个余单子同态:

余乘法方形   delta[Cy] ∘ f ≈ (f ⨂ f) ∘ delta[Cx]
     余单位三角形   epsilon[Cy] ∘ f ≈ epsilon[Cx]

这是在 Theory/Algebra/Monoid/Hom.v 中 [MonoidHom] 的完全箭头反转镜像。余单同态包含恒等映射并在复合下封闭，因此内部余单和它们的同态形成一个范畴 Comon(C)，与 sigma 对象和 hom 完全像 [Mon] 一样打包——态射等价就是底层 C-态射的等价——而投射出底层对象和态射就得到遗忘函子 Comon(C) ⟶ C，其构造上是忠实的 ([Comon_Forget_Faithful])。

超越其代数角色，这个类是范畴概率中*确定性*背后的谓词：在每个对象都携带一个典范复制/丢弃余单体的范畴中（Cho–Jacobs 的 CD 范畴，arXiv:1709.00322 §2），一个态射被称为确定性（Fritz, arXiv:1908.07021, 定义 10.1；这个条件可以追溯到 Carboni–Walters）当且仅当它是典范余单体之间的余单体同态——复制 f 的输出等同于在复制的输入上运行 f 两次，而丢弃输出等同于丢弃输入。Structure/Monoidal/CopyDiscard/Deterministic.v 在这些典范余单体上实例化了这个类。

[Comonoid_Iso] 传输在末端通过共轭将一个余 monoid 结构沿同构 i : x ≅ y 移动；i 的两个分量随后都成为余 monoid 同态——相对于目标上的传输结构。它以独立基础设施的形式提供，目前在树中没有使用者。特别是，Structure/Monoidal/CopyDiscard/Deterministic.v 并未使用它：结构同构的确定性要求在两个端点的标准余 monoid 之间有 [ComonoidHom]，而传输只产生到 [Comonoid_Iso i Cx] 的同态，因此那些引理在标准供应处通过直接的相容性追赶证明。
*)

Section ComonoidHom.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class ComonoidHom {x y : C} (Cx : Comonoid x) (Cy : Comonoid y)
      (f : x ~> y) : Type := {
  (* f preserves comultiplication: delta[Cy] ∘ f ≈ (f ⨂ f) ∘ delta[Cx] / f 保持余乘法：delta[Cy] ∘ f ≈ (f ⨂ f) ∘ delta[Cx] *)
  hom_delta   : delta[Cy] ∘ f ≈ (f ⨂ f) ∘ delta[Cx];
  (* f preserves the counit: epsilon[Cy] ∘ f ≈ epsilon[Cx] / f 保持余单位：epsilon[Cy] ∘ f ≈ epsilon[Cx] *)
  hom_epsilon : epsilon[Cy] ∘ f ≈ epsilon[Cx]
}.

(* The identity is a comonoid homomorphism. / 恒等映射是一个余单子同态。 *)
Lemma ComonoidHom_id {x} (Cx : Comonoid x) : ComonoidHom Cx Cx id.
Proof. split; cat. Qed.

(*
Comonoid homomorphisms are closed under composition: paste the two
   preservation squares, fusing (f ⨂ f) ∘ (g ⨂ g) into (f ∘ g) ⨂ (f ∘ g)
   by the interchange law [bimap_comp].

--------
余单子同态在复合运算下是封闭的：将两个保持图拼接，将 (f ⨂ f) ∘ (g ⨂ g) 通过交换律 [bimap_comp] 融合为 (f ∘ g) ⨂ (f ∘ g)。
*)
Lemma ComonoidHom_comp {x y z} {Cx : Comonoid x} {Cy : Comonoid y}
      {Cz : Comonoid z} {f : y ~> z} {g : x ~> y} :
  ComonoidHom Cy Cz f → ComonoidHom Cx Cy g → ComonoidHom Cx Cz (f ∘ g).
Proof.
  intros F G.
  split.
  - rewrite comp_assoc.
    rewrite (@hom_delta _ _ _ _ _ F).
    rewrite <- comp_assoc.
    rewrite (@hom_delta _ _ _ _ _ G).
    rewrite comp_assoc.
    now rewrite <- bimap_comp.
  - rewrite comp_assoc.
    rewrite (@hom_epsilon _ _ _ _ _ F).
    apply (@hom_epsilon _ _ _ _ _ G).
Qed.

(* Being a comonoid homomorphism transports along ≈ (bimap respects ≈). / 作为一个余单同态沿 ≈ 传输（bimap 尊重 ≈）。 *)
Lemma ComonoidHom_equiv {x y} {Cx : Comonoid x} {Cy : Comonoid y}
      {f g : x ~> y} :
  f ≈ g → ComonoidHom Cx Cy f → ComonoidHom Cx Cy g.
Proof.
  intros E F.
  split.
  - rewrite <- E.
    apply (@hom_delta _ _ _ _ _ F).
  - rewrite <- E.
    apply (@hom_epsilon _ _ _ _ _ F).
Qed.

(*
Transport of a comonoid structure across an isomorphism i : x ≅ y, by
   conjugation: copy on y is "carry back along i⁻¹, copy on x, carry both
   halves forward along i", and discard on y is "carry back, discard".  The
   laws are those of Cx conjugated by i; each proof cancels the inner
   [from i ∘ to i], applies the corresponding law of Cx, and transports the
   result across the naturality square of the relevant structural map.

--------
通过同构 i : x ≅ y 将余单子结构的传递，通过共轭实现：在 y 上的复制是“沿 i⁻¹ 携回，在 x 上复制，然后将两半沿 i 带到前面”，在 y 上的丢弃是“携回，丢弃”。 法则是 Cx 的法则通过 i 共轭；每个证明都会消去内部的 [from i ∘ to i]，应用 Cx 的相应法则，并将结果通过相关结构映射的自然性方格进行传递。
*)

#[local] Obligation Tactic := intros.

Program Definition Comonoid_Iso {x y : C} (i : x ≅ y) (Cx : Comonoid x) :
  Comonoid y := {|
  delta   := (to i ⨂ to i) ∘ delta[Cx] ∘ from i;
  epsilon := epsilon[Cx] ∘ from i
|}.
Next Obligation.
  (*
coassociativity: cancel the conjugating iso on the right, then it is
     [delta_coassoc] of Cx pushed across the associator's naturality.

--------
余结合性：取消右边的共轭同构，然后它就是穿过结合子的自然性推动的 Cx 的 [delta_coassoc]。
*)
  apply (iso_to_epic i).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  assert (E : ((to i ⨂ to i) ∘ delta[Cx]) ⨂ to i
                ≈ ((to i ⨂ to i) ⨂ to i) ∘ (delta[Cx] ⨂ id)).
  { rewrite <- bimap_comp; cat. }
  rewrite E; clear E.
  rewrite <- comp_assoc.
  rewrite (@delta_coassoc _ _ _ Cx).
  normal.
  rewrite from_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  normal.
  reflexivity.
Qed.
Next Obligation.
  (*
left counit: cancel the conjugating iso, apply [delta_counit_left] of
     Cx, and close with naturality of the left unitor's inverse.

--------
左余单位：取消结合的同构，应用 Cx 的 [delta_counit_left]，并用左单位子的逆的自然性闭合。
*)
  apply (iso_to_epic i).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  assert (E : epsilon[Cx] ⨂ to i ≈ (id ⨂ to i) ∘ (epsilon[Cx] ⨂ id)).
  { rewrite <- bimap_comp; cat. }
  rewrite E; clear E.
  rewrite <- comp_assoc.
  rewrite (@delta_counit_left _ _ _ Cx).
  apply from_unit_left_natural.
Qed.
Next Obligation.
  (* right counit: mirror of the previous obligation. / 右余约：前一义务的镜像。 *)
  apply (iso_to_epic i).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  assert (E : to i ⨂ epsilon[Cx] ≈ (to i ⨂ id) ∘ (id ⨂ epsilon[Cx])).
  { rewrite <- bimap_comp; cat. }
  rewrite E; clear E.
  rewrite <- comp_assoc.
  rewrite (@delta_counit_right _ _ _ Cx).
  apply from_unit_right_natural.
Qed.

#[local] Obligation Tactic := cat_simpl.

(*
Both components of the isomorphism are comonoid homomorphisms with
   respect to the transported structure.

--------
同构的两个分量都是关于传递结构的余单元同态。
*)
Lemma ComonoidHom_Iso_to {x y} (i : x ≅ y) (Cx : Comonoid x) :
  ComonoidHom Cx (Comonoid_Iso i Cx) (to i).
Proof.
  split; simpl.
  - rewrite <- !comp_assoc.
    rewrite iso_from_to; cat.
  - rewrite <- comp_assoc.
    rewrite iso_from_to; cat.
Qed.

Lemma ComonoidHom_Iso_from {x y} (i : x ≅ y) (Cx : Comonoid x) :
  ComonoidHom (Comonoid_Iso i Cx) Cx (from i).
Proof.
  split; simpl.
  - symmetry.
    rewrite comp_assoc.
    normal.
    rewrite !iso_from_to; cat.
  - reflexivity.
Qed.

(*
The category Comon(C) of internal comonoids in C: objects are objects of
   C equipped with a comonoid structure, morphisms are C-morphisms equipped
   with a proof of homomorphy, and equivalence is equivalence of the
   underlying morphisms — the same sigma packaging as [Mon] and [Sub] in
   Construction/Subcategory.v.

--------
在 C 中的内余单元的范畴 Comon(C)：对象是配备有余单元结构的 C 的对象，态射是配备有同态证明的 C-态射，而等价性是基础态射的等价性——与 Construction/Subcategory.v 中的 [Mon] 和 [Sub] 的 sigma 封装相同。
*)
Program Definition Comon : Category := {|
  obj     := { x : C & Comonoid x };
  hom     := fun X Y => { f : `1 X ~> `1 Y & ComonoidHom `2 X `2 Y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun X => (id; ComonoidHom_id `2 X);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; ComonoidHom_comp `2 f `2 g)
|}.

(*
The forgetful functor Comon(C) ⟶ C projects out the underlying object
   and morphism; it is faithful by construction ([Comon_Forget_Faithful]
   below).

--------
遗忘函子 Comon(C) ⟶ C 投射出基础对象和态射；它从构造上是忠实的（见下文的 [Comon_Forget_Faithful]）。
*)
Program Definition Comon_Forget : Comon ⟶ C := {|
  fobj := fun X => `1 X;
  fmap := fun _ _ f => `1 f
|}.

(*
Faithfulness is definitional: morphism equivalence in Comon(C) IS
   equivalence of the underlying C-morphisms, which is what [fmap] projects
   out.

--------
忠实性是定义性的：Comon(C) 中的态射等价就是底层 C-态射的等价，这就是 [fmap] 投影出来的内容。
*)
#[export] Instance Comon_Forget_Faithful : Faithful Comon_Forget.
Proof.
  constructor.
  intros X Y f g E.
  exact E.
Qed.

End ComonoidHom.

Arguments Comon C {M}.
