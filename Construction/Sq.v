Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.DoubleCategory.
Require Import Category.Theory.DoubleCategory.Companion.

Generalizable All Variables.

(*
   * * The double category of commuting squares

   nLab: https://ncatlab.org/nlab/show/double+category (Examples)

   For any category [C], there is a double category [Sq C] whose objects
   are the objects of [C], whose vertical AND horizontal 1-cells are both
   the morphisms of [C], and whose squares

   a --h--> b
   |        |
   u        v
   v        v
   c --k--> d

   are the proofs that the square commutes: [dsq h u v k := k ∘ u ≈ v ∘ h].
   A square is a mere proposition (an inhabitant of the hom-setoid's
   relation), so we equip it with the TRIVIAL setoid identifying all
   inhabitants; every coherence field of [DoubleCategory] then holds
   automatically, and the fields demanding a witness (vertical and
   horizontal pasting, the globular associator and unitors) are exactly
   the associativity and unit laws of [C].

   This instance is the class's reuse audit: it exercises every field of
   [DoubleCategory] in the degenerate proof-irrelevant regime, dually to
   Construction/Cospan/Double.v where squares are genuinely
   proof-relevant. 

   --------
   * * 可交换平方的双范畴

   nLab: https://ncatlab.org/nlab/show/double+category（示例）

   对于任意范畴 [C] ，存在一个双范畴 [Sq C] ，其对象是 [C] 的对象，其垂直和水平的 1-胞都是 [C] 的态射，并且其平方

   a --h--> b
   |        |
   u        v
   v        v
   c --k--> d

   是该平方可交换的证明：[dsq h u v k := k ∘ u ≈ v ∘ h]。一个平方只是一个命题（同源集合关系中的成员），因此我们给它配备 TRIVIAL 的集合体来识别所有成员；[DoubleCategory] 的每个相容场便自动成立，而那些需要证据的字段（垂直和水平粘合、球形结合子和单位子）正是 [C] 的结合律和单位律。这个实例是该类的重用审计：它在退化的证明无关的环境中使用了 [DoubleCategory] 的每个字段，与 Construction/Cospan/Double.v 中正真证明相关的方格形成对偶。
*)

(*
 The trivial setoid on a type: all inhabitants are identified.  For
 [Sq C] the carrier is always a commuting-square proposition, so this
 is honest proof-irrelevance rather than information loss.  Kept local:
 applied to a data-carrying type it would silently identify everything,
 so it must not leak into the library interface. 

 --------
 类型上的平凡等价集：所有元素都被视为相同。对于 [Sq C]，其承载者总是一个交换方格命题，因此这是诚实的证明不可区分性，而不是信息丢失。保持本地性：应用于携带数据的类型时，它会悄无声息地将所有东西视为相同，因此不能泄露到库接口中。
*)
#[local] Program Definition trivial_setoid (A : Type) : Setoid A := {|
  equiv := fun _ _ => True
|}.

Local Obligation Tactic := simpl; intros; repeat intro; try exact I.

Program Definition Sq (C : Category) : DoubleCategory := {|
  dcat := C;
  dhor := fun a b => a ~{C}~> b;
  dsq := fun a b c d h u v k => k ∘ u ≈ v ∘ h;
  dsq_setoid := fun a b c d h u v k => trivial_setoid _;
  dhid := fun a => id[a];
  dhcomp := fun a b c g f => g ∘ f
|}.
Next Obligation.
  (*
 dsq_coerce : k ∘ u' ≈ v' ∘ h from k ∘ u ≈ v ∘ h along u ≈ u', v ≈ v' 

 --------
 dsq_coerce：从 k ∘ u ≈ v ∘ h 沿着 u ≈ u'，v ≈ v' 推出 k ∘ u' ≈ v' ∘ h
*)
  now rewrite <- eu, <- ev.
Qed.
Next Obligation.
  (* dsq_vid : h ∘ id ≈ id ∘ h / dsq_vid : h ∘ id ≈ id ∘ h *)
  cat.
Qed.
Next Obligation.
  (*
 dsq_vcomp : l ∘ (u' ∘ u) ≈ (v' ∘ v) ∘ h 

 --------
 dsq_vcomp ： l ∘ (u' ∘ u) ≈ (v' ∘ v) ∘ h
*)
  rewrite comp_assoc, X0, <- comp_assoc, X, comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  (* dsq_hcomp : (k' ∘ k) ∘ u ≈ w ∘ (h' ∘ h) / dsq_hcomp ：(k' ∘ k) ∘ u ≈ w ∘ (h' ∘ h) *)
  rewrite <- comp_assoc, X, comp_assoc, X0, <- comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  (* dassoc : the globular associator is associativity of C / dassoc：球状结合子是 C 的结合性 *)
  unshelve eexists.
  { rewrite id_right, id_left.
    symmetry; apply comp_assoc. }
  unshelve eexists.
  { rewrite id_right, id_left.
    apply comp_assoc. }
  split; exact I.
Qed.
Next Obligation.
  (*
 dunit_left : the globular left unitor is id_left of C 

 --------
 dunit_left：球状左单位子是 C 的 id_left
*)
  unshelve eexists.
  { cat. }
  unshelve eexists.
  { cat. }
  split; exact I.
Qed.
Next Obligation.
  (*
 dunit_right : the globular right unitor is id_right of C 

 --------
 dunit_right：球状右单位子是 C 的 id_right
*)
  unshelve eexists.
  { cat. }
  unshelve eexists.
  { cat. }
  split; exact I.
Qed.

(*
   * ** The coercion/composition interchange mixin holds trivially

   Squares of [Sq C] are propositions under the trivial setoid, so both
   interchange fields of [DoubleCoerceComp] are immediate.  This makes the
   companion/conjoint uniqueness theorems of
   Theory/DoubleCategory/Companion.v available at [Sq C]. 

   --------
   * ** 强制/组合交换混入是显然成立的

   [Sq C] 的平方在平凡等价类下是命题，因此 [DoubleCoerceComp] 的两个交换字段都是直接的。这使得 Theory/DoubleCategory/Companion.v 的伴随/共伴随唯一性定理在 [Sq C] 可用。
*)

Definition Sq_DoubleCoerceComp (C : Category) : DoubleCoerceComp (Sq C).
Proof. construct; exact I. Defined.

(*
   * ** Companions: every vertical morphism is its own companion

   The companion of a vertical morphism [u : a ~> b] is [u] ITSELF viewed
   as a horizontal 1-cell.  The binding squares are the trivially
   commuting squares [u ∘ id ≈ u ∘ id] and [id ∘ u ≈ id ∘ u], and both
   zigzag identities hold automatically since any two squares with the
   same boundary are equal. 

   --------
   * ** 伴随：每个垂直态射都是它自己的伴随

   一个垂直态射 [u : a ~> b] 的伴随就是将 [u] 自身视为水平 1-胞。约束方格是平凡可交换的方格 [u ∘ id ≈ u ∘ id] 和 [id ∘ u ≈ id ∘ u]，并且两条之字形恒等式自动成立，因为任何两个具有相同边界的方格都是相等的。
*)

Program Definition Sq_companion {C : Category} {a b : C}
  (u : a ~{C}~> b) : Companion (D:=Sq C) u := {|
  comp_hor := u
|}.
Next Obligation.
  (* comp_unit : u ∘ id ≈ u ∘ id / comp_unit : u ∘ id ≈ u ∘ id *)
  reflexivity.
Qed.
Next Obligation.
  (* comp_counit : id ∘ u ≈ id ∘ u / comp_counit : id ∘ u ≈ id ∘ u *)
  reflexivity.
Qed.

(*
   * ** Conjoints: exactly the isomorphisms

   AUDIT NOTE.  In [Sq C] a conjoint of [u : a ~> b] is a two-sided
   inverse of [u]: unwinding the binding squares at this model,
   [conj_unit] reads [conj_hor ∘ u ≈ id ∘ id] and [conj_counit] reads
   [id ∘ id ≈ u ∘ conj_hor].  A general morphism therefore has no conjoint
   here — in the quintet double category of a 1-category, conjoints are
   right adjoints, and an adjoint between locally discrete hom-categories
   is an inverse.  Accordingly [Sq_conjoint] is delivered at an
   isomorphism (the conjoint of [to u] is [from u]), and the necessity is
   recorded by [Sq_conjoint_iso]: any conjoint of [u] in [Sq C] makes [u]
   invertible.  Conjoints of arbitrary morphisms live instead in the
   transposed model whose horizontal 1-cells are the morphisms of
   [C^op]. 

   --------
   * ** 共轭算子：恰好是同构

   审计注释。在  [Sq C] 中，[u : a ~> b] 的共轭算子是 [u] 的双边逆元：在这个模型中展开绑定平方，[conj_unit] 等于 [conj_hor ∘ u ≈ id ∘ id]，[conj_counit] 等于 [id ∘ id ≈ u ∘ conj_hor]。因此，一般的态射在这里没有共轭算子——在一个 1-范畴的五重双范畴中，共轭算子是右伴随，而局部离散的 Hom-范畴之间的伴随是逆元。因此 [Sq_conjoint] 给出的就是一个同构（[to u] 的共轭算子是 [from u]），其必要性由 [Sq_conjoint_iso] 记录：[Sq C] 中 [u] 的任意共轭算子都使 [u] 可逆。任意态射的共轭算子则存在于换位模型中，在该模型中水平 1-胞为 [C^op] 的态射。
*)

Program Definition Sq_conjoint {C : Category} {a b : C}
  (u : a ≅ b) : Conjoint (D:=Sq C) (to u) := {|
  conj_hor := from u
|}.
Next Obligation.
  (* conj_unit : from u ∘ to u ≈ id ∘ id / conj_unit ：从 u ∘ 到 u ≈ id ∘ id *)
  rewrite iso_from_to; cat.
Qed.
Next Obligation.
  (* conj_counit : id ∘ id ≈ to u ∘ from u / conj_counit : id ∘ id ≈ to u ∘ from u *)
  rewrite iso_to_from; cat.
Qed.

(*
 Necessity: a conjoint of [u] in [Sq C] is a two-sided inverse of [u],
 so only isomorphisms have conjoints in this model. 

 --------
 必要性：在 [Sq C] 中，[u] 的伴随是 [u] 的双边逆元，所以在这个模型中，只有同构才有伴随。
*)
Program Definition Sq_conjoint_iso {C : Category} {a b : C}
  (u : a ~{C}~> b) (P : Conjoint (D:=Sq C) u) : a ≅ b := {|
  to := u;
  from := conj_hor P
|}.
Next Obligation.
  (* iso_to_from : u ∘ conj_hor P ≈ id / iso_to_from : u ∘ conj_hor P ≈ id *)
  pose proof (conj_counit P) as Hc; simpl in Hc.
  rewrite <- Hc; cat.
Qed.
Next Obligation.
  (* iso_from_to : conj_hor P ∘ u ≈ id / iso_from_to : conj_hor P ∘ u ≈ id *)
  pose proof (conj_unit P) as Hu; simpl in Hu.
  rewrite Hu; cat.
Qed.
