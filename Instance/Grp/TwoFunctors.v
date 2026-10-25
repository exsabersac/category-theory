Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Twist.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(* * * Two functors with the same object function, over groups / * * 两个具有相同对象函数的函子，作用于群 *)

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, Section I.3 ("Functors"), printed p. 15
 nLab: https://ncatlab.org/nlab/show/functor
 nLab: https://ncatlab.org/nlab/show/inner+automorphism

 Mac Lane closes Section I.3 by asking the reader to find two DIFFERENT
 functors whose object function is the identity, the point being that a
 functor is not determined by what it does to objects.  This file builds
 that pair over groups, together with the two facts that say why the
 obvious candidates do not work.

 WHAT IS BUILT.

 - [Grp_conj]: conjugation a ↦ t * a * t⁻¹ by an element t of a group,
 as a morphism of [Grp] (Instance/Grp.v), and [Grp_conj_iso]
 exhibiting it as an isomorphism with inverse the conjugation by
 t⁻¹.  These are the inner automorphisms.

 - [S3]: the symmetric group on three letters, presented as the
 semidirect product of a rotation of order three by a reflection of
 order two, over a carrier with decidable equality.  Its setoid IS
 propositional equality -- literally, not merely extensionally: the
 two relations are CONVERTIBLE, so [S3_equiv_is_eq] and
 [S3_eq_is_equiv] below are each the identity coercion, and calling
 them a record "in both directions" inflates them (an audit said so
 and was right; the underlying fact is stronger than the pair of
 lemmas suggests).  So a computation refuting an equation of carrier
 elements is a statement about the hom-setoid of [Grp], not about
 how a term happens to be written.  [S3] is
 nonabelian ([S3_nonabelian]), which is exactly what the witness
 needs.

 - [GrpAt G]: the one-object category whose only object is G and whose
 morphisms are the endomorphisms of G in [Grp].  Its inclusion
 [GrpAt_Incl] into [Grp] is full ([GrpAt_Incl_Full]), faithful
 ([GrpAt_Incl_Faithful]) and injective on objects
 ([GrpAt_Incl_injective_on_objects]), so [GrpAt G] presents the full
 subcategory of [Grp] on the single object G.

 - The pair: [Id] and [S3_Twist], both endofunctors of [GrpAt S3] with
 the identity object function ([S3_Twist_fobj]), differing on the
 concrete morphism [S3_conj_r] at the concrete element
 [S3_s] ([S3_twist_differs_on_conj_r]), hence distinct in the strict
 functor setoid ([S3_two_functors_distinct]) while identified by the
 weak one ([S3_two_functors_weakly_equal]).

 WHY THE TWIST IS NOT DEGENERATE.  [S3_Twist] is [Twist] (Functor/Twist.v)
 of the identity functor by conjugation with the reflection [S3_s].  Two
 ways for such a witness to collapse are ruled out here by proof rather
 than by assertion.  First, conjugation in an ABELIAN group is the
 identity automorphism ([Grp_conj_abelian]), so a conjugation twist over
 an abelian group proves nothing; the in-tree abelian witness Z/2
 (Instance/Grp.v) is shown to collapse in exactly that way
 ([Z2_conj_trivial]).  Second, and more generally, a twist by a NATURAL
 family collapses ([Twist_natural_strict_id]); the canonical
 group-theoretic family, inversion viewed as the isomorphism from a
 group to its opposite (Instance/Grp.v), is natural, and its
 twist is therefore an endofunctor of the whole of [Grp] with the
 identity object function that is strictly EQUAL to [Id]
 ([Grp_op_twist_is_Id]).  The conjugation family on [GrpAt S3] escapes
 both: S3 is nonabelian, and the family is not natural at the inner
 automorphism by the rotation ([S3_conj_not_central]), which is exactly
 the datum [S3_two_functors_distinct] consumes.

 SCOPE, STATED PLAINLY.  Mac Lane's exercise is posed for the whole
 category of groups.  What is constructed here is the same twist over
 the full subcategory of [Grp] on the single object S3, where the family
 is one honest inner automorphism, plus the two collapse theorems above
 which show what goes wrong with the uniform candidates.  The companion
 witness in Construction/Free/TwoFunctors.v (Fong and Spivak's Exercise
 3.40) needs no groups at all.

 WHAT EXACTLY IS MISSING, and it is one principle rather than a vague
 appeal to choice.  An audit of the first commit built the [Grp]-wide
 pair using nothing from this file except [Twist], [Twist_not_strict_id],
 [uip_of_dec] and [Grp_conj_iso], adding only a decision procedure for
 equality of [GrpObject]s: with one in hand, the family that conjugates
 at S3 and is the identity elsewhere is definable, and the resulting
 endofunctor of [Grp] has the identity object function, is equal to [Id]
 in [Cat] and distinct from it in [StrictCat].  Reading the axioms off
 that construction gives exactly two, [classic] and
 [constructive_indefinite_description] -- so the barrier really is a
 choice principle, as the informal story says, and this library is
 axiom-free (docs/AXIOMS.md).

 The machinery in Functor/Twist.v is therefore exactly one principle
 short of the exercise as posed, and that principle is the object
 discriminator, not anything about twists.

 AND THE OBSTRUCTION CANNOT BE UPGRADED TO A THEOREM, which is worth
 saying because the reflex elsewhere in this development is to convert
 "we could not" into "it cannot" by counterexample.  Here that move is
 unavailable: since the separating endofunctor exists in every model of
 Rocq extended by classical epsilon, the statement "every endofunctor of
 [Grp] with the identity object function is strictly [Id]" is NOT
 provable in Rocq, modulo the relative consistency of that extension.
 So nothing is claimed to exist or not to exist here, and nothing can be.

 A CONSEQUENCE OF THE SAME PRINCIPLE, not a second obstacle.  The first
 commit recorded separately that the object component of a
 [Functor_StrictEq_Setoid] witness is an ARBITRARY proof of [F x = G x] --
 for functors sharing the identity object function, a loop [G = G] in
 [GrpObject] -- so that refuting strict equality means refuting every
 such loop rather than only [eq_refl].  That is accurate, but it is not
 an independent barrier: the same decision procedure that supplies the
 discriminator collapses every loop through Hedberg, via this
 development's own [uip_of_dec] in Functor/Twist.v.  The witnesses below
 sidestep it because their object types have decidable equality.

 STRICT VERSUS WEAK.  The distinctness is stated in
 [Functor_StrictEq_Setoid] (Theory/Functor.v), the hom-setoid of
 [StrictCat] (Instance/StrictCat.v).  It could not be stated in
 [Functor_Setoid] (Theory/Functor.v), the hom-setoid of [Cat]
 (Instance/Cat.v), because that setoid identifies naturally
 isomorphic functors and [S3_Twist] IS naturally isomorphic to [Id] --
 [S3_two_functors_weakly_equal] proves it, the natural isomorphism being
 the conjugation itself.  So the two functors are EQUAL as morphisms of
 [Cat] and DIFFERENT as morphisms of [StrictCat]; that is the reading
 under which Mac Lane's question has content in this library. 

 --------
 书籍：Mac Lane，《Categories for the Working Mathematician》，第2版，Springer GTM 5, 1998，第I.3节（"函子"），印刷页15
 nLab: https://ncatlab.org/nlab/show/functor
 nLab: https://ncatlab.org/nlab/show/inner+automorphism

 Mac Lane在第I.3节的结尾要求读者找到两个不同的函子，它们的对象函数是恒等函数，其目的在于说明一个函子并不由它对对象的作用决定。本文件在群上构建了这一对函子，同时说明了两个事实，解释了为什么那些显而易见的候选不行。

 构建内容。

 - [Grp_conj]：由群元素t作用的共轭a ↦ t * a * t⁻¹，作为[Grp]的态射（Instance/Grp.v），以及[Grp_conj_iso]显示它是一个同构，其逆为由t⁻¹作用的共轭。这些是内自同构。- [S3]：三个字母上的对称群，表示为三阶旋转与二阶反射的半直积，作用在具有可判等性的载体上。它的集合类型是命题等式——字面意义上的，而不仅仅是扩展意义上的：这两个关系是可互换的，所以下面的 [S3_equiv_is_eq] 和 [S3_eq_is_equiv] 各自都是恒等强制类型，并且称它们为“两个方向上的记录”会使它们膨胀（一次审计显示如此，且确实正确；其潜在事实比这对引理所指出的更强）。因此，针对载体元素的一条方程式的计算反证，是关于 [Grp] 的同态集合类型的陈述，而不是关于一个项如何书写的。[S3] 是非交换的（[S3_nonabelian]），这正是证据所需要的。- [GrpAt G]：一个单对象范畴，其唯一对象是 G，且其态射是 [Grp] 中 G 的自态射。其包含函数 [GrpAt_Incl] 到 [Grp] 是满的（[GrpAt_Incl_Full]）、忠实的（[GrpAt_Incl_Faithful]）并且在对象上是单射的（[GrpAt_Incl_injective_on_objects]），因此 [GrpAt G] 展示了 [Grp] 中关于唯一对象 G 的满子范畴。

 - 这对：[Id] 和 [S3_Twist]，都是 [GrpAt S3] 的自函子，具有恒等对象函数（[S3_Twist_fobj]），在具体元素 [S3_s] 上的具体态射 [S3_conj_r] 上有所不同（[S3_twist_differs_on_conj_r]），因此在严格函子集合等价类中（[S3_two_functors_distinct]）是不同的，但在弱等价类中（[S3_two_functors_weakly_equal]）被认同。为什么扭结不是退化的。[S3_Twist] 是 [Twist]（Functor/Twist.v）通过与反射 [S3_s] 结合的共轭作用的恒等函子。这里通过证明而不是断言，排除了这种证据崩溃的两种方式。首先，阿贝尔群中的共轭作用是恒等自同构（[Grp_conj_abelian]），因此在阿贝尔群上的共轭扭结没有任何意义；树内的阿贝尔证据 Z/2（Instance/Grp.v）正是以这种方式被证明崩溃（[Z2_conj_trivial]）。其次，更一般而言，由一个自然族引起的扭曲会崩塌（[Twist_natural_strict_id]）；典型的群论族，将反演视为从一个群到其对偶群的同构（Instance/Grp.v），是自然的，因此其扭曲是整个[Grp]的一个自函子，其恒等对象函数严格等于[Id]（[Grp_op_twist_is_Id]）。[GrpAt S3]上的共轭族则两者都不满足：S3是非阿贝尔的，并且该族在由旋转产生的内自同构处不是自然的（[S3_conj_not_central]），这正是[S3_two_functors_distinct]所使用的数据。范围，明确说明。Mac Lane 的练习是针对整个群的范畴提出的。这里构造的是同一个扭结，但在 [Grp] 的单对象 S3 的全子范畴上，其中该族是一个真实的内自同构，加上上面两个塌缩定理，它们展示了统一候选对象出了什么问题。在 Construction/Free/TwoFunctors.v（Fong 和 Spivak 的练习 3.40）中的伴随证据则完全不需要群。到底缺少的是什么，它是一个原则，而不是对选择的模糊呼吁。对第一次提交的审计使用了这个文件中除了 [Twist]、[Twist_not_strict_id]、[uip_of_dec] 和 [Grp_conj_iso] 之外的任何内容都没有，用这些构建了 [Grp] 广义配对，只增加了 [GrpObject] 相等的判定程序：有了这个程序，就可以定义在 S3 上共轭而在其他地方是恒等的族，并且所得的 [Grp] 的自函子具有恒等对象函数，在 [Cat] 中等于 [Id]，而在 [StrictCat] 中与之不同。从该构造中读出公理正好有两个，[classic] 和 [constructive_indefinite_description]——所以障碍确实是一个选择原则，正如非正式故事所说，而这个库是无公理的 (docs/AXIOMS.md)。因此，Functor/Twist.v 中的机制正好比所提出的练习少了一个原则，而这个原则是对象判别器，而不是关于扭结的任何东西。

 而且这个障碍无法提升为定理，这一点值得说明，因为在本开发的其他地方的做法是通过反例将“我们不能”转换为“它不能”。在这里，这种做法不可行：由于在每个通过经典 ε 扩展的 Roq 模型中都存在分离自函子，所以命题“[Grp] 的每个具有恒等对象函数的自函子都是严格 [Id]”在 Roq 中不可证明，前提是该扩展的相对一致性。因此，此处没有声称存在或不存在任何东西，也没有任何东西可以声称。同一原理的一个结果，而不是第二个障碍。第一次提交单独记录了 [Functor_StrictEq_Setoid] 证据的对象组成部分是 [F x = G x] 的任意证明——对于共享恒等对象函数的函子，在 [GrpObject] 中的 [G = G] 循环——因此，反驳严格相等意味着反驳每个这样的循环，而不仅仅是 [eq_refl]。这是准确的，但它不是独立的障碍：提供判别器的同一决策过程通过 Hedberg 折叠每个循环，依赖于本开发中的 Functor/Twist.v 中 [uip_of_dec]。下面的证据规避了它，因为它们的对象类型具有可判定的相等性。严格与弱。其区别在 [Functor_StrictEq_Setoid]（Theory/Functor.v）、[StrictCat]（Instance/StrictCat.v）的同态集合体中有所说明。在 [Functor_Setoid]（Theory/Functor.v）、[Cat]（Instance/Cat.v）的同态集合体中无法说明，因为该集合体会将自然同构的函子视为相同，而 [S3_Twist] 与 [Id] 是自然同构的 —— [S3_two_functors_weakly_equal] 证明了这一点，自然同构就是共轭作用本身。因此，这两个函子作为 [Cat] 的态射是相等的，但作为 [StrictCat] 的态射是不同的；这就是在该库中理解 Mac Lane 问题的方式。
*)

#[local] Obligation Tactic := idtac.

(** ** Inner automorphisms / ** 内自同构 *)

(*
 Conjugation by t is a group homomorphism: t(ab)t⁻¹ collapses to
 (tat⁻¹)(tbt⁻¹) once the inner t⁻¹t is cancelled. 

 --------
 通过 t 的共轭是一个群同态：t(ab)t⁻¹ 在内部 t⁻¹t 被消去后变为 (tat⁻¹)(tbt⁻¹)。
*)
Definition Grp_conj (G : GrpObject) (t : carrier G) : G ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom G G
       {| morphism := fun a => grp_mul G (grp_mul G t a) (grp_inv G t) |} _ _).
  - intros a b Hab.
    now rewrite Hab.
  - simpl.
    rewrite grp_mul_unit_r.
    apply grp_mul_inv_r.
  - intros a b; simpl.
    rewrite (grp_mul_assoc G (grp_mul G t a) (grp_inv G t)
               (grp_mul G (grp_mul G t b) (grp_inv G t))).
    rewrite <- (grp_mul_assoc G (grp_inv G t) (grp_mul G t b) (grp_inv G t)).
    rewrite <- (grp_mul_assoc G (grp_inv G t) t b).
    rewrite grp_mul_inv_l.
    rewrite grp_mul_unit_l.
    rewrite <- (grp_mul_assoc G (grp_mul G t a) b (grp_inv G t)).
    rewrite (grp_mul_assoc G t a b).
    reflexivity.
Defined.

(* Conjugation by t and by t⁻¹ are mutually inverse, so conjugation is an automorphism -- an INNER automorphism of G. / 由 t 和 t⁻¹ 的共轭是互为逆的，因此共轭是一个自同构——G 的一个内自同构。 *)
Definition Grp_conj_iso (G : GrpObject) (t : carrier G) :
  @Isomorphism Grp G G.
Proof.
  unshelve notypeclasses refine
    (@Build_Isomorphism Grp G G (Grp_conj G t) (Grp_conj G (grp_inv G t)) _ _).
  - intro a; simpl.
    unfold Basics.compose; simpl.
    rewrite grp_inv_inv.
    rewrite <- (grp_mul_assoc G t (grp_mul G (grp_inv G t) a) t).
    rewrite <- (grp_mul_assoc G t (grp_inv G t) a).
    rewrite grp_mul_inv_r.
    rewrite grp_mul_unit_l.
    rewrite grp_mul_assoc.
    rewrite grp_mul_inv_r.
    apply grp_mul_unit_r.
  - intro a; simpl.
    unfold Basics.compose; simpl.
    rewrite grp_inv_inv.
    rewrite <- (grp_mul_assoc G (grp_inv G t) (grp_mul G t a) (grp_inv G t)).
    rewrite <- (grp_mul_assoc G (grp_inv G t) t a).
    rewrite grp_mul_inv_l.
    rewrite grp_mul_unit_l.
    rewrite grp_mul_assoc.
    rewrite grp_mul_inv_l.
    apply grp_mul_unit_r.
Defined.

(*
 THE DEGENERACY CHECK, PROVED.  Over an abelian group every conjugation
 is the identity morphism, so a twist by an inner automorphism there is
 the identity functor and separates nothing. 

 --------
 退化性检查，已证明。在阿贝尔群上，每个共轭都是恒等态射，所以通过内自同构的扭曲在这里是恒等函子，并且什么也不分离。
*)
Lemma Grp_conj_abelian (G : GrpObject)
  (comm : ∀ a b : carrier G, grp_mul G a b ≈ grp_mul G b a)
  (t : carrier G) : Grp_conj G t ≈ @id Grp G.
Proof.
  intro a; simpl.
  rewrite (comm t a).
  rewrite grp_mul_assoc.
  rewrite grp_mul_inv_r.
  apply grp_mul_unit_r.
Qed.

(* The in-tree abelian witness is Z/2, and it does collapse. / 树内的阿贝尔见证是 Z/2，并且它确实会坍塌。 *)
Example Z2_conj_trivial (t : carrier Z2) : Grp_conj Z2 t ≈ @id Grp Z2.
Proof.
  apply Grp_conj_abelian.
  intros a b; simpl.
  now destruct a, b.
Qed.

(* * ** The symmetric group on three letters / * ** 三个字母的对称群 *)

(* Z/3, written additively, as the rotation part. / Z/3，按加法方式书写，作为旋转部分。 *)
Inductive rot : Type := rot0 | rot1 | rot2.

Definition rot_add (a b : rot) : rot :=
  match a, b with
  | rot0, rot0 => rot0 | rot0, rot1 => rot1 | rot0, rot2 => rot2
  | rot1, rot0 => rot1 | rot1, rot1 => rot2 | rot1, rot2 => rot0
  | rot2, rot0 => rot2 | rot2, rot1 => rot0 | rot2, rot2 => rot1
  end.

Definition rot_neg (a : rot) : rot :=
  match a with rot0 => rot0 | rot1 => rot2 | rot2 => rot1 end.

(*
 An element of S3 is a pair (i, b): the rotation r^i followed by the
 reflection s^b.  Multiplication is the semidirect product rule
 r^i s^b · r^j s^c = r^(i ± j) s^(b+c), the sign being negative exactly
 when b is the reflection -- this is s r s⁻¹ = r⁻¹. 

 --------
 S3 的一个元素是一个二元组 (i, b)：先旋转 r^i，然后反射 s^b。乘法遵循半直积规则 r^i s^b · r^j s^c = r^(i ± j) s^(b+c)，当 b 是反射时符号为负——这就是 s r s⁻¹ = r⁻¹。
*)
Definition S3carrier : Type := (rot * bool)%type.

Definition s3_mul (p q : S3carrier) : S3carrier :=
  (rot_add (fst p) (if snd p then rot_neg (fst q) else fst q),
   xorb (snd p) (snd q)).

Definition s3_inv (p : S3carrier) : S3carrier :=
  if snd p then p else (rot_neg (fst p), false).

Definition s3_unit : S3carrier := (rot0, false).

Program Definition s3_setoid : Setoid S3carrier := {| equiv := @eq S3carrier |}.

(* Every law is a finite check: associativity is 216 cases, the unit and inverse laws 6 each. / 每条定律都是一个有限的检查：结合律有216种情况，单位元和逆元定律各有6种情况。 *)
Definition S3 : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := S3carrier ; is_setoid := s3_setoid |};
    grp_unit := s3_unit;
    grp_mul  := s3_mul;
    grp_inv  := s3_inv;
    (* [s3_setoid]'s `≈` is [@eq S3carrier], already a [Prop]. / [s3_setoid] 的 `≈` 是 [@eq S3carrier]，已经是 [Prop]。 *)
    grp_prop := eq_PropEquiv S3carrier
  |}.
  - intros x y Hxy u v Huv; simpl in *; subst; reflexivity.
  - intros [i b] [j c] [k d]; destruct i, j, k, b, c, d; reflexivity.
  - intros [j c]; destruct j, c; reflexivity.
  - intros [j c]; destruct j, c; reflexivity.
Defined.

(*
 The setoid of S3 IS propositional equality, in both directions.  This is
 what licenses closing the distinctness arguments below by [discriminate]
 on carrier elements: the refuted statement is the hom-setoid equation
 itself. 

 --------
 S3 的集合等式在两个方向上都是命题等式。这就是允许通过载体元素上的 [discriminate] 来结束下面不同性论证的原因：被反驳的陈述本身就是同态集合等式。
*)
Example S3_equiv_is_eq (a b : carrier S3) (H : a ≈ b) : a = b := H.
Example S3_eq_is_equiv (a b : carrier S3) (H : a = b) : a ≈ b := H.

(* The rotation and the reflection. / 旋转和反射。 *)
Definition S3_r : carrier S3 := (rot1, false).
Definition S3_s : carrier S3 := (rot0, true).

(* S3 is nonabelian: r * s and s * r are different reflections. / S3 是非交换的：r * s 和 s * r 是不同的反射。 *)
Lemma S3_nonabelian :
  grp_mul S3 S3_r S3_s ≈ grp_mul S3 S3_s S3_r → False.
Proof. simpl; discriminate. Qed.

(*
 Consequently conjugation by the reflection is not the identity: it
 inverts the rotation. 

 --------
 因此，通过反射的共轭不是恒等变换：它会反转旋转。
*)
Lemma S3_conj_s_nontrivial : Grp_conj S3 S3_s ≈ @id Grp S3 → False.
Proof.
  intro H.
  pose proof (H S3_r) as Hr.
  simpl in Hr.
  discriminate.
Qed.

(* * ** The full subcategory of Grp on a single group / * ** 在单一群上的群的完整子范畴 *)

(*
 One object, whose endomorphism monoid in [Grp] supplies the morphisms;
 the category laws are those of [Grp] at the object G. 

 --------
 一个对象，其在 [Grp] 中的自同态幺半群提供了态射；该范畴的范畴法则是在对象 G 处的 [Grp] 的法则。
*)
Program Definition GrpAt (G : GrpObject) : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => G ~{Grp}~> G;
  homset  := fun _ _ => @homset Grp G G;
  id      := fun _ => @id Grp G;
  compose := fun _ _ _ f g => f ∘ g
|}.
(*
 [compose_respects] is discharged by typeclass resolution from [Grp]'s own
 instance; the four remaining obligations are the category laws, which are
 [Grp]'s laws at the object G. 

 --------
 [compose_respects] 由类型类解析从 [Grp] 自身的实例中解脱；剩下的四个义务是范畴律，它们是 [Grp] 在对象 G 上的律。
*)
Next Obligation.
  intros G x y f.
  apply id_left.
Qed.
Next Obligation.
  intros G x y f.
  apply id_right.
Qed.
Next Obligation.
  intros G x y z w f g h.
  apply comp_assoc.
Qed.
Next Obligation.
  intros G x y z w f g h.
  apply comp_assoc_sym.
Qed.

(* The inclusion into [Grp]. / 纳入 [Grp]。 *)
Program Definition GrpAt_Incl (G : GrpObject) : GrpAt G ⟶ Grp := {|
  fobj := fun _ => G;
  fmap := fun _ _ f => f
|}.
Next Obligation.
  intros G x y f g Hfg.
  exact Hfg.
Qed.
Next Obligation.
  intros G x.
  reflexivity.
Qed.
Next Obligation.
  intros G x y z f g.
  reflexivity.
Qed.

#[export] Program Instance GrpAt_Incl_Full (G : GrpObject) :
  Full (GrpAt_Incl G) := {|
  prefmap := fun _ _ g => g
|}.
Next Obligation.
  intros G x y g.
  reflexivity.
Qed.

#[export] Program Instance GrpAt_Incl_Faithful (G : GrpObject) :
  Faithful (GrpAt_Incl G).
Next Obligation.
  intros G x y f g Hfg.
  exact Hfg.
Qed.

(*
 The object map is injective, so [GrpAt G] is a subcategory of [Grp] in
 the strict sense of the word and not merely a category mapping into it.
 NOTE HOW LITTLE THIS COSTS, since an audit rightly asked: the object
 type of [GrpAt G] is [poly_unit], so any two objects are equal and the
 injectivity hypothesis is discarded outright; fullness and faithfulness
 are definitional too, the hom-type being [Grp]'s own on the nose.  All
 three are worth stating -- they are what "full subcategory" means, and
 this development has been strict about the word -- but none of the
 three has content.  What follows;
 with fullness and faithfulness above, it is the full subcategory on G. 

 --------
 对象映射是单射的，因此  [GrpAt G]  是  [Grp]  的子范畴，严格意义上如此，而不仅仅是映射到其中的一个范畴。
 注意这几乎不花什么代价，因为有一次审计正确地提出：[GrpAt G] 的对象类型是 [poly_unit]，所以任意两个对象都是相等的，单射的假设被直接舍弃；完全性和忠实性也是定义性的，因为同态类型正是 [Grp] 自身。三者都值得声明——它们就是“完全子范畴”的含义，而这一发展对词语使用非常严格——但三者本身没有实质内容。接下来；
 在上述完全性和忠实性下，它就是关于 G 的完全子范畴。
*)
Lemma GrpAt_Incl_injective_on_objects (G : GrpObject) (x y : GrpAt G) :
  fobj[GrpAt_Incl G] x = fobj[GrpAt_Incl G] y → x = y.
Proof.
  intros _.
  destruct x, y.
  reflexivity.
Qed.

(*
 An isomorphism of G with itself in [Grp] is one in [GrpAt G]: the
 morphisms, composition, identity and hom-setoids agree definitionally. 

 --------
 在  ZZ W0WZZ 中，G 与自身的同构是在  ZZ W1WZZ 中的：态射、复合、恒等和同态集合从定义上是一致的。
*)
Definition GrpAt_iso {G : GrpObject} (i : @Isomorphism Grp G G)
  (x : GrpAt G) : @Isomorphism (GrpAt G) x x :=
  @Build_Isomorphism (GrpAt G) x x (to i) (from i)
    (iso_to_from i) (iso_from_to i).

(*
 Uniqueness of identity proofs on the single object, by Hedberg from the
 (trivially) decidable equality of [poly_unit]. 

 --------
 由 Hedberg 提出的关于单个对象的身份证明的唯一性，基于 [poly_unit] 的（平凡地）可判定等式。
*)
Definition poly_unit_eq_dec (x y : poly_unit) : {x = y} + {x <> y} :=
  left (match x, y with ttt, ttt => eq_refl end).

(** ** The two functors / ** 这两个函子 *)

(*
 The twist of the identity functor of the full subcategory on S3 by
 conjugation with the reflection. 

 --------
 通过与反射的共轭，将S3上的全子范畴的恒等函子扭转。
*)
Definition S3_twist_family : ∀ x : GrpAt S3, x ≅ x :=
  GrpAt_iso (Grp_conj_iso S3 S3_s).

Definition S3_Twist : GrpAt S3 ⟶ GrpAt S3 :=
  Twist (@Id (GrpAt S3)) S3_twist_family.

(*
 Both functors have the identity object function, by computation.  The
 [=] here is on OBJECTS, where propositional equality is the right
 notion and the one [Functor_StrictEq_Setoid] itself uses; morphisms
 stay compared with ≈ throughout. 

 --------
 通过计算，两个函子都有恒等对象函数。这里的 [=] 是作用于对象的，其中命题等式是正确的概念，并且 [Functor_StrictEq_Setoid] 本身也使用它；态射在整个过程中与 ≈ 进行比较。
*)
Lemma S3_Twist_fobj (x : GrpAt S3) : fobj[S3_Twist] x = fobj[@Id (GrpAt S3)] x.
Proof. reflexivity. Qed.

(*
 Indeed the object functions agree as FUNCTIONS, not merely pointwise:
 both are [fun x => x] after unfolding. 

 --------
 确实，该对象的函数作为函数是相符的，而不仅仅是逐点相符：展开后两者都是 [fun x => x]。
*)
Example S3_Twist_object_function :
  fobj[S3_Twist] = fobj[@Id (GrpAt S3)].
Proof. reflexivity. Qed.

(*
 The separating morphism: the inner automorphism by the rotation, read as
 an endomorphism of the single object of [GrpAt S3].  The type ascription
 is what lets [fmap] find its source and target, since the hom-type of a
 one-object category does not mention them. 

 --------
 分离态射：由旋转引起的内自同构，被读作  [GrpAt S3] 单对象的一个自同态。类型赋值是让  [fmap] 找到其源和目标的原因，因为单对象范畴的 Hom 型并不提及它们。
*)
Definition S3_conj_r : ttt ~{GrpAt S3}~> ttt := Grp_conj S3 S3_r.

(*
 The concrete separating datum: at that morphism, the two functors take
 different values on the reflection. 

 --------
 混凝土分离基准：在那个态射上，这两个函子在反射上取不同的值。
*)
Example S3_twist_value :
  grp_map (fmap[S3_Twist] S3_conj_r) S3_s ≈ (rot1, true).
Proof. reflexivity. Qed.

Example S3_id_value :
  grp_map (fmap[@Id (GrpAt S3)] S3_conj_r) S3_s ≈ (rot2, true).
Proof. reflexivity. Qed.

(*
 Hence the two arrow maps differ IN THE HOM-SETOID of [GrpAt S3], which
 is the hom-setoid of [Grp] at S3: two homomorphisms are equivalent there
 exactly when they agree at every element, and these disagree at [S3_s]. 

 --------
 因此，这两个箭头映射在  [GrpAt S3] 的同值集（hom-setoid）中是不同的，该同值集是 [Grp] 在 S3 的同值集：两个同态在那里当且仅当它们在每个元素上都相同时才等价，而它们在 [S3_s] 上不相同。
*)
Theorem S3_twist_differs_on_conj_r :
  fmap[S3_Twist] S3_conj_r
    ≈ fmap[@Id (GrpAt S3)] S3_conj_r → False.
Proof.
  intro H.
  pose proof (H S3_s) as Hs.
  simpl in Hs.
  discriminate.
Qed.

(*
 The naturality that breaks down: conjugation by the reflection does not
 commute with conjugation by the rotation, since S3 is nonabelian.  This
 is the single datum the separation rests on. 

 --------
 分解的自然性：通过反射的共轭与通过旋转的共轭不交换，因为 S3 是非阿贝尔群。这是分离所依赖的唯一数据。
*)
Lemma S3_conj_not_central :
  S3_twist_family ttt ∘ S3_conj_r
    ≈ fmap[@Id (GrpAt S3)] S3_conj_r ∘ S3_twist_family ttt → False.
Proof.
  intro H.
  pose proof (H S3_s) as Hs.
  simpl in Hs.
  discriminate.
Qed.

(*
 The two functors are distinct in the strict functor setoid.  The
 argument goes through the general criterion of Functor/Twist.v: a twist
 differs from the identity exactly where its family is not natural,
 the object components of a strict equality being collapsed to [eq_refl]
 by uniqueness of identity proofs on the single object. 

 --------
 在严格函子集合中，这两个函子是不同的。论证通过了 Functor/Twist.v 的一般准则：一个扭转恰好在其系列不自然的地方与恒等不同，严格等式的对象分量被单对象上的恒等性证明的唯一性塌缩为 [eq_refl]。
*)
Theorem S3_two_functors_distinct :
  @equiv _ Functor_StrictEq_Setoid S3_Twist (@Id (GrpAt S3)) → False.
Proof.
  unfold S3_Twist.
  exact (Twist_not_strict_id (@Id (GrpAt S3)) S3_twist_family
           (uip_of_dec poly_unit_eq_dec) (x:=ttt) (y:=ttt)
           (f:=S3_conj_r) S3_conj_not_central).
Qed.

(*
 And they are IDENTIFIED by the weak setoid, the hom-setoid of [Cat]:
 the conjugation family is itself the natural isomorphism.  This is why
 the statement above has to be made strictly. 

 --------
 它们由弱等价子集、[Cat] 的同态等价子集识别：共轭族本身就是自然同构。这就是为什么上面的陈述必须严格表达的原因。
*)
Theorem S3_two_functors_weakly_equal :
  @equiv _ Functor_Setoid S3_Twist (@Id (GrpAt S3)).
Proof. exact (Twist_Id_weak_equiv S3_twist_family). Qed.

(*
 The same two statements read off the two categories of categories: the
 pair is one and the same morphism of [Cat], and two different morphisms
 of [StrictCat].  The hom-setoids are the two functor setoids on the
 nose, as Test/Issue138.v records. 

 --------
 这两个相同的陈述可以从两类的类别中读取：这一对在  [Cat] 中是同一个态射，而在  [StrictCat] 中是两个不同的态射。Hom-集合是两个函子集合，准确无误，正如 Test/Issue138.v 所记录的那样。
*)
Example S3_pair_equal_in_Cat :
  @equiv _ (@homset Cat (GrpAt S3) (GrpAt S3)) S3_Twist (@Id (GrpAt S3)).
Proof. exact S3_two_functors_weakly_equal. Qed.

Theorem S3_pair_distinct_in_StrictCat :
  @equiv _ (@homset StrictCat (GrpAt S3) (GrpAt S3))
    S3_Twist (@Id (GrpAt S3)) → False.
Proof. exact S3_two_functors_distinct. Qed.

(* * ** The uniform candidate over all of Grp, and its collapse / * ** 所有组中均匀候选及其塌缩 *)

(*
 Inversion as an isomorphism from a group to its opposite
 (Instance/Grp.v); both round trips are [grp_inv_inv]. 

 --------
 作为从一个群到其对立群的同构的逆元（实例/Grp.v）；两个往返都是 [grp_inv_inv] 。
*)
Definition Grp_inv_iso (G : GrpObject) : @Isomorphism Grp G (Grp_Op G).
Proof.
  unshelve notypeclasses refine
    (@Build_Isomorphism Grp G (Grp_Op G) (Grp_inv_to G) (Grp_inv_from G) _ _).
  - intro a; simpl.
    unfold Basics.compose.
    apply grp_inv_inv.
  - intro a; simpl.
    unfold Basics.compose.
    apply grp_inv_inv.
Defined.

(*
 Twisting the opposite-group functor by inversion gives an endofunctor of
 the WHOLE of [Grp] whose object function is the identity -- the shape
 Mac Lane's exercise asks for. 

 --------
 通过取逆来扭转对立群函子，得到一个作用于整个 [Grp] 的自函子，其对象函数是恒等的——这正是 Mac Lane 练习所要求的形状。
*)
Definition Grp_op_twist : Grp ⟶ Grp := Twist Grp_Op Grp_inv_iso.

Lemma Grp_op_twist_fobj (G : Grp) : fobj[Grp_op_twist] G = G.
Proof. reflexivity. Qed.

Example Grp_op_twist_object_function : fobj[Grp_op_twist] = fobj[@Id Grp].
Proof. reflexivity. Qed.

(*
 But it is the identity functor, strictly: inversion is natural (that is
 [grp_map_inv], every homomorphism commutes with inversion), and a
 natural family produces nothing new ([Twist_natural_strict_id]).  So
 this candidate -- a family of isomorphisms available uniformly at every
 group, and the one the tree already builds as [Grp_op_Isomorphism]
 (Instance/Grp.v) -- does not answer the exercise, and the file does
 not pretend otherwise. 

 --------
 但严格来说，它是恒等函子：取逆是自然的（也就是说，[grp_map_inv]，每个同态都与取逆交换），而一个自然的族不会产生新的东西（[Twist_natural_strict_id]）。因此，这个候选——在每个群中都统一可用的一族同构，以及树已经构建的那个 [Grp_op_Isomorphism]（Instance/Grp.v）——并不能回答该练习，而且该文件也没有假装可以回答。
*)
Theorem Grp_op_twist_is_Id :
  @equiv _ Functor_StrictEq_Setoid Grp_op_twist (@Id Grp).
Proof.
  apply Twist_natural_strict_id.
  intros G H f a; simpl.
  unfold Basics.compose.
  symmetry.
  apply grp_map_inv.
Qed.
