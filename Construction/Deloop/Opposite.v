Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(* * ** The opposite monoid, and delooping against duality / * ** 对偶幺半群，以及针对对偶性的去循环 *)

(*
 Riehl, CTiC, Example 1.2.2(iii): the opposite of a delooping is the
 delooping of the opposite monoid.  This is the device by which a RIGHT
 action of M is presented as a LEFT action of M^op, and it is the reason
 the composition-order choice above is a choice rather than a convention:
 the other choice deloops M^op, and for non-commutative M those categories
 differ (Construction/Funny/Comparison.v's [ListMon] is a live example). 

 --------
 Riehl, CTiC, 示例 1.2.2(iii)：解循环的相反是对偶单的解循环。这是将 M 的右作用表示为 M^op 的左作用的方法，并且这也是上面组合顺序选择是一个选择而不是惯例的原因：另一个选择是解循环 M^op，对于非交换的 M，这些范畴是不同的（Construction/Funny/Comparison.v 的 [ListMon] 是一个实际例子）。
*)

Program Definition MonObject_op (M : MonObject) : MonObject := {|
  mon_setoid := mon_setoid M;
  mon_unit   := mon_unit;
  mon_op     := fun a b => mon_op b a;

  mon_op_respects := _;
  mon_op_assoc    := fun a b c => mon_op_assoc_sym M c b a;
  mon_op_unit_l   := fun a => mon_op_unit_r a;
  mon_op_unit_r   := fun a => mon_op_unit_l a
|}.
Next Obligation. now intros ?? H1 ?? H2; rewrite H1, H2. Qed.

(*
 The double opposite agrees with the original on all three DATA fields, by
 [eq_refl].  It is NOT [eq] to it: the two law fields come back as
 [mon_op_assoc_sym] applied twice and as the swapped unit laws, which are
 propositionally but not syntactically the originals, and [MonObject] has no
 proof irrelevance.  So this is weaker than Construction/Opposite.v's
 `C^op^op = C` by reflexivity, and the difference is exactly that the
 category laws there are packaged to be self-inverse while these are not. 

 --------
 双重对立在所有三个数据字段上与原始对象一致，由 [eq_refl] 定义。它不是 [eq]：两个律字段返回为 [mon_op_assoc_sym] 应用两次以及调换后的单位律，这在命题上与原始对象相同，但在语法上不同，并且 [MonObject] 没有证明无关性。因此，这比 Construction/Opposite.v 中的 `C^op^op = C` 弱一点，区别正是在那里的范畴律是封装为自逆的，而这些则不是。
*)
Example MonObject_op_op_carrier (M : MonObject) :
  carrier (MonObject_op (MonObject_op M)) = carrier M := eq_refl.
Example MonObject_op_op_unit (M : MonObject) :
  @mon_unit (MonObject_op (MonObject_op M)) = @mon_unit M := eq_refl.
Example MonObject_op_op_op (M : MonObject) :
  @mon_op (MonObject_op (MonObject_op M)) = @mon_op M := eq_refl.

(*
 And the two constructions commute definitionally: (B M)^op and B (M^op)
 have the same objects, the same hom-setoids, the same identity, and the
 same composition, so the comparison functors are identities on both. 

 --------
 这两个构造在定义上是可交换的： (B M)^op 和 B (M^op) 具有相同的对象、相同的 Hom-集族、相同的恒等和相同的复合，因此比较函子在两者上都是恒等的。
*)
Program Definition Deloop_op_to (M : MonObject) :
  (Deloop M)^op ⟶ Deloop (MonObject_op M) := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.

Program Definition Deloop_op_from (M : MonObject) :
  Deloop (MonObject_op M) ⟶ (Deloop M)^op := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.

(*
 Riehl Example 1.2.2(iii).  NOTE THE STRENGTH, which the first version of
 this file got wrong: `≅[Cat]` in this library IS equivalence of
 categories, because Cat's hom-setoid identifies naturally isomorphic
 functors (Instance/Cat.v), so the statement below is NOT an isomorphism
 of categories.  Here the stronger statement is available and is given
 immediately after: the two categories agree on objects, homs, hom-setoid,
 identities and composition, so the comparison is an isomorphism in
 StrictCat ([Deloop_op_strict]).  (Correction prompted by the groupoid
 work that consumes this file.) 

 --------
 Riehl 示例 1.2.2(iii)。注意强度，本文件的第一个版本写错了：在这个库中，`≅ [Cat]ZZ ` 是范畴的等价，因为 Cat 的 hom-集合体自然地识别同构函子（Instance/Cat.v），所以下面的陈述不是范畴的同构。在这里可以得到更强的陈述，并在之后立即给出：这两个范畴在对象、Hom、hom-集合体、恒等映射和复合上都一致，所以在 StrictCat 中的比较是同构（[Deloop_op_strict]）。（此更正由使用本文件的群对象工作促成。）
*)
Program Definition Deloop_op (M : MonObject) :
  (Deloop M)^op ≅[Cat] Deloop (MonObject_op M) := {|
  to   := Deloop_op_to M;
  from := Deloop_op_from M
|}.
(*
 Both round trips are the identity functor on the nose, so the witnessing
 natural isomorphism is the identity at the single object and the coherence
 condition collapses under the two unit laws. 

 --------
 两个往返都是严格的恒等函子，因此见证的自然同构在单一对象上是恒等的，并且在两个单位律下一致性条件消失。
*)
Next Obligation.
  exists (fun _ => iso_id); simpl; intros.
  now rewrite mon_op_unit_r, mon_op_unit_l.
Qed.
Next Obligation.
  exists (fun _ => iso_id); simpl; intros.
  now rewrite mon_op_unit_r, mon_op_unit_l.
Qed.

(* The group case transports too. / 团体案件也会运输。 *)
Definition GrpObject_op (G : GrpObject) : GrpObject := {|
  grp_monoid := MonObject_op (grp_monoid G);
  grp_inv    := grp_inv (g:=G);
  grp_inv_l  := fun a => grp_inv_r (g:=G) a;
  grp_inv_r  := fun a => grp_inv_l (g:=G) a
|}.

(*
 The strict form.  Both comparison functors are the identity on objects
 and on morphisms, so the object component of StrictCat's hom-setoid is
 [eq_refl], the transports vanish, and what remains is reflexivity of the
 morphism.  This is the genuine "isomorphism of categories" that the
 comment above previously — and wrongly — attached to the [Cat] form. 

 --------
 严格形式。两个比较函子在对象和态射上都是恒等的，因此 StrictCat 的同态集合的对象分量是 [eq_refl]，搬运消失，剩下的是态射的自反性。这才是真正的“范畴同构”，上面的注释之前 — 并且错误地 — 将其归于 [Cat] 形式。
*)
Program Definition Deloop_op_strict (M : MonObject) :
  (Deloop M)^op ≅[StrictCat] Deloop (MonObject_op M) := {|
  to   := Deloop_op_to M;
  from := Deloop_op_from M
|}.
(*
 Both round-trip obligations are discharged by the library's default
 obligation tactic: the comparison functors are the identity on objects
 AND on morphisms, so the two sides are convertible and nothing is left
 to prove. 

 --------
 图书馆的默认义务策略已经履行了双程义务：比较函子在对象上和态射上都是恒等的，因此两边是可互换的，没有什么需要证明的。
*)
