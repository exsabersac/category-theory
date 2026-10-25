Require Import Category.Lib.
Require Import Equations.Prop.Logic.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(* * * The comparison functor [StrictCat ⟶ Cat] / * * 比较仿函数 [StrictCat ⟶ Cat] *)

(*
 Issue #138 observes that [Cat] uses [Functor_Setoid], which identifies
 functors only up to natural isomorphism, whereas the ZFC-style notion of
 equality of functors is the *strict* one used by [StrictCat]
 ([Functor_StrictEq_Setoid]: equal object maps, with morphism maps agreeing
 after transport).  The two notions are not interchangeable — the underlying
 1-category of the 2-category [Cat] genuinely needs the weak hom-equivalence,
 since an isomorphism there is an *equivalence* of categories (this is what
 the Lawvere/comma characterisation of adjunctions in
 [Construction.Comma.Adjunction] relies on).

 What *is* true, and is the content of this file, is that the strict notion
 refines the weak one: strict equality of functors implies natural
 isomorphism.  This gives an identity-on-objects, identity-on-morphisms
 comparison functor [StrictCat_to_Cat : StrictCat ⟶ Cat], exhibiting
 [StrictCat] as a strictification of [Cat].  Functors *out of* [StrictCat]
 that do not respect natural isomorphism — e.g. the underlying-graph functor
 [Construction.Free.Quiver.Forgetful : StrictCat ⟶ Quiv] — therefore cannot
 in general be factored through this comparison functor, which is precisely
 why [StrictCat] is needed. 

 --------
 问题 #138 指出，[Cat] 使用 [Functor_Setoid]，该方法仅在自然同构意义下识别函子，而 ZFC 风格的函子等同性的概念是 [StrictCat] 使用的*严格*概念（[Functor_StrictEq_Setoid]：对象映射相等，且在传输后态射映射一致）。这两种概念不可互换——2-范畴 [Cat] 的底层 1-范畴确实需要弱态射等价，因为那里同构是范畴的*等价*（这正是 [Construction.Comma.Adjunction] 中拉瓦尔/逗号表征伴随的依据）。真正的情况，也是这个文件的内容，是严格的概念细化了弱的概念：函子严格相等意味着自然同构。这给出了一个在对象上和态射上都是恒等的比较函子 [StrictCat_to_Cat : StrictCat ⟶ Cat]，展示了 [StrictCat] 作为 [Cat] 的严格化。从 [StrictCat] 出发的函子如果不尊重自然同构——例如底图函子 [Construction.Free.Quiver.Forgetful : StrictCat ⟶ Quiv]——因此通常不能通过这个比较函子分解，这正是为什么需要 [StrictCat]。
*)

(*
 An equality of objects induces an isomorphism: transport the identity along
 the equality.  By path induction this is [iso_id] when the proof is
 [eq_refl], so [to] and [from] compute to [id]. 

 --------
 对象的等式会引起同构：沿着等式传递恒等式。通过路径归纳，当证明是 [eq_refl] 时，这是 [iso_id]，因此 [to] 和 [from] 计算为 [id]。
*)
Definition iso_of_eq {C : Category} {x y : C} (p : x = y) : x ≅ y :=
  match p in (_ = z) return (x ≅ z) with
  | eq_refl => iso_id
  end.

(*
 Transporting a morphism along an equality of its codomain is the same as
 post-composing with the induced isomorphism. 

 --------
 沿着其余域的等式传输一个态射与后组合诱导的同构是相同的。
*)
Lemma transport_cod_to_iso {C : Category} {c a b : C} (p : a = b) (g : c ~> a) :
  transport (fun z => hom c z) p g ≈ to (iso_of_eq p) ∘ g.
Proof. destruct p; simpl; now rewrite id_left. Qed.

(*
 Dually, transporting along an equality of the domain (via [transport_r]) is
 pre-composition with the induced isomorphism. 

 --------
 同样地，沿着域的等式进行传输（通过 [transport_r]）是与诱导同构的预组合。
*)
Lemma transport_r_dom_to_iso {C : Category} {a b d : C} (p : a = b) (g : b ~> d) :
  transport_r (fun z => hom z d) p g ≈ g ∘ to (iso_of_eq p).
Proof. destruct p; unfold transport_r; simpl; now rewrite id_right. Qed.

(*
 The mathematical core of issue #138: two functors that are strictly equal
 (equal on objects, with morphism maps agreeing after transport) are
 naturally isomorphic.  The natural isomorphism is, objectwise, the identity
 transported along the object equality. 

 --------
 问题 #138 的数学核心：两个函子严格相等（在对象上相等，其态射映射在传递后也相同）是自然同构的。自然同构在每个对象上是沿对象等式传递的恒等映射。
*)
Lemma strict_equiv_implies_fun_equiv {C D : Category} (F G : C ⟶ D) :
  @equiv _ Functor_StrictEq_Setoid F G ->
  @equiv _ Functor_Setoid F G.
Proof.
  intros [eq_on_obj coh].
  exists (fun x => iso_of_eq (eq_on_obj x)).
  intros x y f.
  pose proof (coh x y f) as Hc.
  rewrite transport_cod_to_iso in Hc.
  rewrite transport_r_dom_to_iso in Hc.
  rewrite <- comp_assoc.
  rewrite <- Hc.
  rewrite comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

(*
 The comparison functor is the identity on both objects and morphisms; the
 only content is that it sends strict equality to natural isomorphism. 

 --------
 比较函子在对象和态射上都是恒等的；唯一的内容是它将严格相等映射为自然同构。
*)
Program Definition StrictCat_to_Cat : StrictCat ⟶ Cat := {|
  fobj := fun C => C;
  fmap := fun _ _ F => F
|}.
Next Obligation.
  repeat intro.
  now apply strict_equiv_implies_fun_equiv.
Qed.
