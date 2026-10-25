Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Twisting a functor by a family of isomorphisms  / * 通过同构族扭曲函子*)

(*
nLab: https://ncatlab.org/nlab/show/functor
   nLab: https://ncatlab.org/nlab/show/natural+isomorphism

   Given a functor [F : C ⟶ C] and a family of isomorphisms
   [α x : x ≅ F x] -- one for each object, with NO naturality assumed --
   the assignment

       x ↦ x,      f ↦ (α y)⁻¹ ∘ fmap[F] f ∘ α x

   is again an endofunctor of C, [Twist F α].  Functoriality needs nothing
   from α beyond invertibility: the identity law is [fmap_id] followed by
   [iso_from_to], and the composition law is [fmap_comp] with the inner
   [α y ∘ (α y)⁻¹] cancelled by [iso_to_from].

   The point of the construction is that its OBJECT FUNCTION IS THE
   IDENTITY, [fun x => x], on the nose, while its arrow function need not
   be the identity.  It is therefore the standard machine for producing
   two functors that agree on objects and differ on morphisms -- the
   question Mac Lane raises in "Categories for the Working Mathematician",
   2nd ed. (GTM 5), Section I.3 ("Functors"), where the reader is asked to
   find two different functors [Grp ⟶ Grp] whose object function is the
   identity, so that a functor is seen not to be determined by its action
   on objects.

   WHEN THE TWIST COLLAPSES.  [Twist_natural_strict_id] proves that if α
   IS natural -- [α y ∘ f ≈ fmap[F] f ∘ α x] for every f -- then
   [Twist F α] is strictly equal to [Id], because naturality lets the two
   copies of α annihilate across f.  [Twist_strict_id_natural] is the
   converse under uniqueness of identity proofs on the objects of C, so
   for a category whose objects have decidable equality the twist differs
   from the identity EXACTLY when α is not natural.  That is what makes
   Mac Lane's exercise awkward in a proof assistant: every natural family
   produces nothing new, and the families one can write uniformly in the
   object tend to be natural.  Instance/Grp/TwoFunctors.v works two such
   candidates out in full, and both do collapse.

   STRICT VERSUS WEAK EQUALITY OF FUNCTORS.  The library has two
   equivalences on [C ⟶ D].  [Functor_Setoid] (Theory/Functor.v),
   which is the hom-setoid of [Cat] (Instance/Cat.v), identifies two
   functors as soon as they are naturally isomorphic.
   [Functor_StrictEq_Setoid] (Theory/Functor.v), the hom-setoid of
   [StrictCat] (Instance/StrictCat.v), asks instead for a propositional
   equality of the object maps together with agreement of the arrow maps
   after transport along it; it refines the weak one
   ([strict_equiv_implies_fun_equiv], Instance/StrictCat/ToCat.v, and
   Test/Issue138.v pins both hom-setoids).

   The twist sits exactly on that seam.  [Twist_Id_weak_equiv] shows that
   for F = Id the twisted functor is ALWAYS identified with [Id] by the
   weak setoid -- α itself is the witnessing natural isomorphism, and its
   coherence condition holds by construction rather than by an argument.
   So a separation of [Twist Id α] from [Id] can only be a separation in
   the strict setoid, and that is the sense in which Mac Lane's exercise
   has to be read here. 

--------
nLab：https://ncatlab.org/nlab/show/functor
 nLab：https://ncatlab.org/nlab/show/natural+isomorphism

给定一个函子 [F : C ⟶ C] 和一系列同构
 [α x : x ≅ F x]——每个对象一个，不假设自然性——
 作业

x ↦ x, f ↦ (α y)⁻¹ ∘ fmap[F] f ∘ α x

又是 C 的内函子 [Twist F α]。 功能性不需要任何东西
 从超越可逆性的 α 开始：恒等律为 [fmap_id]，随后为
 [iso_from_to]，其组成规律为 [fmap_comp]，其内
 [α y ∘ (α y)⁻¹] 被 [iso_to_from] 取消。

构造的要点是它的对象函数是
 IDENTITY，[fun x => x]，在鼻子上，而其箭头功能不需要
 是身份。 因此，它是生产的标准机器
 两个函子在对象上一致而在态射上不同——
 麦克莱恩在“工作数学家的类别”中提出的问题，
 第二版。 (GTM 5)，第 I.3 节（“函子”），要求读者
 找到两个不同的函子 [Grp ⟶ Grp]，其目标函数是
 身份，以便函子不被视为由其动作决定
 在物体上。

当扭曲崩溃时。 [Twist_natural_strict_id] 证明如果 α
 是自然的 -- [α y ∘ f ≈ fmap[F] f ∘ α x] 对于每个 f -- 那么
 [Twist F α] 严格等于 [Id]，因为自然性让两者
 α 的拷贝在 f 上湮灭。 [Twist_strict_id_natural] 是
 在 C 的对象上的身份证明的唯一性下进行对话，所以
 对于对象具有可判定相等性的类别，扭曲是不同的
 当 α 不是自然数时，完全由恒等式得出。 这就是使
 麦克莱恩的练习在证明助理中很尴尬：每个自然家庭
 没有产生任何新的东西，人们可以统一地写在
 对象往往是自然的。 Instance/Grp/TwoFunctors.v 工作两个这样的
 候选人全部出局，两人都崩溃了。

函子的严格与弱等式。 图书馆有两个
 [C ⟶ D] 上的等效项。 [Functor_Setoid]（理论/Functor.v），
 这是 [Cat] (Instance/Cat.v) 的 hom-setoid，标识了两个
 一旦函子自然同构。 
[Functor_StrictEq_Setoid] (Theory/Functor.v)，hom-setoid
 [StrictCat]（Instance/StrictCat.v），要求提供一个命题
 对象映射的相等性以及箭头映射的一致性
 沿其运输后； 它精炼弱者
 （[strict_equiv_implies_fun_equiv]、Instance/StrictCat/ToCat.v 和
 Test/Issue138.v 固定两个 hom-setoids）。

扭曲正好位于该接缝处。 [Twist_Id_weak_equiv] 表明
 对于 F = Id，扭曲函子始终通过 [Id] 进行标识
 弱集合——α本身就是见证自然同构，它的
 连贯条件是通过构造而不是通过论证而成立的。 
因此，[Twist Id α] 与 [Id] 的分离只能是以下方面的分离：
 严格的集合，这就是麦克莱恩的练习的意义
 必须在这里阅读。 
*)

Section Twist.

Context {C : Category}.
Context (F : C ⟶ C).
Context (α : ∀ x : C, x ≅ F x).

#[local] Obligation Tactic := idtac.

(*
The twisted functor.  Note [fobj := fun x => x]: the object function is
   the identity function itself, not merely a function isomorphic to it. 

--------
扭曲函子。 注意 [fobj := fun x => x]：目标函数是
 恒等函数本身，而不仅仅是与其同构的函数。 
*)
Program Definition Twist : C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun x y f => (α y)⁻¹ ∘ fmap[F] f ∘ α x
|}.
Next Obligation.
  intros x y f g Hfg.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros x; simpl.
  rewrite fmap_id, id_right.
  apply iso_from_to.
Qed.
Next Obligation.
  intros x y z f g; simpl.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite (comp_assoc (α y)).
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(*
The object function is the identity, by computation.  The [=] is on
   OBJECTS, which is where this library does use propositional equality --
   it is what [Functor_StrictEq_Setoid] compares; morphisms are compared
   with ≈ everywhere. 

--------
通过计算，对象函数是恒等式。 [=] 已开启
 OBJECTS，这是这个库使用命题相等的地方——
 这是 [Functor_StrictEq_Setoid] 所比较的； 比较态射
 到处都有 ≈ 。 
*)
Lemma Twist_fobj (x : C) : fobj[Twist] x = x.
Proof. reflexivity. Qed.

(*
If α is natural, the twist is strictly equal to the identity functor:
   the object equalities are all [eq_refl], and the arrow condition is
   α cancelling itself across f. 

--------
如果 α 是自然的，则扭曲严格等于恒等函子：
 对象等式均为 [eq_refl]，箭头条件为
 α 在 f 上抵消自身。 
*)
Theorem Twist_natural_strict_id
  (nat : ∀ (x y : C) (f : x ~> y), α y ∘ f ≈ fmap[F] f ∘ α x) :
  @equiv _ Functor_StrictEq_Setoid Twist (@Id C).
Proof.
  exists (fun _ => eq_refl).
  intros x y f.
  (*
Both transports are along [eq_refl], hence the identity, so the
     coherence condition reduces by conversion to the arrow maps agreeing. 

--------
两种传输均沿 [eq_refl] 进行，因此具有同一性，因此
 相干条件通过转换为一致的箭头图而减少。 
*)
  change ((α y)⁻¹ ∘ fmap[F] f ∘ α x ≈ f).
  rewrite <- comp_assoc.
  rewrite <- nat.
  rewrite comp_assoc.
  rewrite iso_from_to.
  apply id_left.
Qed.

(*
The converse, given uniqueness of identity proofs on the objects of C.
   The hypothesis is needed because the strict setoid allows an ARBITRARY
   proof of [x = x] as the object component; without [uip] a nontrivial
   loop could in principle scramble the transports. 

--------
相反，考虑到 C 对象的身份证明的唯一性。 
该假设是必要的，因为严格的 setoid 允许任意
 [x = x] 作为对象组件的证明； 没有 [uip] 就不平凡
 循环原则上可以扰乱传输。 
*)
Theorem Twist_strict_id_natural
  (uip : ∀ (x : C) (p : x = x), p = eq_refl)
  (H : @equiv _ Functor_StrictEq_Setoid Twist (@Id C)) :
  ∀ (x y : C) (f : x ~> y), α y ∘ f ≈ fmap[F] f ∘ α x.
Proof.
  destruct H as [eq_on_obj coherent].
  intros x y f.
  pose proof (coherent x y f) as Hc.
  rewrite (uip x (eq_on_obj x)), (uip y (eq_on_obj y)) in Hc.
  (* with both object equalities [eq_refl] the transports vanish  / 当两个对象相等 [eq_refl] 时，传输消失*)
  assert (Hred : (α y)⁻¹ ∘ fmap[F] f ∘ α x ≈ f) by exact Hc.
  assert (Hpost : α y ∘ ((α y)⁻¹ ∘ fmap[F] f ∘ α x) ≈ α y ∘ f)
    by (apply compose_respects; [ reflexivity | exact Hred ]).
  rewrite <- Hpost.
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(*
The distinctness criterion in the form it is used: a SINGLE morphism at
   which α is not natural separates the twist from the identity in
   the strict functor setoid. 

--------
使用形式的独特性标准：单态射
 其中 α 不是自然的，将扭曲与恒等式分开
 严格函子集合。 
*)
Corollary Twist_not_strict_id
  (uip : ∀ (x : C) (p : x = x), p = eq_refl)
  {x y : C} {f : x ~> y}
  (Hnat : α y ∘ f ≈ fmap[F] f ∘ α x → False) :
  @equiv _ Functor_StrictEq_Setoid Twist (@Id C) → False.
Proof.
  intro H.
  exact (Hnat (Twist_strict_id_natural uip H x y f)).
Qed.

End Twist.

Arguments Twist {C} F α.

(*
Uniqueness of identity proofs from decidable equality of objects
   (Hedberg's argument, via the stdlib's axiom-free [UIP_dec]); this is
   how the [uip] hypothesis above is discharged for the concrete
   categories used as witnesses. 

--------
来自可判定对象相等性的身份证明的唯一性
 （Hedberg 的论点，通过 stdlib 的无公理 [UIP_dec]）； 这是
 上述 [uip] 假设如何具体体现
 用作证人的类别。 
*)
Definition uip_of_dec {A : Type}
  (dec : ∀ x y : A, {x = y} + {x <> y}) (x : A) (p : x = x) : p = eq_refl :=
  UIP_dec dec p eq_refl.

Section TwistId.

Context {C : Category}.
Context (α : ∀ x : C, x ≅ x).

(*
The twist of the IDENTITY functor is always naturally isomorphic to the
   identity functor -- α is the natural isomorphism, and the coherence
   condition of [Functor_Setoid] is literally the definition of the
   twisted arrow map.  Hence the weak setoid, which is the hom-setoid of
   [Cat], never separates this pair, however far α is from being natural. 

--------
IDENTITY 函子的扭曲总是自然同构于
 恒等函子——α是自然同构，相干
 [Functor_Setoid] 的条件字面上是定义
 扭曲的箭头地图。 因此弱集合体，即 hom-setoid
 [Cat]，无论 α 离自然有多远，都不会分开这一对。 
*)
Theorem Twist_Id_weak_equiv :
  @equiv _ Functor_Setoid (Twist (@Id C) α) (@Id C).
Proof.
  exists α.
  intros x y f; simpl.
  reflexivity.
Qed.

End TwistId.
