Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Variety.

Generalizable All Variables.

(* * * Comparing the group variety with the category of groups / * * 将群的变体与群的范畴进行比较 *)

(*
 Mac Lane §V.6, book p. 124; the comparison obligation raised by issue
 #440's QA correction, which asks for [GroupVariety ≅[Cat] Grp] now that
 #255 has landed [Grp].

 ** THE ISOMORPHISM IS NOT AVAILABLE, AND THE REASON IS STRUCTURAL

 [Grp]'s objects (Instance/Grp.v) carry an ARBITRARY [SetoidObject]:
 a type together with a chosen equivalence, with every law stated up to
 that `≈`.  [GroupVariety]'s objects carry a BARE TYPE, with every law a
 Leibniz [=], because that is what Instance/Comp.v's [OpAlgebra] and
 [EqSignature] are built on.  The functor below goes one way for nothing
 — a bare type is a setoid under [=] — and is fully faithful.  What
 is missing is essential surjectivity in the other direction: to hit a group
 whose `≈` is coarser than [=] one must quotient its carrier by `≈`, and
 this tree has no quotient of a setoid by its own equivalence that
 returns a TYPE.  (Construction/Quotient.v quotients a category's
 hom-setoids, not a carrier.)  So the isomorphism is neither proved nor
 refuted here; what IS refuted, at Test/ProbeVariety440.v's negative n4,
 is that the two categories are the same object.

 The honest discharge of the QA correction is therefore the strongest
 comparison that does hold, stated as such: [GroupVariety_to_Grp], full
 and faithful, with [GroupVariety_to_Grp_reflects_iso] as its immediate
 consequence.  An earlier revision of this paragraph called that
 "exactly an isomorphism onto a full subcategory", which is too strong
 and an audit was right to catch it: full and faithful gives an
 EQUIVALENCE onto the full image, not an isomorphism, because
 injectivity on objects is neither proved here nor cheap to get.

 ** THIS WHOLE FILE CARRIES [functional_extensionality_dep]

 Not one of its TWENTY-TWO constants is closed under the global context
 — twelve [.glob] heads plus ten [Program] obligations, the latter
 invisible to a head census and missed by a first count that said
 "eleven".  The reason is inherited twice over.  [GroupVariety] mentions
 Instance/Comp.v's [GroupEq], which is [Defined] with the axiom; and
 the translation of an [AlgHom] into a [GrpHom] must turn
 [op_commute]'s argument-bundle equation into the pointwise statements
 [grp_map_unit] and [grp_map_mul], which is the same bundle rebuild that
 Instance/Variety.v's header describes.  Nothing here is gated;
 docs/AXIOMS.md records the file.

 This is also why the comparison lives in its own file: it keeps
 Instance/Grp.v's closure off Instance/Variety.v, and it keeps every
 axiom-carrying constant of this development in the two places
 docs/AXIOMS.md can point at. 

 --------
 Mac Lane §V.6，书页第124页；由问题#440的QA更正提出的比较义务，该更正要求在#255已经上线[Grp]后使用[GroupVariety ≅[Cat] Grp]。

 ** 同构不可用，原因是结构性的[Grp] 的对象（Instance/Grp.v）携带一个任意的 [SetoidObject]：
 一个类型以及一个选定的等价关系，每条定律都是以该 `≈` 为准叙述的。[GroupVariety] 的对象携带一个裸类型，每条定律都是一个莱布尼茨 [=]，因为这是 Instance/Comp.v 的 [OpAlgebra] 和 [EqSignature] 所建立的基础。下面的函子单向应用时没有任何阻碍——在 [=] 下裸类型是一个集合类型——而且它是完全忠实的。缺失的是另一方向上的本质满射性：要映射到一个其 `≈` 比 [=] 更粗的群，必须通过 `≈` 对其承载集合取商，而这个树没有能够通过自身等价关系对集合取商后返回一个类型的操作。(Construction/Quotient.v 对一个类别的同态集进行商运算，而不是对承载对象进行商运算。) 因此这里既没有证明也没有反驳该同构；在 Test/ProbeVariety440.v 的负面 n4 中被反驳的是，这两个类别是相同的对象。

 因此，对 QA 修正的诚实完成就是最强的比较，可以表述为：[GroupVariety_to_Grp] ，完全且忠实，[GroupVariety_to_Grp_reflects_iso] 是其直接结果。该段落的早期修订版本称其为“正好是到一个完整子类别的同构”，这说法过强，审核正确地指出了这一点：完全且忠实给出的是到完整像的等价，而不是同构，因为这里既没有证明对象的单射性，也不容易获得。

 ** 整个文件承载 [functional_extensionality_dep]它的二十二个常量中没有一个在全局上下文下是封闭的——十二个 [.glob] 头加上十个 [Program] 义务，后者对头计数是不可见的，并且在第一次计数中被漏掉了，当时说的是“十一”。原因是继承了两次。 [GroupVariety] 提到 Instance/Comp.v 的 [GroupEq]，它是带有公理的 [Defined]；将一个 [AlgHom] 翻译成 [GrpHom] 必须将 [op_commute] 的参数捆绑方程转化为逐点语句 [grp_map_unit] 和 [grp_map_mul]，这与 Instance/Variety.v 的头文件描述的捆绑重建相同。这里没有任何内容被封锁；文件 docs/AXIOMS.md 记录了该文件。这也是为什么比较保存在它自己的文件中的原因：它将 Instance/Grp.v 的闭包与 Instance/Variety.v 分开，并且它将本开发中的每个带公理的常量保存在两个 docs/AXIOMS.md 可以指向的位置。
*)

Module UA := Category.Instance.Comp.UniversalAlgebra.

(* * ** Turning an algebra homomorphism into a group homomorphism Both lemmas are [op_commute] followed by a bundle rebuild, which is where the extensionality enters. / * ** 将一个代数同态转换为群同态 两个引理都是 [op_commute]，随后是一个包重建，这就是外延性起作用的地方。 *)

(*
 The three bundle-normalisation lemmas.  An argument bundle over a
 finite enumeration is pointwise determined by its values, but NOT
 convertible to the case split on them — a [match] on a variable does
 not reduce — so each of these is an extensionality step, and they are
 where this file's axiom actually enters.  Each is written in the shape
 Instance/Comp.v's own [one'], [mul'] and [inv'] use, so that the
 rewritten goal is convertible with the [Grp] statement. 

 --------
 三个束归一化引理。一个对有限枚举的参数束由其值逐点决定，但不能转换为对它们进行的情况拆分——一个变量上的 [match] 不会归约——因此每个都是一个外延性步骤，它们是本文件公理实际介入的地方。每个都以 Instance/Comp.v 自身 [one']、[mul'] 和 [inv'] 使用的形式编写，因此重写后的目标可以与 [Grp] 语句可转换。
*)

Lemma nullary_bundle {A : Type} (k : UA.nullary → A) :
  k = (fun i => match i return A with end).
Proof. extensionality i; destruct i. Qed.

Lemma binary_bundle {A : Type} (k : UA.binary → A) :
  k = (fun i => match i return A with
                | UA.Fst => k UA.Fst
                | UA.Snd => k UA.Snd
                end).
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma unary_bundle {A : Type} (k : UA.unary → A) : k = (fun _ => k UA.Only).
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma alg_hom_one {A B : UA.OpAlgebra UA.GroupOp} (f : UA.AlgHom A B) :
  UA.map f (UA.one' (G:=A)) = UA.one' (G:=B).
Proof.
  unfold UA.one'.
  rewrite UA.op_commute.
  f_equal.
  extensionality i; destruct i.
Qed.

Lemma alg_hom_mul {A B : UA.OpAlgebra UA.GroupOp} (f : UA.AlgHom A B)
  (a b : UA.carrier A) :
  UA.map f (UA.mul' a b) = UA.mul' (UA.map f a) (UA.map f b).
Proof.
  unfold UA.mul'.
  rewrite UA.op_commute.
  f_equal.
  extensionality i; destruct i; reflexivity.
Qed.

(** ** The comparison functor / ** 比较函数对象 *)

Section ToGrp.

(* The three group laws [Grp] asks for, read off the variety's own [equations] field at the corresponding equation name. [assoc] arrives the other way round, hence the [symmetry]. / 三个群法则 [Grp] 要求，从相应的方程名称处读取该流形自身的 [equations] 域。[assoc] 是反过来的，因此 [symmetry] 。 *)

Program Definition GroupVariety_obj_to_Grp (x : GroupVariety) : GrpObject := {|
  grp_setoid := {| carrier   := UA.carrier (`1 x)
                 ; is_setoid := eq_Setoid (UA.carrier (`1 x)) |};
  grp_unit := UA.one' (G:=`1 x);
  grp_mul  := fun a b => UA.mul' a b;
  grp_inv  := fun a => UA.inv' a;
  (* The carrier setoid is [eq_Setoid], so `≈` is already a [Prop]. / 载体集合是 [eq_Setoid]，所以 `≈` 已经是一个 [Prop]。 *)
  grp_prop := eq_PropEquiv (UA.carrier (`1 x))
|}.
(*
 [grp_mul_respects] is discharged by Lib.v's default [Obligation Tactic]
 — under [eq_Setoid] it is [Proper (eq ==> eq ==> eq)] — so the three
 obligations that remain are the three laws, in [GrpObject]'s order.
 Their binders are pre-bound: [x] is the algebra and [X] its
 satisfaction proof, the sigma having been destructed. 

 --------
 [grp_mul_respects] 由 Lib.v 的默认 [Obligation Tactic] 解除——在 [eq_Setoid] 下它是 [Proper (eq ==> eq ==> eq)] ——所以剩下的三个义务就是三个定律，按 [GrpObject] 的顺序。它们的绑定器已预先绑定：[x] 是代数，[X] 是它的满足证明，sigma 已被解构。
*)
Next Obligation.
  symmetry.
  exact (X UA.assoc (fun i => match i with
                              | UA.One => a | UA.Two => b | UA.Three => c
                              end)).
Qed.
Next Obligation.
  exact (X UA.unit_left (fun _ => a)).
Qed.
Next Obligation.
  exact (X UA.inv_left (fun _ => a)).
Qed.

Program Definition GroupVariety_hom_to_Grp {x y : GroupVariety} (f : x ~> y) :
  GrpHom (GroupVariety_obj_to_Grp x) (GroupVariety_obj_to_Grp y) := {|
  grp_map := {| morphism := UA.map (`1 f) |}
|}.
(* Here too the binders are pre-bound and the sigma destructed, so [f] is the underlying [AlgHom] and not the pair. / 这里的绑定器也是预先绑定的，并且西格玛被破坏，所以 [f] 是底层的 [AlgHom]，而不是成对的。 *)
Next Obligation.
  exact (alg_hom_one f).
Qed.
Next Obligation.
  exact (alg_hom_mul f a b).
Qed.

Program Definition GroupVariety_to_Grp : GroupVariety ⟶ Grp := {|
  fobj := GroupVariety_obj_to_Grp;
  fmap := fun _ _ f => GroupVariety_hom_to_Grp f
|}.

End ToGrp.

(*
   * ** It is faithful, and full

   Faithful: both hom-setoids are pointwise Leibniz equality on the same
   carrier, so the hypothesis and the conclusion are the same statement.

   Full: a [GrpHom] between images preserves the unit and the
   multiplication pointwise, and that is enough to rebuild [op_commute]
   at each of the three operations — the arities are finite enumerations,
   so the bundle is rebuilt by case analysis (and one more use of
   extensionality). 

   --------
   * ** 它是忠实的，并且是满的

   忠实：两个同态集都是在相同载体上的逐点莱布尼茨相等，因此假设和结论是相同的陈述。

   满的：映像之间的一个  [GrpHom]  保留单位和逐点乘法，这足以在三个运算的每一个上重建  [op_commute] ——元数是有限枚举，因此该捆绑通过情况分析（以及再次使用外延性）重建。
*)

Lemma GroupVariety_to_Grp_Faithful : Faithful GroupVariety_to_Grp.
Proof. construct; simpl in *; auto. Qed.

Program Definition GroupVariety_hom_from_Grp {x y : GroupVariety}
  (g : GroupVariety_obj_to_Grp x ~{Grp}~> GroupVariety_obj_to_Grp y) : x ~> y :=
  ({| UA.map := grp_map g |}; I).
Next Obligation.
  destruct o; simpl.
  - (* one: nullary. Normalise both bundles to the empty match, after which the goal IS [grp_map_unit] by conversion. / 一：零元。将两个捆绑包都归一化为空匹配，之后目标通过转换为 [grp_map_unit]。 *)
    rewrite (nullary_bundle (fun i => grp_map g (args i))).
    rewrite (nullary_bundle args).
    exact (grp_map_unit g).
  - (* mul: binary / mul：二进制 *)
    rewrite (binary_bundle (fun i => grp_map g (args i))).
    rewrite (binary_bundle args).
    exact (grp_map_mul g (args UA.Fst) (args UA.Snd)).
  - (* inv: unary, where [inv'] uses a constant bundle / inv: 一元，其中 [inv'] 使用一个常量束 *)
    rewrite (unary_bundle (fun i => grp_map g (args i))).
    rewrite (unary_bundle args).
    exact (grp_map_inv g (args UA.Only)).
Qed.

Program Definition GroupVariety_to_Grp_Full : Functor.Full GroupVariety_to_Grp := {|
  prefmap := fun _ _ g => GroupVariety_hom_from_Grp g
|}.

(*
 A free consequence an audit pointed out: a fully faithful functor
 reflects isomorphisms, and Theory/Functor.v ships that implication, so
 two isomorphic groups in the image come from isomorphic algebras. 

 --------
 一次审计指出的一个自由结论：一个完全忠实的函子会反映同构，而 Theory/Functor.v 传递了这个蕴含，因此映像中的两个同构群来自同构的代数。
*)
Definition GroupVariety_to_Grp_reflects_iso :
  ∀ x y : GroupVariety,
    GroupVariety_to_Grp x ≅ GroupVariety_to_Grp y → x ≅ y :=
  @FullyFaithful _ _ GroupVariety_to_Grp
    GroupVariety_to_Grp_Full GroupVariety_to_Grp_Faithful.
