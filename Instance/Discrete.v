Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Discrete.

Generalizable All Variables.

Import EqNotations.

(* * * The discrete category on a Type / * * 类型上的离散范畴 *)

(*
 nLab: https://ncatlab.org/nlab/show/discrete+category

 Given any [Type] [A], the discrete category [DiscreteCat A] has the elements
 of [A] as objects and *propositional equality* [x = y] as the hom from [x] to
 [y]. Identity is [eq_refl] and composition is [eq_trans] (in the categorical
 orientation: [compose (g : y = z) (f : x = y) : x = z]). The hom-setoid is the
 strict-equality setoid [Morphism_equality], so every [≈]-goal here reduces to
 an [eq]-goal between equality proofs and is discharged by destructing the
 proofs — no UIP, function extensionality, or other axiom is needed, because
 the equivalence is [eq] itself rather than a quotient.

 This is the object-level construction: [DiscreteCat] *builds* a category out
 of a type. It is a genuinely different notion from the [Discrete] predicate of
 Structure/Discrete.v, which *asserts* that a given category has only identity
 morphisms. The sanity lemma [DiscreteCat_Discrete] at the end connects the two
 by showing that every [DiscreteCat A] does satisfy that predicate.

 Functors out of [DiscreteCat A] are exactly functions [A → C]: any [f : A → C]
 extends to [DiscreteCat_Functor f], transporting [id] along the equality
 witness. This is the left adjoint at the level of a single functor; the
 adjunction itself is [Disc_Objects_Adjunction] in Instance/Cat/Objects.v.
 NOTE THE AMBIENT: it is [Coq ⟶ StrictCat], not `Set ⟶ Cat`. That
 file proves [objects_not_functorial_over_Cat]: over [Cat] the swap
 endofunctor of [Indiscrete bool] is naturally isomorphic to the
 identity while moving every object, so no objects functor into a
 target comparing object maps by LEIBNIZ equality exists there. An
 isomorphism-setoid one does; the strict reading is the exercise's
 choice. 

 --------
 nLab: https://ncatlab.org/nlab/show/discrete+category

 给定任意 [Type] [A]，离散范畴 [DiscreteCat A] 的对象是 [A] 的元素，*命题等式* [x = y] 是从 [x] 到 [y] 的同态。恒等映射是 [eq_refl]，复合是 [eq_trans]（按范畴方向：[compose (g : y = z) (f : x = y) : x = z]）。同态集是严格等价集 [Morphism_equality]，因此这里的每一个 [≈] 目标都归约为 [eq] 目标（在等式证明之间），并通过析构这些证明来解决——不需要 UIP、函数外延性或其他公理，因为等价本身就是 [eq] 而不是商。这是对象级构造：[DiscreteCat] *从类型* 构建一个范畴。它与 Structure/Discrete.v 中的 [Discrete] 谓词是完全不同的概念，后者 *断言* 给定的范畴只具有恒等态射。最后的健全性引理 [DiscreteCat_Discrete] 通过展示每个 [DiscreteCat A] 都满足该谓词，将两者联系起来。从 [DiscreteCat A] 出发的函子恰好是函数 [A → C] : 任何 [f : A → C] 都可以扩展到 [DiscreteCat_Functor f] ，沿等式证据传送 [id]。这是在单个函子层面的左伴随；伴随本身在 Instance/Cat/Objects.v 中是 [Disc_Objects_Adjunction]。
 请注意环境：它是 [Coq ⟶ StrictCat]，而不是 `Set ⟶ Cat`。该文件证明了 [objects_not_functorial_over_Cat] ：在 [Cat] 上，[Indiscrete bool] 的交换自函子自然同构于恒等函子，同时移动每个对象，因此在那儿不存在任何对象函子映射到目标以 LEIBNIZ 等式比较对象的情况。存在一个同构-集合体；严格的理解是练习的选择。
*)

(*
 The discrete category on [A]: objects are elements of [A], morphisms are
 proofs of equality, composition is transitivity of equality. The explicit
 [@{o h p}] binders follow convention 2.4.11 (cf. Instance/One.v). 

 --------
 在 [A] 上的离散范畴：对象是 [A] 的元素，态射是等式的证明，复合是等式的传递性。显式的 [@{o h p}] 绑定遵循惯例 2.4.11（参见 Instance/One.v）。
*)
Program Definition DiscreteCat@{o h p} (A : Type@{o}) : Category@{o h p} := {|
  obj     := A;                       (* objects are elements of A / 对象是 A 的元素 *)
  hom     := fun x y => x = y;        (* morphisms are equality proofs / 态射是等式证明 *)
  homset  := fun x y => Morphism_equality@{o h p} x y;  (* strict-eq setoid / 严格等价集合 *)
  id      := fun _ => eq_refl;        (* identity is reflexivity / 身份是自反性 *)
  compose := fun _ _ _ g f => eq_trans f g  (* composition is transitivity / 复合是及物性 *)
|}.
(*
 The category laws (id_left, id_right, comp_assoc, comp_assoc_sym) and the
 [compose_respects] Proper are all discharged by the default obligation
 tactic: every goal is an [eq] between equality proofs, closed by reduction
 and reflexivity. 

 --------
 范畴定律（id_left、id_right、comp_assoc、comp_assoc_sym）以及 [compose_respects] 性质都被默认义务战术消解：每个目标都是 [eq] 在等式证明之间，通过化简和自反性闭合。
*)

(*
 Every function [f : A → C] induces a functor out of the discrete category:
 an object [x] maps to [f x], and the unique morphism [e : x = y] maps to [id]
 transported along [e] (which is [id] whenever [e] is [eq_refl]).

 THE BINDERS ARE LOAD-BEARING.  An earlier revision declared this with bare
 [{A : Type} {C : Category}]; universe minimization then instantiated the
 shape's hom and proof levels at [Set], so the printed type carried
 [DiscreteCat@{u Set Set} A ⟶ C].  Because [Limit] and [IsLimitCone]
 identify the shape's hom-and-proof universe with the AMBIENT's (unlike
 [Cone], which keeps them apart), that [Set] propagated into the statement
 of every limit over a discrete diagram — [iprod], [Complete] applied to a
 discrete shape, and thence [GAFT] and [representability_theorem], which
 printed [Category@{u1 Set Set}] and refused instantiation at any category
 whose homs live above [Set].  Annotating here, on the model of
 [DiscreteCat_Functor'] (Structure/Limit/Comparison.v), leaves the
 shape's levels free; the trailing [+] allows the auxiliary universes that
 [Program]'s obligations introduce.  The measured signature is

 DiscreteCat_Functor@{o h p uo uh up u} :
 ∀ {A : Type@{o}} {C : Category@{uo uh up}},
 (A → obj) → Functor@{o h p uo uh up}
 ( * o h p uo uh up u |= up < u / h <= p / h <= uh / h <= up
 / p <= up / uh <= up / … * )

 — no literal [Set] anywhere. 

 --------
 每个函数 [f : A → C] 引入了一个从离散范畴出的函子：一个对象 [x] 映射到 [f x]，唯一的态射 [e : x = y] 映射到沿 [e] 传送的 [id]（当 [e] 是 [eq_refl] 时，这就是 [id]）。这些绑定器是承重的。早期的修订用裸露的 [{A : Type} {C : Category}] 声明了这一点；然后宇宙最小化在 [Set] 实例化了形状的 hom 和 proof 级别，因此打印类型携带了 [DiscreteCat@{u Set Set} A ⟶ C]。因为 [Limit] 和 [IsLimitCone] 将形状的 hom 和 proof 宇宙与 AMBIENT 的宇宙识别在一起（不同于 [Cone]，后者将它们区分开），所以 [Set] 传播到每个离散图的极限声明中 — [iprod]，在离散形状上应用的 [Complete]，然后是 [GAFT] 和 [representability_theorem]，这些打印了 [Category@{u1 Set Set}] 并拒绝在 hom 位于 [Set] 之上的任何范畴进行实例化。在这里进行注释，按照 [DiscreteCat_Functor']（Structure/Limit/Comparison.v）的模式，会使形状的层次保持自由；随后出现的 [+] 允许 [Program] 所引入的辅助宇宙。测得的签名是

 DiscreteCat_Functor@{o h p uo uh up u} :
 ∀ {A : Type@{o}} {C : Category@{uo uh up}},
 (A → obj) → Functor@{o h p uo uh up}
 ( * o h p uo uh up u |= up < u / h <= p / h <= uh / h <= up
 / p <= up / uh <= up / … * )

 — 在任何地方都没有字面意义上的 [Set]。
*)
Program Definition DiscreteCat_Functor@{o h p uo uh up +}
  {A : Type@{o}} {C : Category@{uo uh up}} (f : A → C) :
  DiscreteCat@{o h p} A ⟶ C := {|
  fobj := f;
  fmap := fun x y (e : x = y) => match e with eq_refl => id end
|}.
(*
 The functor laws ([fmap_respects], [fmap_id], [fmap_comp]) are all discharged
 by the default obligation tactic: on the discrete source every morphism is an
 equality proof, so each goal reduces to a trivial identity in [C]. 

 --------
 函子定律（[fmap_respects]、[fmap_id]、[fmap_comp]）都可以通过默认义务战术来解决：在离散源上，每个态射都是一个等式证明，因此每个目标都简化为[C]中的一个平凡恒等式。
*)

(*
 Sanity lemma bridging the two notions: the constructed category
 [DiscreteCat A] satisfies the [Discrete] predicate of Structure/Discrete.v —
 every morphism forces its endpoints equal and is the transported identity. 

 --------
 连接这两种概念的合理性引理：构造的范畴[DiscreteCat A]满足Structure/Discrete.v中的[Discrete]谓词——每个态射都强制其端点相等，并且是被传递的恒等映射。
*)
Lemma DiscreteCat_Discrete@{o h p} (A : Type@{o}) :
  Discrete (DiscreteCat@{o h p} A).
Proof.
  intros x y e.
  exists e.                     (* the equality witness is the morphism itself / 等式见证本身就是态射 *)
  now destruct e.               (* [e ≈ rew e in eq_refl] by destructing [e] / 通过破坏 [e] 来 [e ≈ rew e in eq_refl] *)
Qed.
