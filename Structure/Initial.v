Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/initial+object
 Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

 An initial object `0` is an object equipped, for every object `x`, with a
 morphism `zero : 0 ~> x` (written `¡` in the literature), subject to the
 universal mapping property that this morphism is unique: any two morphisms
 `0 ~> x` are equal (zero_unique). This is exactly the dual of a terminal
 object: an initial object in C is a terminal object in C^op, with all arrows
 reversed. The dual of `one : x ~> 1` is `zero : 0 ~> x`. An object that is
 both initial and terminal is a zero object. 

 --------
 nLab：https://ncatlab.org/nlab/show/initial+object
 Wikipedia：https://en.wikipedia.org/wiki/Initial_and_terminal_objects

 初始对象`0`是一个对象，对于每个对象`x`，都配备有一个态射`zero : 0 ~> x`（文献中记作`¡`），并满足以下泛映射性质：该态射是唯一的：任何两个态射`0 ~> x`都是相等的（zero_unique）。这正好是终对象的对偶：C中的初始对象是C^op中的终对象，并且所有箭头方向相反。`one : x ~> 1`的对偶是`zero : 0 ~> x`。既是初始对象又是终对象的对象称为零对象。
*)

(*
 Where initial objects come from, and what they are for

 Wikipedia: https://en.wikipedia.org/wiki/Universal_property
 nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
 nLab:      https://ncatlab.org/nlab/show/empty+type

 The initial object is the purest species of universal property: an
 object characterized not by any internal structure but solely by its
 relationship to everything else.  Universal mapping properties of
 this kind were presented by Pierre Samuel in 1948 for topological
 constructions and subsequently used extensively by Bourbaki, a
 decade before Kan independently introduced the closely related
 notion of adjoint functors in 1958 (Wikipedia, “Universal
 property”).  The initial object is the empty case of the whole
 theory of colimits — the colimit of the empty diagram, equivalently
 the nullary coproduct — which is why the unit laws [coprod_zero_l]
 and [coprod_zero_r] of Structure/Cocartesian.v exhibit 0 as the unit
 of the coproduct.  Any two initial objects are isomorphic by a
 unique isomorphism, and this uniqueness up to unique isomorphism,
 shared by every universal construction, is what licenses speaking of
 THE initial object (Milewski, “Products and Coproducts”, 2015).
 When the initial object moreover coincides with the terminal one,
 Structure/ZeroObject.v records the coincidence as [zero_coincide],
 and the additive spine of the library builds on it.

 A substantial portion of category theory reduces to exhibiting an
 initial object somewhere.  A universal arrow from c to a functor F IS
 an initial object of a comma category (Wikipedia, “Universal
 property”), and Theory/Universal/Arrow.v defines it exactly so, as
 the field [arrow_initial]; a colimit is an initial cocone; and a left
 adjoint to U exists precisely when each comma category d ↓ U has an
 initial object, the pivot on which Freyd's adjoint functor theorem
 turns.  That pivot is load-bearing in-tree: Theory/WeaklyInitial.v
 promotes a weakly initial family to a genuine initial object by
 Freyd's product-plus-equalizer construction
 ([initial_from_weakly_initial]), and Adjunction/GAFT.v concludes the
 theorem through [GAFT_from_initials].  Even the empty category [_0]
 of Instance/Zero.v is an instance, initial in Cat via the vacuous
 functor [From_0].

 The initial object also seeds the categorical account of induction.
 Adámek constructs the initial F-algebra as the colimit of the ω-chain
 0 ~> F 0 ~> F² 0 ~> ... based at the initial object (Adámek, “Free
 algebras and automata realizations in the language of categories”,
 Comment. Math. Univ. Carolinae 1974); in this library the chain of
 Construction/Chain.v starts at [initial_obj], and Theory/Adamek.v
 derives the initial algebra as [adamek].  Lambek had already observed
 that the structure map of any initial algebra is an isomorphism
 (Lambek, “A Fixpoint Theorem for Complete Categories”, Mathematische
 Zeitschrift 1968), formalized as [lambek] in Theory/Lambek.v; and the
 unique algebra morphism out of the initial algebra is the fold —
 [cata] of Theory/Recursion.v — so structural recursion is initiality
 put to work.  The ADJ group made this the basis of programming
 language semantics: abstract syntax is an initial algebra, and a
 semantics is the unique homomorphism into any target algebra, with
 compositionality following at once (Goguen, Thatcher, Wagner, Wright,
 “Initial Algebra Semantics and Continuous Algebras”, JACM 1977).

 The computational reading of this file is the empty type.  In
 Instance/Coq.v, [Coq_Initial] witnesses False as the initial object
 of the category of Coq types, the unique arrow out being [False_rect]
 — the empty function, Haskell's Void with its absurd (Milewski,
 “Products and Coproducts”, 2015).  Under propositions-as-types the
 empty type is falsehood, its eliminator is exactly ex falso
 quodlibet, and the eta-rule supplies the uniqueness half of
 initiality (nLab, “empty type”).  Read this way, [zero_unique] costs
 nothing: a function out of the empty type is defined by zero clauses,
 and any two such functions agree because there is no argument on
 which they could differ. 

 --------
 初始对象的来源及其用途

 维基百科:  https://en.wikipedia.org/wiki/Universal_property 
 nLab:       https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor 
 nLab:       https://ncatlab.org/nlab/show/empty+type初始对象是最纯粹的普遍性质类型的对象：它的特征不是由任何内部结构决定的，而仅由它与其他所有事物的关系决定。皮埃尔·萨缪尔(Pierre Samuel)在1948年提出了这种类型的普遍映射性质用于拓扑构造，随后在十年后被布尔巴基(Bourbaki)广泛使用，而在1958年，冈(Kan)独立引入了密切相关的伴随函子概念（Wikipedia，“Universal property”）。初始对象是余极限理论的空例——空图的余极限，同样也是零元积（nullary coproduct）——这就是为什么 Structure/Cocartesian.v 中的单位律 [coprod_zero_l] 和 [coprod_zero_r] 将 0 显示为余积的单位。任何两个初始对象通过唯一的同构是同构的，而这种唯一性（直到唯一同构）是每个泛对象构造都具有的，这就是为什么可以谈论“初始对象”的原因（Milewski，《Products and Coproducts》，2015）。当初始对象进一步与终对象重合时，Structure/ZeroObject.v 将这种重合记录为 [zero_coincide]，而且库的加性脊柱正是建立在它之上。范畴论的很大一部分可以归结为展示某处的初始对象。从 c 到函子 F 的一个通用箭头就是逗号范畴的一个初始对象（维基百科，“通用性质”），而 Theory/Universal/Arrow.v 正是如此定义的，即字段 [arrow_initial]；余极限是一个初始余锥；当且仅当每个逗号范畴 d ↓ U 都有一个初始对象时，U 的左伴随才存在，这就是弗雷德的伴随函子定理的枢轴。这个枢轴在树中是承重的：Theory/WeaklyInitial.v 通过弗雷德的乘积加等化子构造（[initial_from_weakly_initial]）将一个弱初始族提升为一个真正的初始对象，而 Adjunction/GAFT.v 通过 [GAFT_from_initials] 得出该定理的结论。即使是 Instance/Zero.v 的空类别 [_0] 也是一个实例，在 Cat 中通过平凡函子 [From_0] 是初始的。初始对象也为归纳的范畴论描述提供了基础。Adámek 构造了初始 F-代数作为以初始对象为基础的 ω 链的余极限  
 0 ~> F 0 ~> F² 0 ~> ...（Adámek，《范畴语言中的自由代数与自动机实现》，  
 Comment. Math. Univ. Carolinae 1974)；在这个库中，Construction/Chain.v 中的链以 [initial_obj] 开始，  
 而 Theory/Adamek.v 将初始代数推导为 [adamek]。Lambek 已经观察到，任何初始代数的结构映射都是一个同构（Lambek，《完整范畴的一个不动点定理》，Mathematische Zeitschrift 1968），在 Theory/Lambek.v 中形式化为 [lambek]；而从初始代数导出的唯一代数态射是 fold——在 Theory/Recursion.v 中形式化为 [cata]——所以结构递归就是将初始性付诸实践。ADJ 团队将此作为编程语言语义学的基础：抽象语法是一个初始代数，语义是到任意目标代数的唯一同态，组合性随之立即出现（Goguen, Thatcher, Wagner, Wright, 《初始代数语义与连续代数》，JACM 1977）。该文件的计算阅读类型为空类型。在 Instance/Coq.v 中，[Coq_Initial] 将 False 作为 Coq 类型范畴的初始对象，其唯一的箭头是 [False_rect] ——空函数，相当于 Haskell 的 Void 及其 absurd（Milewski, “Products and Coproducts”, 2015）。在命题即类型的解释下，空类型表示假，其消解器恰好是 ex falso quodlibet，而 eta 规则提供了初始性的一半唯一性（nLab, “empty type”）。这样理解，[zero_unique] 不耗费任何资源：从空类型到其他类型的函数通过零条款定义，任何两个这样的函数都一致，因为没有参数可以使它们不同。
*)

(*
 To be initial is just to be terminal in the opposite category; but to avoid
 confusion, we'd like a set of notations specific to categories with initial
 objects. As a consequence the initial-object UMP is not restated here as a
 primitive Class: `Initial C` literally unfolds to `Terminal (C^op)`, and the
 projections below recover the C-side names (initial_obj, zero, zero_unique)
 from the Terminal fields. 

 --------
 成为初始对象只是成为对立范畴中的终端对象；但为了避免混淆，我们希望有一套专门用于具有初始对象的范畴的符号。因此，初始对象的 UMP 在这里不会作为原始类重新表述：`Initial C` 字面上展开为 `Terminal (C^op)`，下面的投影从终端字段恢复了 C 端的名称（initial_obj、zero、zero_unique）。
*)

(*
   【Initial 记号与字段展开】/ Notation & field walkthrough

   1) 本文件不重写 Class：Notation “'Initial' C” := (@Terminal (C^op))。
      在对偶范畴里把终对象当初始对象用——箭头方向自动翻转。
      No new Class: Initial C is Terminal on C^op (arrows reverse).

   2) 导出名字 / Exported names (dual of Terminal's fields)
      - initial_obj / 0  —— 对象 0（= C^op 里的 terminal_obj）
      - zero {x}        —— ¡ : 0 ~> x（= C^op 里的 one）
      - zero_unique     —— 任意两出射箭头 ≈（= one_unique）

   3) 阅读提示：先懂 Terminal.v，再把「进 1」改成「出 0」即可。
      Read Terminal first; flip “into 1” to “out of 0”.
*)

Notation "'Initial' C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.
Notation "@Initial C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.

Section Initial_.

Context `{I : @Initial C}.

(* The initial object `0` itself (terminal in C^op). / 初始对象 `0` 本身（在 C^op 中为终端对象）。 *)
Definition initial_obj : C := @terminal_obj _ I.

(*
 The unique morphism `¡ : 0 ~> x` (the `one` of C^op).      

 --------
 唯一的态射 `¡ : 0 ~> x`（C^op 的 `one`）。
*)
Definition zero {x} : initial_obj ~{C}~> x := @one _ I _.

(*
 Uniqueness: any two morphisms out of `0` are equivalent.   

 --------
 唯一性：从 `0` 出发的任意两个态射是等价的。
*)
Definition zero_unique {x} (f g : initial_obj ~{C}~> x) : f ≈ g :=
  @one_unique _ I _ _ _.

End Initial_.

Notation "0" := initial_obj : object_scope.

Notation "zero[ C ]" := (@zero _ _ C)
  (at level 9, format "zero[ C ]") : morphism_scope.

(*
 Postcomposing the unique morphism `0 ~> x` is again unique (dual of
 one_comp): any `f ∘ zero` is forced to equal `zero` by zero_unique. 

 --------
 对唯一态射 `0 ~> x` 进行后组合仍然是唯一的（one_comp 的对偶）：任何 `f ∘ zero` 都被 zero_unique 强制等于 `zero`。
*)
Corollary zero_comp `{T : @Initial C} {x y : C} {f : x ~> y} :
  f ∘ zero ≈ zero.
Proof. apply (@one_comp _ T). Qed.

(*
 Uniqueness of the initial object (Mac Lane, CWM 2nd ed., §I.5, p. 20),
 the exact dual of [terminal_unique].

 Note this is NOT obtained by transporting [terminal_unique] along the
 [Initial C = Terminal (C^op)] definition: that would produce an
 isomorphism in `C^op`, and reading it back into `C` costs more than the
 two-line direct argument. Each structure supplies the unique arrow out of
 its own object, and both round trips are arrows out of an initial object,
 so [zero_unique] identifies them with the identity. 

 --------
 初始对象的唯一性（Mac Lane，《范畴论概论》第二版，第I.5节，第20页），是 [terminal_unique] 的精确对偶。

 注意，这不是通过沿着 [Initial C = Terminal (C^op)] 的定义将 [terminal_unique] 转换得到的：那样只会在 `C^op` 中产生一个同构，并且再读回到 `C` 会比两行的直接论证花费更多。每个结构都提供其自身对象的唯一箭头，而两个往返都是来自初始对象的箭头，因此 [zero_unique] 将它们识别为恒等映射。
*)
Program Definition initial_unique {C : Category} (I1 I2 : @Initial C) :
  @initial_obj C I1 ≅ @initial_obj C I2 := {|
  to   := @zero C I1 (@initial_obj C I2);
  from := @zero C I2 (@initial_obj C I1)
|}.
Next Obligation. apply (@zero_unique C I2). Qed.
Next Obligation. apply (@zero_unique C I1). Qed.

(*
 And it is the only arrow between them, so the isomorphism is canonical --
 the “unique isomorphism” half of Mac Lane's statement, dual to
 [terminal_arrow_unique]. 

 --------
 而它是它们之间唯一的箭头，因此同构是典范的——麦克莱恩陈述中“唯一同构”的一半，与 [terminal_arrow_unique] 对偶。
*)
Corollary initial_arrow_unique {C : Category} (I1 I2 : @Initial C)
      (f g : @initial_obj C I1 ~> @initial_obj C I2) : f ≈ g.
Proof. apply (@zero_unique C I1). Qed.

(*
 The initial dual of Block A, taken by duality in the file's own idiom:
 each definition is its terminal counterpart read in C^op, exactly as
 [initial_obj]/[zero]/[zero_unique] above are [terminal_obj]/[one]/
 [one_unique] read in C^op.  Note that -- unlike [initial_unique],
 where the file records that transporting would cost more than the
 direct argument -- there is no cost here: no isomorphism has to be
 read back into C, because the statements are about C-objects
 throughout and only the hom-direction is reversed. 

 --------
 块 A 的初始对偶，通过文件自身的术语取对偶：
 每一个定义都是在 C^op 中读取的其终端对应物，正如上面的
 [initial_obj] / [zero] / [zero_unique] 在 C^op 中读取为 [terminal_obj] / [one] / [one_unique] 一样。注意——不同于 [initial_unique]，其中文件记录了运输会比直接参数更耗费——这里没有成本：不需要将任何同构读回到 C，因为整个叙述都是关于 C-对象的，只是同态方向被反转了。
*)
Definition IsInitialObj {C : Category} (c : C) : Type :=
  @IsTerminalObj (C^op) c.

Definition is_initial_zero {C : Category} {c : C} (H : IsInitialObj c)
  {x : C} : c ~> x := @is_terminal_one (C^op) c H x.

Definition is_initial_unique {C : Category} {c : C} (H : IsInitialObj c)
  {x : C} (f g : c ~> x) : f ≈ g := @is_terminal_unique (C^op) c H x f g.

Definition Initial_from_IsInitialObj {C : Category} {c : C}
  (H : IsInitialObj c) : @Initial C :=
  @Terminal_from_IsTerminalObj (C^op) c H.

Definition IsInitialObj_from_Initial {C : Category} (I : @Initial C) :
  IsInitialObj (@initial_obj C I) :=
  @IsTerminalObj_from_Terminal (C^op) I.

(*
 Riehl, CTiC, Exercise 1.6.ii(i), initial half.  [Isomorphism_Opposite]
 (Construction/Opposite.v) re-reads the C-isomorphism in C^op, and
 [Terminal_iso] at C^op is the whole proof. 

 --------
 Riehl，CTiC，练习 1.6.ii(i)，初始一半。[Isomorphism_Opposite]（Construction/Opposite.v）在 C^op 中重新读取 C-同构，并且 [Terminal_iso] 在 C^op 中是整个证明。
*)
Definition Initial_iso {C : Category} (I : @Initial C) (y : C)
  (i : @initial_obj C I ≅ y) : @Initial C :=
  @Terminal_iso (C^op) I y (Isomorphism_Opposite i).

(*
 The transported structures choose the new object definitionally, which
 is what makes them usable as transports rather than as bare existence
 statements. 

 --------
 被传输的结构按定义选择新的对象，这正是使它们可用作传输而不是作为纯粹存在陈述的原因。
*)
Corollary Terminal_iso_obj {C : Category} (T : @Terminal C) (y : C)
  (i : @terminal_obj C T ≅ y) : @terminal_obj C (Terminal_iso T y i) = y.
Proof. reflexivity. Qed.

Corollary Initial_iso_obj {C : Category} (I : @Initial C) (y : C)
  (i : @initial_obj C I ≅ y) : @initial_obj C (Initial_iso I y i) = y.
Proof. reflexivity. Qed.

(*
 The dual of [terminal_unique_up_to_unique_iso]: two initial objects are
 connected by exactly one isomorphism. 

 --------
 [terminal_unique_up_to_unique_iso] 的对偶：两个初始对象恰好由一个同构连接。
*)
Program Definition initial_unique_up_to_unique_iso {C : Category}
  (I1 I2 : @Initial C) :
  Unique (fun _ : @initial_obj C I1 ≅ @initial_obj C I2 => True) := {|
  unique_obj := initial_unique I1 I2;
  unique_property := I
|}.
Next Obligation.
  split.
  - apply (@zero_unique C I1).
  - apply (@zero_unique C I2).
Qed.

Program Definition initial_hom_unique {C : Category} (I1 I2 : @Initial C) :
  Unique (fun _ : @initial_obj C I1 ~> @initial_obj C I2 => True) := {|
  unique_obj := @zero C I1 (@initial_obj C I2);
  unique_property := I
|}.
Next Obligation. apply (@zero_unique C I1). Qed.

(*
 Any two morphisms out of an object isomorphic to `0` agree.  Transport both
 along the isomorphism -- `p ≈ (p ∘ from i) ∘ to i` -- and the transported
 halves are morphisms out of `0` proper, where [zero_unique] applies.

 This is the engine behind strict initiality (Structure/BiCCC.v's
 [initial_strict]): once an object is KNOWN isomorphic to `0`, arrows out of
 it are forced, even though arrows INTO `0` are not. 

 --------
 任何从一个与  `0`  同构的对象出的两个态射都是一致的。沿同构—— `p ≈ (p ∘ from i) ∘ to i` ——传输两者，传输后的两半就是从  `0`  出发的正确态射，其中  [zero_unique]  适用。

 这是严格初始性的核心（Structure/BiCCC.v 的 [initial_strict]）：一旦一个对象被知道与  `0`  同构，出射的箭头就被强制确定，即使指向  `0`  的箭头不是这样。
*)
Lemma iso_initial_arrow_unique {C : Category} `{I : @Initial C} {y z : C}
      (i : y ≅ @initial_obj C I) (p q : y ~> z) : p ≈ q.
Proof.
  rewrite <- (id_right p), <- (id_right q).
  rewrite <- (iso_from_to i).
  rewrite !comp_assoc.
  now rewrite (@zero_unique C I z (p ∘ from i) (q ∘ from i)).
Qed.
