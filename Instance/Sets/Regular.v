Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * Regular arrows in Sets: the blanket principle decides every proposition / * * 集合中的常规箭头：普遍原则决定每一个命题 *)

(*
 nLab:      https://ncatlab.org/nlab/show/Diaconescu%27s+theorem
 nLab:      https://ncatlab.org/nlab/show/split+epimorphism
 Wikipedia: https://en.wikipedia.org/wiki/Diaconescu%27s_theorem
 Wikipedia: https://en.wikipedia.org/wiki/Axiom_of_choice

 Mac Lane, CWM 2nd ed., §I.5 Exercise 7 asks, in its second half, for the
 regularity of every arrow of Set with nonempty domain.
 Instance/FinSet/Regular.v settles that over FinSet by an executable finite
 search.  This file measures what the same statement costs over [Sets], the
 library's category of setoids, and the measurement does not come out where
 the classical account of the exercise suggests it will.

 THE CLASSICAL ACCOUNT.  Fix f : A → B with A inhabited by a₀.  A
 pseudoinverse must send each b of B to SOME element of the fibre f⁻¹(b)
 when that fibre is nonempty, and anywhere at all (say a₀) when it is
 empty.  Nothing in the data of f selects a fibre element, so the classical
 construction picks one simultaneously for every b in the image: an
 instance of the axiom of choice over the family of fibres.  Reading a
 regularity witness back off is choice-free, and is
 [regular_epic_retraction] / [regular_monic_section] of
 Theory/Morphisms.v.

 WHAT THE PRINCIPLE COSTS HERE.  In this library's ambient logic that
 account understates the price, and understates it by a wide margin.  The
 blanket principle is stronger than any choice axiom on offer: it DECIDES
 EVERY PROPOSITION.  [blanket_regularity_entails_LEM] below derives,
 axiom-free, the Type-valued excluded middle ∀ P : Prop, P + (P → False)
 from [BlanketRegularity]; and [blanket_splitting_entails_LEM] derives the
 very same conclusion from the weaker principle [BlanketSplitting], "every
 epimorphism with inhabited domain splits", which is the internal axiom of
 choice the nLab page on split epimorphisms records as the categorical
 phrasing of choice.  Coq's ambient logic is intuitionistic and proves
 neither conclusion, so neither principle is available in this development,
 and the exercise's second half stops at the finite case for a reason.

 THE COUNTERMODEL.  Take bool with Coq's `=` for A, and bool again for B
 but with the two booleans identified exactly when P holds ([sets_coarse]
 below); A is inhabited by [true], and the identity on carriers is a
 [Sets]-morphism into the coarser setoid ([sets_coarsen]), since it only
 ever has to make things MORE equal.  A pseudoinverse g is again a
 [Sets]-morphism, so P forces g true = g false; the regularity equation
 read at each of the two booleans gives (g b = b) + P; two answers on the
 left force P → False, and either answer on the right gives P outright.
 That is [sets_coarsen_regular_dec], and its converse
 [sets_coarsen_regular_of_dec] holds too, so the regularity of this ONE
 arrow of [Sets] is EXACTLY the decidability of P
 ([sets_coarsen_regular_iff_dec]).

 WHY CHOICE CANNOT BE THE MEASURE.  A choice axiom would not deliver these
 principles, because Coq's choice axioms do not decide propositions.  The
 standard library axiomatizes relational choice on its own, with no
 classical import (Stdlib.Logic.RelationalChoice); the module that does
 yield excluded middle is Stdlib.Logic.ClassicalChoice, and it yields it by
 re-exporting Stdlib.Logic.ClassicalUniqueChoice, which re-exports
 Stdlib.Logic.Classical -- the excluded middle there is imported outright,
 not extracted from choice.  What the countermodel above turns on is
 instead the SETOID phrasing: choice over setoids is the extensional axiom
 of choice, and Stdlib.Logic.SetoidChoice records its decomposition into
 classical logic, relational choice, unique choice, and a limited
 functional extensionality, citing Carlström, "EM + Ext_ + AC_int is
 equivalent to AC_ext" (Mathematical Logic Quarterly 50(3), 2004,
 pp. 236-240).  The classical logic in that decomposition is exactly what
 the theorems below recover, and the argument that recovers it has the
 shape of Diaconescu's: a two-element object coarsened by a proposition,
 over which choosing a representative decides the proposition (Diaconescu,
 "Axiom of choice and complementation", Proc. Amer. Math. Soc. 51, 1975,
 pp. 176-178; nLab, "Diaconescu's theorem", retrieved 2026-08).  A setoid
 library supplies the quotient-like objects that argument needs at no extra
 cost, which is why the price is paid HERE and is not paid by the
 intensional choice axioms of the standard library.

 WHAT REMAINS TRUE.  Nothing above refutes the regularity of any particular
 arrow of [Sets], and that too is a theorem rather than an omission:
 [sets_coarsen_not_regular_absurd] REFUTES non-regularity for
 [sets_coarsen], so no proof that this arrow is not regular can exist --
 and this in a case where [sets_coarse_const] puts an arrow in the reverse
 hom-set and [true] inhabits the domain.  Over [Sets], then, an arrow with
 inhabited domain can be neither provably regular nor provably not, which
 is why the in-tree refutations of regularity ([TwoXY_not_regular] in
 Instance/Two.v, [finset_empty_to_one_not_regular] in
 Instance/FinSet/Regular.v) both work by exhibiting an EMPTY reverse
 hom-set.  That shape is forced, not chosen for convenience. 

 --------
 nLab：       https://ncatlab.org/nlab/show/Diaconescu%27s+theorem
 nLab：       https://ncatlab.org/nlab/show/split+epimorphism
 Wikipedia：  https://en.wikipedia.org/wiki/Diaconescu%27s_theorem
 Wikipedia：  https://en.wikipedia.org/wiki/Axiom_of_choice

 Mac Lane，CWM 第二版，§I.5 练习 7 在其后半部分要求，每个具有非空定义域的 Set 箭头的正规性。Instance/FinSet/Regular.v 通过可执行的有限搜索在 FinSet 上解决了这个问题。该文件衡量同样的陈述在 [Sets]——库的集合类范畴上需要的代价，而测量结果并没有像该练习的经典解释所建议的那样。经典叙述。固定 f : A → B 且 A 中存在 a₀。伪逆必须在纤维 f⁻¹(b) 非空时将 B 的每个 b 映射到该纤维中的某个元素，当纤维为空时则可以映射到任意位置（例如 a₀）。f 的数据中没有任何东西可以选择纤维元素，因此经典构造会同时为像中的每个 b 选择一个元素：这是在纤维族上应用选择公理的一个实例。将正规性见证回溯则不依赖选择，并且是 Theory/Morphisms.v 中的 [regular_epic_retraction] / [regular_monic_section]。原则在这里的代价是什么。在这个库的环境逻辑中，这种说法低估了代价，而且幅度很大。这个通用原则比任何现有的选择公理都要强：它决定每一个命题。下面的 [blanket_regularity_entails_LEM] 在无公理的情况下，从 [BlanketRegularity] 推导出了类型值的排中律 ∀ P : Prop, P + (P → False)；而 [blanket_splitting_entails_LEM] 从更弱的原则 [BlanketSplitting] 推导出了完全相同的结论，“每一个有已知域的满射都可拆分”，这就是 nLab 页面关于分裂满射所记录的作为选择范畴表述的内部选择公理。Coq 的环境逻辑是直觉主义的，既不能证明这两个结论，所以在这个开发中没有可用的原则，而且练习的后半部分在有限情况就停止是有原因的。反模型。取 Coq 的 `=` 作为 A 的 bool，再取 bool 作为 B，但只有当 P 成立时，这两个布尔值才完全相等（见下文 [sets_coarse]）；A 由 [true] 构成，并且载体上的恒等映射是 [Sets] 到较粗集体 ([sets_coarsen]) 的态射，因为它只需要让事物更相等。伪逆 g 仍然是 [Sets] 态射，因此 P 强制 g true = g false；在两个布尔值上读取正则性方程得到 (g b = b) + P；左边的两个答案强制 P → False，而右边的任何答案直接得到 P。这就是 [sets_coarsen_regular_dec]，它的逆命题 [sets_coarsen_regular_of_dec] 也成立，因此 [Sets] 的这个唯一箭头的正则性恰好是 P 的可判定性 ([sets_coarsen_regular_iff_dec])。为什么选择不能作为衡量标准。选择公理无法提供这些原理，因为 Coq 的选择公理不会决定命题。标准库自行公理化了关系选择，没有任何经典逻辑的导入（Stdlib.Logic.RelationalChoice）；产生排中律的模块是 Stdlib.Logic.ClassicalChoice，它通过重新导出 Stdlib.Logic.ClassicalUniqueChoice 来产生排中律，而后者又重新导出 Stdlib.Logic.Classical —— 那里的排中律是直接导入的，而不是从选择中提取的。上面的反例模型依赖的是SETOID的表述：对setoid的选择就是选择的外延公理，而Stdlib.Logic.SetoidChoice记录了它分解为经典逻辑、关系选择、唯一选择以及有限功能外延的过程，引用了Carlström的论述，“EM + Ext_ + AC_int等价于AC_ext”（《数学逻辑季刊》50(3), 2004, 第236-240页）。在该分解中的经典逻辑正是下面定理所恢复的，而恢复它的论证具有Diaconescu的形式：一个被命题粗化的两元素对象，对其选择一个代表会决定该命题（Diaconescu，“选择公理与补集”，《美国数学学会会议录》51, 1975, 第176-178页；nLab，“Diaconescu定理”，检索于2026-08）。一个集合等价类库提供了参数所需的类似商对象而无需额外成本，这就是为什么代价在这里支付，而不是由标准库的内涵选择公理支付的原因。保持真实的内容。以上没有任何内容反驳  [Sets] 的任何特定箭头的规律性，这本身也是一个定理，而不是遗漏：
 [sets_coarsen_not_regular_absurd]  反驳了  [sets_coarsen] 的非规律性，因此不存在证明该箭头不规律的证据——
 即使在  [sets_coarse_const] 将一个箭头放入反向同态集合且 [true] 存在于该域的情况下也是如此。因此，在  [Sets] 上，一个具有已存在域的箭头既不能被证明是规律的，也不能被证明是不规律的，这就是为什么针对规律性的树内反驳（在 Instance/Two.v 的 [TwoXY_not_regular]、在 Instance/FinSet/Regular.v 的 [finset_empty_to_one_not_regular]）都通过展示空的反向同态集合来实现的。那种形态是被迫形成的，而非出于方便选择的。
*)

(* ------------------------------------------------------------------------ *)
(* * ** The countermodel: bool coarsened by a proposition / * ** 反例模型：被命题粗化的布尔值 *)

Section Coarsening.

Context (P : Prop).

(*
 Two booleans count as equal when they are equal, or when P holds.  The
 relation is [Type]-valued, as every hom-setoid relation in this library is
 ([crelation], Lib/Setoid.v), so a proof of it can be taken apart by
 [destruct] into the informative case distinction the theorems below run
 on. 

 --------
 当两个布尔值相等时，或者当 P 成立时，它们算作相等。这个关系是 [Type] 值的，就像这个库中的每个同集合关系 ([crelation]，Lib/Setoid.v) 一样，因此它的证明可以被 [destruct] 拆解为下面定理所运行的有信息的情况区分。
*)
Definition sets_coarse_equiv (b b' : bool) : Type := ((b = b') + P)%type.

Program Definition sets_coarse_setoid : Setoid bool := {|
  equiv := sets_coarse_equiv
|}.
Next Obligation.
  constructor; repeat intro.
  - left; reflexivity.
  - destruct X; [ left; now symmetry | now right ].
  - destruct X; destruct X0; try (now right).
    left; now transitivity y.
Qed.

Definition sets_coarse : SetoidObject :=
  {| carrier := bool ; is_setoid := sets_coarse_setoid |}.

(*
 The identity on carriers, read as an arrow into the coarser setoid.  It
 respects the equivalences because it only ever has to make things MORE
 equal.  Its domain is [bool_setoid_object] (Instance/Sets.v), which is
 inhabited by [true], so the blanket principle applies to it. 

 --------
 在承载体上的恒等映射，可以理解为指向较粗的集合类的箭头。它遵守等价关系，因为它总是只需要使事物变得更相等。它的定义域是 [bool_setoid_object]（Instance/Sets.v），该域被 [true] 占据，因此通用原理适用于它。
*)
Program Definition sets_coarsen : bool_setoid_object ~{Sets}~> sets_coarse := {|
  morphism := fun b : bool => b
|}.

(*
 The reverse hom-set is inhabited: a constant map respects any pair of
 equivalences.  This is what keeps the theorems below from being about an
 empty hom-set, which is how the tree's other non-regularity results
 work. 

 --------
 反向同态集是可充满的：一个常量映射尊重任何一对等价关系。这就是下面定理不涉及空同态集的原因，而树的其他非规整性结果就是这样工作的。
*)
Program Definition sets_coarse_const :
  sets_coarse ~{Sets}~> bool_setoid_object := {|
  morphism := fun _ : bool => true
|}.

(*
 When P is refuted, the identity on carriers runs BACK as well: the
 coarsening added nothing. 

 --------
 当 P 被反驳时，载体上的同一性也会回退：所增加的粗化毫无用处。
*)
Program Definition sets_coarse_sharpen (np : P → False) :
  sets_coarse ~{Sets}~> bool_setoid_object := {|
  morphism := fun b : bool => b
|}.
Next Obligation.
  repeat intro.
  destruct X as [E | p]; [ exact E | now contradiction np ].
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Regularity of this one arrow is decidability of P / * ** 这个箭头的规律性是 P 的可判定性 *)

(*
 Forwards.  A pseudoinverse g satisfies (g b = b) + P at each of the two
 booleans.  If it answers on the left at both then g true = true and
 g false = false, while P would force g true = g false through g's own
 respectfulness; so P is refuted.  If it answers on the right anywhere, P
 is handed over directly. 

 --------
 前进。伪逆 g 在两个布尔值的每一个上都满足 (g b = b) + P。如果它在两个上都在左边给出答案，那么 g true = true 且 g false = false，而 P 会通过 g 自身的尊重性强制 g true = g false；因此 P 被反驳。如果它在任何地方在右边给出答案，则 P 会被直接交出。
*)
Lemma sets_coarsen_regular_dec :
  RegularMorphism sets_coarsen → (P + (P → False))%type.
Proof.
  intros [g Hg].
  destruct (Hg true)  as [Et | p]; [| exact (inl p) ].
  destruct (Hg false) as [Ef | p]; [| exact (inl p) ].
  right; intro p.
  assert (Hgg : g true = g false)
    by (apply (proper_morphism g); right; exact p).
  simpl in Et, Ef.
  rewrite Et, Ef in Hgg.
  discriminate.
Qed.

(*
 Backwards, by cases on the decision.  If P holds, everything in the
 codomain is equivalent to everything else and any arrow back will do; if P
 is refuted, the coarsening is invisible and the identity on carriers is a
 two-sided inverse. 

 --------
 反过来，根据决策的情况。如果 P 成立，值域中的所有东西都相互等价，任何箭头返回都可以；如果 P 被否定，粗化是不可见的，并且载体上的恒等映射是一个双边逆。
*)
Definition sets_coarsen_regular_of_dec :
  (P + (P → False))%type → RegularMorphism sets_coarsen.
Proof.
  intros [p | np].
  - exists sets_coarse_const.
    intro b; simpl; unfold sets_coarse_equiv.
    now right.
  - exists (sets_coarse_sharpen np).
    intro b; simpl; unfold sets_coarse_equiv.
    now left.
Defined.

(*
 So the two are equivalent, and the regularity of a single named arrow of
 [Sets] is neither more nor less than the decidability of an arbitrary
 proposition. 

 --------
 所以这两者是等价的，[Sets] 的单个命名箭头的规律性既不多也不少于任意命题的可判定性。
*)
Definition sets_coarsen_regular_iff_dec :
  RegularMorphism sets_coarsen ↔ (P + (P → False))%type :=
  (sets_coarsen_regular_dec, sets_coarsen_regular_of_dec).

(*
 It is epic outright: the identity on carriers is right-cancellable because
 two arrows out of the coarse setoid that agree after it already agree
 pointwise. 

 --------
 这简直是史诗级的：载体上的恒等映射是右可消的，因为从粗等价集合出的两个箭头在它之后已经逐点相同，它们也已经逐点相同。
*)
Lemma sets_coarsen_epic : Epic sets_coarsen.
Proof. constructor; intros Z g1 g2 H b; exact (H b). Qed.

(*
 Hence a splitting of it would decide P too, through
 [regular_of_retraction]: a right inverse is in particular a
 pseudoinverse. 

 --------
 因此，通过 [regular_of_retraction] 对它的分解也将决定 P：一个右逆特别是一个伪逆。
*)
Lemma sets_coarsen_retraction_dec :
  Retraction sets_coarsen → (P + (P → False))%type.
Proof.
  intro R.
  exact (sets_coarsen_regular_dec (regular_of_retraction _ R)).
Qed.

(*
 And non-regularity is not merely unproven but refutable: if regularity led
 to a contradiction then P would be refuted, P alone being enough to build a
 pseudoinverse, and a refutation of P builds one as well.  This is the
 precise sense in which an arrow of [Sets] with inhabited domain cannot be
 shown non-regular. 

 --------
 而非规则性不仅是未被证明的，而且是可以被反驳的：如果规则性导致矛盾，那么 P 将被反驳，仅 P 本身就足以构建一个伪逆，而对 P 的反驳也同样可以构建一个伪逆。这正是 [Sets] 的一个源于非空域的箭头无法被证明为非规则的确切意义。
*)
Lemma sets_coarsen_not_regular_absurd :
  (RegularMorphism sets_coarsen → False) → False.
Proof.
  intro H.
  apply H, sets_coarsen_regular_of_dec.
  right; intro p.
  exact (H (sets_coarsen_regular_of_dec (inl p))).
Qed.

End Coarsening.

(* ------------------------------------------------------------------------ *)
(* * ** The two blanket principles, and what each entails / * ** 两个总体原则，以及每个原则所包含的内容 *)

(*
 The statement Mac Lane's exercise makes about Set, transcribed for [Sets]:
 every arrow whose domain is inhabited -- inhabitation taken as DATA, an
 actual element, which is what "nonempty" means constructively -- is
 regular. 

 --------
 Mac Lane的练习对Set所做的陈述，转录给[Sets]：每一个其定义域非空的箭头——非空被视为数据，即一个实际元素，这在构造意义上就是“非空”的意思——都是正则的。
*)
Definition BlanketRegularity : Type :=
  ∀ (A B : SetoidObject) (a0 : carrier A) (f : A ~{Sets}~> B),
    RegularMorphism f.

(*
 The internal axiom of choice in the same restricted form: every
 epimorphism whose domain is inhabited splits.  The nLab page on split
 epimorphisms records that the axiom of choice internal to a category may
 be phrased as "all epimorphisms are split" and that "In Set this is
 equivalent to the usual axiom of choice" (retrieved 2026-08). 

 --------
 相同受限形式下的内部选择公理：每一个定义域非空的满射都是可分的。nLab 关于可分满射的页面记录了内部于范畴的选择公理可以表述为“所有满射都是可分的”，并且“在集合范畴中，这等价于通常的选择公理”（检索于 2026-08）。
*)
Definition BlanketSplitting : Type :=
  ∀ (A B : SetoidObject) (a0 : carrier A) (f : A ~{Sets}~> B),
    Epic f → Retraction f.

(*
 The implication between them, as a statement of Coq rather than as prose:
 [regular_epic_retraction] applied under both quantifiers.  This is the
 step Instance/FinSet/Regular.v's header describes, and it is one line. 

 --------
 它们之间的蕴含，作为 Coq 的一个陈述而不是散文：
 [regular_epic_retraction] 在两个量词下应用。这是步骤 Instance/FinSet/Regular.v 的头部所描述的，并且它就是一行。
*)
Definition blanket_regularity_entails_splitting :
  BlanketRegularity → BlanketSplitting :=
  fun HR A B a0 f E => regular_epic_retraction f (HR A B a0 f) E.

(*
 The internal choice principle decides every proposition, by the
 countermodel: [sets_coarsen] is epic with inhabited domain, so the
 principle splits it, and a splitting is a pseudoinverse. 

 --------
 内部选择原理决定每一个命题，通过反例模型：[sets_coarsen] 在有非空域的情况下是史诗性的，所以该原理将其分裂，而一个分裂是伪逆。
*)
Theorem blanket_splitting_entails_LEM :
  BlanketSplitting → ∀ P : Prop, (P + (P → False))%type.
Proof.
  intros HS P.
  exact (sets_coarsen_retraction_dec P
           (HS bool_setoid_object (sets_coarse P) true
              (sets_coarsen P) (sets_coarsen_epic P))).
Qed.

(*
 And so does the regularity principle, which implies the splitting one.
 Proved twice over: directly from the countermodel, and -- as
 [blanket_regularity_entails_splitting] composed with
 [blanket_splitting_entails_LEM] -- through the splitting principle, which
 is the route the FinSet header describes in prose. 

 --------
 正则性原理也是如此，它暗示了分裂原理。已经被证明两次：一次是直接从反例模型证明，另一次是——通过将 [blanket_regularity_entails_splitting] 与 [blanket_splitting_entails_LEM] 组合 ——通过分裂原理证明，这正是 FinSet 头文件在文字中描述的方法。
*)
Theorem blanket_regularity_entails_LEM :
  BlanketRegularity → ∀ P : Prop, (P + (P → False))%type.
Proof.
  intros HR P.
  exact (sets_coarsen_regular_dec P
           (HR bool_setoid_object (sets_coarse P) true (sets_coarsen P))).
Qed.

Definition blanket_regularity_entails_LEM_via_splitting :
  BlanketRegularity → ∀ P : Prop, (P + (P → False))%type :=
  fun HR => blanket_splitting_entails_LEM
              (blanket_regularity_entails_splitting HR).
