(* * * (R-Mod, ⊗, R) is symmetric monoidal CLOSED: the tensor-hom adjunction / * * (R-模, ⊗, R) 是对称幺半闭的：张量-同构伴随 *)

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §IV.1, printed p. 80 — the hom-set form of an adjunction, of
 which “⊗ is left adjoint to Hom” is the running example.
 Book:      Mac Lane, ibid., §IV.6, printed p. 98 — the tensor-hom
 adjunction proper: for a commutative ring R the bijection
 Hom(V ⊗ W, X) ≅ Hom(V, Hom(W, X)), natural in all three
 variables.
 nLab:      https://ncatlab.org/nlab/show/tensor-hom+adjunction
 nLab:      https://ncatlab.org/nlab/show/closed+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Tensor-hom_adjunction

 Instance/Mod/Monoidal.v supplied the ⊗ half — the bifunctor [ModTensor],
 the unitors, the associator, both coherence laws, the braiding and the
 symmetry.  Its own header says in terms that the closed structure is a
 companion file's business (Instance/Mod/Monoidal.v):

 “NO CLOSED STRUCTURE.  The internal hom, the tensor-hom adjunction
 and any [SymMonClosed] instance are a companion file's business,
 not this one's; nothing here mentions an exponent.”

 This file is that companion.  Delivered:

 - [HomMod V W], the internal hom: the module of R-linear maps V ⟶ W
 - [hm_curry] / [hm_uncurry] with BOTH round trips
 - [exp_iso_Mod], the bijection as an isomorphism of hom-setoids in
 [Sets]; [eval_Mod], evaluation; [ump_exponents_Mod], the universal
 property in existence-and-uniqueness form
 - **[RMod_SymMonClosed]**, the headline: an inhabitant of
 Structure/Monoidal/StarAutonomous.v's [SymMonClosed] class, whose
 underlying symmetric monoidal structure IS Monoidal.v's
 [ModSymmetric]
 - [ihom_post] / [ihom_pre], the internal hom's two arrow actions, and
 the SIX naturality squares — three variables, each read through the
 forward leg and through the backward leg

 COMMUTATIVITY, AND WHERE IT IS SPENT.  Everything is stated over an
 arbitrary [RingObject] together with an explicit commutativity
 hypothesis, the same proposition after elaboration as Instance/Rng.v's
 [CRng_Sub] predicate so that an object of [CRng] supplies it by
 projection and Instance/Rng.v's [Int_Ring_commutative] discharges it
 at ℤ:

 Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
 rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

 Commutativity is spent in EXACTLY ONE PROOF, [hm_smul_linear]: the claim
 that r · φ is still LINEAR when φ is.  Unfolded, (r·φ)(s·v) is
 r · (s · φ v) and linearity demands s · (r · φ v); [Rcomm] is what turns
 one into the other, and nothing else in the file reaches for it.

 THAT IS MACHINE-MEASURED, NOT ASSERTED.  Lib.v sets
 [Default Proof Using “Type”], which keeps only the section variables a
 lemma's STATEMENT mentions.  [Rcomm] appears in no statement in
 Section [InternalHom] — so the build DEMANDS the annotation
 `Proof using R Rcomm` on [hm_smul_linear] and rejects it on none of its
 siblings.  The annotation is kept for that reason and must not be
 removed; deleting it makes the file fail at that lemma's [Qed] with

 The following section variable is used but not declared: Rcomm.

 The instrument is also readable from OUTSIDE the proof, and the probe
 section at the end pins it as a TYPING negative: [hm_smul_linear] takes
 [Rcomm] as an ARGUMENT, so `@hm_smul_linear R V W r f` is ill-typed,
 while `@hm_smul_zero R V W r f` and `@hm_smul_plus R V W r f` — the two
 siblings, same section, same statement shape — elaborate.

 A FINER MEASUREMENT THE HEADER WOULD OTHERWISE MISS.  [Rcomm] is needed
 only to make the linear maps into an OBJECT of [RMod R].  Currying
 itself is commutativity-free, and that is visible in the signatures the
 same instrument produces: [cur_fun R {V W X} f v w] and
 [cur_at R {V W X} f v] — the map w ↦ f (v ⊗ w) together with the proof
 that it is a module homomorphism W ⟶ X — take NO [Rcomm].  Only
 [hm_curry], whose codomain is [HomMod], does.

 PRIOR ART, AND [HomMod] IS NOT A FIRST SIGHTING.  Instance/FdVect/
 DoubleDual.v's [DualMod] is ALREADY the W := R case of this internal
 hom.  That is an identification, not an analogy: its carrier
 (DoubleDual.v, the carrier field of [DualMod]'s record) is
 `RModHom V (Ring_RMod (field_ring F))`, which is
 [hm_setoid]'s carrier at W := Ring_RMod; and since Instance/Mod.v's
 [Ring_RMod] has `rm_smul := rig_mul (ring_rig R)` and
 `rm_smul_assoc := rig_mul_assoc`, its scalar action r · φ is this file's
 pointwise action on the nose, its [dual_smul_linear] (DoubleDual.v)
 is [hm_smul_linear] with the same three rewrites in the same order, and
 its own header at DoubleDual.v already localises “the one use of
 commutativity” to exactly that lemma.  So [HomMod] GENERALISES an
 existing construction in two independent directions — an arbitrary
 target module W in place of the base ring, and an arbitrary
 [RingObject] with an explicit [Rcomm] in place of a [FieldObject] — and
 the localisation of commutativity is INHERITED rather than discovered.
 What is new here is the tensor-hom adjunction over it, which
 DoubleDual.v does not have (its own header, DoubleDual.v, records
 that the library then had no monoidal structure to state it against).

 NO BRAID IS NEEDED, AND THAT IS A FACT ABOUT THE CLASS'S ORIENTATION.
 Structure/Monoidal/StarAutonomous.v declares

 exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z

 with `eval' {x y} : (x ⇒ y) ⨂ x ~> y`.  Read at x := V, y := W,
 z := X this is Hom(V ⊗ W, X) ≅ Hom(V, Hom(W, X)), which is the module
 theorist's own statement, and evaluation puts the internal hom on the
 LEFT of the tensor — so [uncur_bilinear]'s underlying map is the
 two-variable (φ, w) ↦ φ w with its arguments already in the order the
 class wants.  Had the class put the internal hom on the right, or had
 the tensor's variance run the other way, the symmetry [ModBraid] would
 have had to be inserted; here it is not, and no [ModBraid] occurs
 anywhere below.  (The symmetry is still present in the STRUCTURE — it
 is what [smc_is_symmetric] carries — it is simply not consumed by the
 adjunction.)

 NATURALITY IN THREE VARIABLES, AND THE ASYMMETRY BETWEEN THE TWO LEGS.
 Each of the three squares is stated twice, once through the forward leg
 [hm_curry] and once through the backward leg [hm_uncurry], because the
 two cost different things and reporting only one would misdescribe the
 result.

 FORWARD ([cur_natural_V], [cur_natural_W], [cur_natural_X]): each is
 `Proof. intros v w; reflexivity. Qed.` — the two sides are pointwise
 the SAME TERM.  Currying is definitional on generators, and
 [mt_fmap] computes there, so there is nothing to prove.

 BACKWARD ([unc_natural_V], [unc_natural_W], [unc_natural_X]): each
 needs one application of [tensor_hom_ext] and then [reflexivity].
 [hm_uncurry] is a [tensor_med], i.e. a [Fixpoint] over [MTerm]; two
 such recursions are pointwise equal at every generator but are not
 the same term at a variable tensor, so extensionality is what closes
 the gap.

 BOTH DIRECTIONS MATTER.  The forward triviality on its own could be
 mistaken for the naturality statement being vacuous; the backward
 squares show it is not — they are true, they are not conversions, and
 the probe section pins the failed strict form of one of them beside its
 generator-level control, so the difference is machine-checked rather
 than described.

 ONE CORRECTION TO THE ROUTE, AND IT MADE EVERY PROOF CHEAPER.
 Instance/Mod/Tensor.v exposes the mediator twice: [tensor_med],
 whose generator equation is `eq_refl`, and [tensor_factor],
 a bare alias for it (`tensor_factor β = tensor_med β` by
 `eq_refl`) whose companion [tensor_factor_commutes] is a `Qed`
 lemma stating an `≈`.  Routing through the second makes every step
 opaque; this file uses the first throughout.  The consequences are
 measured below rather than claimed:

 - [hm_uncurry_gen] holds at LEIBNIZ `=` by `eq_refl` (the uncurried
 map's value at a generator IS φ applied to the argument);
 - [hm_curry_uncurry] is `Proof. intros v w; reflexivity. Qed.`;
 - [hm_uncurry_curry] is one [tensor_hom_ext] then `reflexivity`;
 - [eval_Mod_gen] holds at Leibniz `=` by `eq_refl`;
 - [ump_uniq] is a one-line `exact (Hh (mt_gen v w))` — no chain;
 - the three backward naturality squares need [tensor_hom_ext] and
 NOTHING ELSE.

 THE JOIN WITH Instance/Mod/Monoidal.v, AND ONE MISMATCH CHECKED RATHER
 THAN ASSUMED.  The tensor's action on arrows is that file's [mt_fmap],
 not a second copy: [mt_fmap] is `tensor_med (mt_bimap f g)` where
 [mt_bimap]'s underlying map is (v, w) ↦ mval f v ⊗ mval g w, and
 [ModTensor]'s `fmap` is `fun p q fg => mt_fmap (fst fg) (snd fg)`, so
 `bimap h id` reduces to `mt_fmap h id` by iota.  That is checked, not
 supposed: [smc_bimap] below records it at `eq_refl`, together with
 [smc_tensor] recording `fobj[tensor] (V, W) = TensorMod V W`.

 HOW THE FIELDS SLOT IN.  Every one of [SymMonClosed]'s four explicit
 fields is filled by `:=` with NO tactic and NO transport, and the three
 DEFINED fields — [curry'], [uncurry'], [eval'], which the class supplies
 with bodies rather than taking as arguments — return this file's own
 constants at `eq_refl`: [smc_curry], [smc_uncurry], [smc_eval].  So
 `eval'` is [eval_Mod] on the nose, and a consumer who reaches for the
 class's vocabulary gets the terms proved about here rather than an
 opaque repackaging.

 WHAT THE INSTANCE IS THE FIRST OF, STATED AT THE STRENGTH IT IS
 MEASURED.  A whole-tree sweep for the token [SymMonClosed] AT THE PARENT
 COMMIT — before this file and its sibling existed — returns six files:
 the class's own (Structure/Monoidal/StarAutonomous.v), three that take it
 as a HYPOTHESIS (Structure/Monoidal/Dual.v, Test/ProbeDual359.v,
 Structure/Closed.v's prose), and two comment mentions
 (Instance/FdVect/DoubleDual.v, Structure/Monoidal/Symmetric.v).
 The revision matters: sweeping at THIS commit returns eight, the two
 extra being this file and Instance/Mod/Monoidal.v, so a sweep that names
 a sibling introduced by the same commit is reporting its own arrival.
 None of the six declares an inhabitant, and
 Structure/Monoidal/Dual.v says
 so in its own words: “Nothing here exhibits a [SymMonClosed] instance,
 so every result is a conditional”.  [RMod_SymMonClosed] is therefore the
 first.  The sibling class [ClosedMonoidal] has exactly one inhabitant,
 Instance/Coq.v's [Coq_ClosedMonoidal], which is
 `CCC_ClosedMonoidal` and so cartesian by construction.

 MEASUREMENTS RECORDED.  93/93 constants closed under the global context
 — the count is [Print Module]'s, which lists 61 source-declared names
 together with the 32 [Program] obligations no source sweep sees, and the
 file declares no [Record], [Class] or [Inductive], so there is no
 unlisted [Build_*].  ([Print Module] wraps the module name onto its own
 line, so split its output on `:= Struct` rather than on the header, and
 count DISTINCT names rather than occurrences.)  Read the GRADE: that is
 a ONE-TIME measurement, not a standing gate.  The commit that lands this
 file registers it in `_CoqProject` and puts fifteen of its constants
 into the `print-assumptions` target; the other 78 were measured once, by
 hand.  With Instance/Mod/Monoidal.v's 123 that is 216 across the pair,
 and the 112 source-declared names of the two together collide with
 nothing in tree.

 RE-MEASURED after the PR “algebraic carriers are sets” (2026-09-17),
 the same way: [Print Module] gives 93 entries here and 123 for
 Instance/Mod/Monoidal.v, of which 32 and 72 respectively are
 [_obligation_] names, leaving 61 + 51 = 112 source-declared; and one
 [Print Assumptions] per name gives 93 “Closed under the global
 context” with zero [Axioms:] blocks.  EVERY FIGURE IN THIS PARAGRAPH
 REPRODUCES UNCHANGED.  The collision sweep was not re-run.

 WHAT IS NOT THEREBY CLAIMED.  This file does NOT prove that ⊗ is not a
 categorical product in [RMod R], so “the first non-cartesian closed
 monoidal witness” is NOT established here.  The obstacle is concrete
 rather than rhetorical: Instance/Mod/Coproduct.v registers
 [RMod_Cartesian], so [RMod R] genuinely has products, and separating
 them from ⊗ would need a rank argument (over ℤ, Instance/Mod/Tensor.v's
 [Int_tensor_iso] gives ℤ ⊗ ℤ ≅ ℤ, and one would then have to refute
 ℤ ≅ ℤ × ℤ).  What IS true and measured is the weaker pair of facts in
 the preceding paragraph.

 UNIVERSES, MEASURED OFF BOTH THE BINDER AND THE BLOCK.  The headline's
 constraint block contains NO equation — `RMod_SymMonClosed@{u u0}` has
 `u0 < u` and bounds — while its BINDER reads `R : RingObject@{u0 u0 u0}`,
 all three of the ring's universes identified by reuse of one level
 variable.  Reading the block alone reports no identification and is
 wrong; this is the trap the tree records at Instance/Mod/Monoidal.v and
 at Structure/Ring.v's [dup_left].  The identification is INHERITED and
 the probe section localises it:

 FREE at `R : RingObject@{rc ra rb}` with `ra < rc` declared —
 [RMod], [TensorMod], [tensor_gen], [HomMod], [ihom_post],
 [tensor_med], [mt_fmap], [hm_curry];
 REJECTED there — [ModSymmetric], [RMod_SymMonClosed].

 AN EARLIER REVISION of those two lines put [tensor_med] (the donor,
 Instance/Mod/Tensor.v), [mt_fmap] and [hm_curry] on the REJECTED
 side, and concluded “So [tensor_med] is A donor, rejected ALONE with
 [TensorMod] and [tensor_gen] accepted at the very same levels”.  All
 three were re-measured after the PR “algebraic carriers are sets”
 (2026-09-17) and all three are now free: moving [mt_eq] to [Prop] means
 [tensor_med_respects] runs through [pequiv] instead of inducting on a
 [Type]-valued relation into a [Type]-valued goal, and the identification
 that induction forced is gone.  What survives is that the headline
 [RMod_SymMonClosed] still carries it, through [ModSymmetric]; the
 remaining donor is therefore upstream of this file, in
 Instance/Mod/Monoidal.v.  Nothing was repaired deliberately -- the
 improvement is a side effect -- and the position of the ring's three
 universes also moved: the record's auxiliary level is now the FIRST
 argument rather than the third, which is why the binder reads
 `RingObject@{rc ra rb}` and not `RingObject@{ra rb rc}`.

 A SECOND, INDEPENDENT OBSERVATION, AND IT LOCALISES THE OTHER HALF —
 NOT IN THIS FILE.  The two identifications a [RingObject@{a b c}] can
 acquire here are FIRST=THIRD and FIRST=SECOND, and they come from
 different places.  The first is what the probe section above pins.  The
 second is NOT the closed half's: [tensor_med] and every ingredient of
 [hm_curry] — [cur_fun], [cur_at], [cur_at_smul], [cur_out_zero],
 [cur_out_plus], [cur_out_smul] — read `RingObject@{a b a}`, and so,
 measured rather than assumed, do [hm_curry] itself and its [Program]
 obligation [hm_curry_obligation_1].  So no constant this file declares
 identifies the first two.
 The equation `u = u0` visible in [RMod_SymMonClosed]'s BINDER is
 therefore inherited whole from Instance/Mod/Monoidal.v's [ModMonoidal],
 which that file's header localises to its own packaging, and the probe
 section below guards the split: under a declared `Constraint rb < ra` —
 which violates FIRST=SECOND while leaving FIRST=THIRD alone —
 [hm_curry], [HomMod], [exp_iso_Mod] and [ump_exponents_Mod] all
 elaborate, while [ModMonoidal], [ModSymmetric] and the headline
 [RMod_SymMonClosed] are all rejected.  Read the constraint BLOCK
 flattened when checking this: [Print] wraps it, and the equations that
 matter here sit past the first line.  Nothing is repaired and nothing
 is claimed unavoidable.

 WHAT IS NOT DELIVERED.

 - No proof that ⊗ is not the categorical product of [RMod R], hence
 no claim of a first non-cartesian witness (see above).
 - No [StarAutonomous] instance.  [RMod R] has no dualizing object in
 tree and none is sought; the file supplies what
 Structure/Monoidal/Dual.v needs as a HYPOTHESIS and stops there.
 - No [Adjunction] record.  The bijection is delivered as an
 isomorphism of hom-setoids in [Sets], naturally in each variable
 separately; it is NOT packaged as `− ⊗ W ⊣ HomMod W −` in
 Theory/Adjunction.v's shape, and no functor `RMod R ⟶ RMod R` for
 either side is built.
 - Consequently no unit, no counit, and no triangle identities; and
 nothing about preservation of colimits by − ⊗ W.
 - No enriched reading: [RMod R] is not exhibited as enriched over
 itself, and [HomMod] is not related to Construction/Enriched.v.
 - No bifunctoriality of [HomMod].  [ihom_post] and [ihom_pre] are its
 two arrow actions and are proved natural where used, but they are
 not assembled into `(RMod R)^op ∏ RMod R ⟶ RMod R`, so the six
 squares are lemmas about arrows rather than about a bifunctor.
 - No naturality in the RING, and no interaction with
 Instance/Rng/Mod.v's restriction of scalars.
 - No non-commutative variant.  Over a general R the correct statement
 is a bimodule one; nothing here approaches it, and the file does
 not exhibit a ring where the construction FAILS.
 - No relation to Instance/Ab/Monoidal.v at R = ℤ (an earlier revision
 added “the ℤ-module structure of an [AbObject] is not in tree”; since
 #454 it is, as Instance/Mod/Cogenerator.v's [Ab_to_ZMod], and the
 relation is still not built), and no relation to
 Instance/Mod/Free.v's free module or to
 Instance/FdVect/DoubleDual.v's dual functor beyond the prose
 identification above.
 - No universe repair; the identification is measured and pinned, not
 lifted, and nothing here is annotated.
 - No [Instance] registration.  Like Instance/Mod/Monoidal.v's three
 structures, [RMod_SymMonClosed] is a plain [Definition]: registering
 it would leave typeclass resolution an unsolvable commutativity
 subgoal at an abstract ring. 

 --------
 书籍：Mac Lane，《为在职数学家准备的范畴》(第2版)，§IV.1，第80页——伴随函数的Hom集合形式，其中“⊗ 是 Hom 的左伴随”是贯穿示例。
 书籍：Mac Lane，同上，§IV.6，第98页——张量-Hom 伴随的正确定义：对于一个交换环 R，有一个自然双射 Hom(V ⊗ W, X) ≅ Hom(V, Hom(W, X))，自然性在三个变量中都成立。
 nLab：https://ncatlab.org/nlab/show/tensor-hom+adjunction
 nLab：https://ncatlab.org/nlab/show/closed+monoidal+category
 维基百科：https://en.wikipedia.org/wiki/Tensor-hom_adjunction

 Instance/Mod/Monoidal.v 提供了 ⊗ 部分——二元函子 [ModTensor]、单位子、结合子、两个一致性律、编织和对称。其自己的头文件指出，封闭结构是伴随文件 Instance/Mod/Monoidal.v 的工作。“没有封闭结构。内部 Hom、张量-Hom 对偶以及任何 [SymMonClosed] 实例都是伴随文件的事情，不属于这个文件；这里没有提到指数。”

 这个文件就是那个伴随文件。已交付：- [HomMod V W]，内部同：从 V 到 W 的 R 线性映射的模
 - [hm_curry] / [hm_uncurry]，具有双向往返
 - [exp_iso_Mod]，作为同态集异构的同构的双射在 [Sets] 中；[eval_Mod]，求值；[ump_exponents_Mod]，存在性和唯一性形式的泛性质
 - **[RMod_SymMonClosed]**，标题：Structure/Monoidal/StarAutonomous.v 中 [SymMonClosed] 类的一个元素，其底层对称单体结构是 Monoidal.v 的 [ModSymmetric]
 - [ihom_post] / [ihom_pre]，内部同的两个箭头作用，以及六个自然性方形 — 三个变量，每个分别通过前向和后向读交换律及其使用位置。一切内容均在任意的 [RingObject] 上陈述，并附带明确的交换律假设，经过详细阐述后的同一命题作为 Instance/Rng.v 的 [CRng_Sub] 谓词，以便 [CRng] 的对象通过投影提供它，而 Instance/Rng.v 的 [Int_Ring_commutative] 在 ℤ 上解除它：

 上下文 (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
 rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

 交换律只在唯一的一个证明中被使用，即 [hm_smul_linear]：当 φ 是线性映射时，r · φ 仍然是线性的声明。展开后，(r·φ)(s·v) 为 r · (s · φ v)，而线性要求为 s · (r · φ v)；[Rcomm] 则使前者变为后者，并且文件中没有其他地方引用它。那是机器测量的，而不是断言的。Lib.v 设置 [Default Proof Using “Type”]，它只保留引理的陈述中提到的部分变量。[Rcomm] 在 [InternalHom] 节的任何陈述中都未出现——因此构建要求在 [hm_smul_linear] 上添加注释 `Proof using R Rcomm`，而不拒绝对其任何同级元素的注释。出于这个原因保留该注释，且不得删除；删除它会导致该引理的 [Qed] 处文件出错，出现：

 以下部分变量已使用但未声明：Rcomm。

 该工具在证明之外也可读，并且在末尾的探测部分将其标记为类型判定为负：[hm_smul_linear] 以 [Rcomm] 作为参数，因此 `@hm_smul_linear R V W r f` 类型错误，而 `@hm_smul_zero R V W r f` 和 `@hm_smul_plus R V W r f` ——两个同级、同节、同样陈述形状——进行详细说明。一个更精细的测量，否则标题将会遗漏。[Rcomm] 只是为了将线性映射变成 [RMod R] 的一个对象。柯里化本身不受交换律影响，这在同一个工具产生的签名中是可见的：[cur_fun R {V W X} f v w] 和 [cur_at R {V W X} f v]——映射 w ↦ f (v ⊗ w) 以及证明它是一个从 W 到 X 的模同态——不需要 [Rcomm]。只有 [hm_curry]，其陪域是 [HomMod]，才需要。先前技术，并且 [HomMod] 并不是首次出现。Instance/FdVect/DoubleDual.v 的 [DualMod] 已经是该内部同态的 W := R 情况。这是一个识别，而不是类比：它的承载类型（DoubleDual.v，即 [DualMod] 记录的承载字段）是 `RModHom V (Ring_RMod (field_ring F))`，而这是 [hm_setoid] 在 W := Ring_RMod 时的承载类型；并且由于 Instance/Mod.v 的 [Ring_RMod] 拥有 `rm_smul := rig_mul (ring_rig R)` 和 `rm_smul_assoc := rig_mul_assoc`，其数标作用 r · φ 在本文件中正好对应逐点作用，其 [dual_smul_linear]（DoubleDual.v）是 [hm_smul_linear]，并且拥有相同顺序的三个重写，其在 DoubleDual.v 的头部已经将“交换律的唯一使用”限定到恰好那个引理。所以 [HomMod] 在两个独立方向上推广了现有的构造——用任意的目标模 W 代替基础环，以及用具有显式 [Rcomm] 的任意 [RingObject] 代替 [FieldObject]——并且交换性的局部化是继承而非发现的。这里的新内容是其上的张量-同构伴随（tensor-hom adjunction），DoubleDual.v 没有这个（它自己的头文件 DoubleDual.v 记录了当时库中没有单体结构来陈述它）。

 不需要编织（braid），这是关于该类朝向的一个事实。Structure/Monoidal/StarAutonomous.v 声明

 exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z使用 `eval' {x y} : (x ⇒ y) ⨂ x ~> y`。读取时 x := V, y := W, z := X，这是 Hom(V ⊗ W, X) ≅ Hom(V, Hom(W, X))，这是模理论者自己的表述，而评估将内部同态放在张量的左侧——所以 [uncur_bilinear] 的底层映射是双变量 (φ, w) ↦ φ w，其参数已经按类所需的顺序排列。如果类将内部同态放在右侧，或者张量的变换方向相反，则必须插入对称性 [ModBraid]；在这里不需要，而且在下面没有出现任何 [ModBraid]。（对称性仍然存在于结构中——它是由 [smc_is_symmetric] 承载——只是没有被伴随消耗。）三个变量的自然性，以及两条腿之间的不对称性。
 每三个平方各陈述两次，一次通过前腿 [hm_curry]，另一次通过后腿 [hm_uncurry]，因为这两者的代价不同，仅报告一个会错误描述结果。

 前向（[cur_natural_V]，[cur_natural_W]，[cur_natural_X]）：每一个都是 `Proof. intros v w; reflexivity. Qed.`——两边在每一点上都是相同的项。柯里化在生成元上是定义性的，而 [mt_fmap] 在那里进行计算，所以没有什么需要证明的。向后（[unc_natural_V], [unc_natural_W], [unc_natural_X]）：每个都需要先应用一次 [tensor_hom_ext]，然后应用 [reflexivity]。 [hm_uncurry] 是一个 [tensor_med]，即 [MTerm] 上的 [Fixpoint]；两个这样的递归在每个生成元处点对点相等，但在变量张量上不是相同的项，因此扩展性是弥合这种差距的方法。

 两个方向都很重要。仅凭正向的平凡性可能会被误认为自然性陈述是空的；向后的方阵表明情况并非如此——它们是真的，它们不是转换，并且探测部分将其中一个失败的严格形式放在其生成元级控制旁边，因此这种差异是机器检查的，而不是描述的。对路线的一次修正，使得每一个证明都更便宜。
 Instance/Mod/Tensor.v 将中介暴露了两次：[tensor_med]，其生成器方程是 `eq_refl`；还有 [tensor_factor]，它只是它的一个别名（通过 `eq_refl` 的 `tensor_factor β = tensor_med β`），它的伴随 [tensor_factor_commutes] 是一个 `Qed` 引理，说明了一个 `≈`。通过第二个路由会使每一步都变得不透明；这个文件在整个过程中使用第一个。其后果在下面进行衡量而不是声明：- [hm_uncurry_gen] 在 LEIBNIZ `=` 由 `eq_refl` 保持（未柯里化映射在一个生成元的值是 φ 应用于该参数）；
 - [hm_curry_uncurry] 是 `Proof. intros v w; reflexivity. Qed.`；
 - [hm_uncurry_curry] 是一个 [tensor_hom_ext] 然后 `reflexivity`；
 - [eval_Mod_gen] 在 Leibniz `=` 由 `eq_refl` 保持；
 - [ump_uniq] 是一行 `exact (Hh (mt_gen v w))` —— 没有链条；
 - 三个向后自然性方格需要 [tensor_hom_ext] 和 没有其他东西。与 Instance/Mod/Monoidal.v 的连接，以及检查而非假设的一个不匹配。张量在箭头上的作用是该文件的 [mt_fmap]，而不是第二份副本：[mt_fmap] 是 `tensor_med (mt_bimap f g)`，其中 [mt_bimap] 的基础映射是 (v, w) ↦ mval f v ⊗ mval g w，[ModTensor] 的 `fmap` 是 `fun p q fg => mt_fmap (fst fg) (snd fg)`，因此 `bimap h id` 通过 iota 化简为 `mt_fmap h id`。这是经过检查的，而非假设：下面的 [smc_bimap] 在 `eq_refl` 记录了它，同时 [smc_tensor] 记录了 `fobj [tensor]ZZ  (V, W) = TensorMod V W`。字段是如何插入的。[SymMonClosed] 的四个显式字段中的每一个都由 `:=` 填充，无需策略，也无需传输，而三个已定义的字段——[curry']、[uncurry']、[eval']，类提供了其实现而不是作为参数传入——在 `eq_refl` 返回这个文件自身的常量：[smc_curry]、[smc_uncurry]、[smc_eval]。因此 `eval'` 正好等于 [eval_Mod]，而使用该类词汇的调用者获取的是这里所证明的术语，而不是一个不透明的重新封装。实例是什么的第一个，在它被测量的强度下说明。对父提交进行整个树的扫描以查找标记 [SymMonClosed] ——在此文件及其同级文件存在之前—— 返回六个文件：该类本身的文件（Structure/Monoidal/StarAutonomous.v）、三个将其作为假设的文件（Structure/Monoidal/Dual.v、Test/ProbeDual359.v、Structure/Closed.v 的文本），以及两个注释提及（Instance/FdVect/DoubleDual.v、Structure/Monoidal/Symmetric.v）。修订版本很重要：在此提交上扫描返回八个文件，多出的两个是该文件和 Instance/Mod/Monoidal.v，因此扫描一个由同一提交引入的同级文件实际上是在报告它自己的出现。六个中没有一个声明了一个实例，而 Structure/Monoidal/Dual.v 用它自己的话说：“这里没有展示 [SymMonClosed] 的实例，所以每个结果都是条件的”。[RMod_SymMonClosed] 因此是第一个。兄弟类 [ClosedMonoidal] 恰好有一个实例，Instance/Coq.v 的 [Coq_ClosedMonoidal]，它是 `CCC_ClosedMonoidal`，因此按构造是笛卡尔的。已记录测量。93/93 常量在全局上下文下封闭 — 计数是 [Print Module] 个，其中列出了 61 个源声明的名称，以及 32 个 [Program] 义务，源扫描无法看到，并且该文件未声明 [Record]、[Class] 或 [Inductive]，因此不存在未列出的 [Build_*]。（[Print Module] 将模块名称换行到自己的行，所以在 `:= Struct` 上拆分其输出，而不是在标题上，并计算不同的名称而不是出现次数。）阅读 GRADE：这是一次性测量，而不是常设门控。提交该文件的提交会将其注册到 `_CoqProject`，并将其 15 个常量放入 `print-assumptions` 目标；其他 78 个常量由人工测量一次。在 Instance/Mod/Monoidal.v 的 123 个实例中，总共在这对中有 216 个，两个源声明的 112 个名称与树中没有任何冲突。

 在 PR “代数载体是集合”（2026-09-17）之后重新测量，方式相同：[Print Module] 在这里给出 93 个条目，在 Instance/Mod/Monoidal.v 中给出 123 个，其中分别有 32 和 72 个 [_obligation_] 名称，剩下 61 + 51 = 112 个源声明名称；每个名称一个 [Print Assumptions] 生成 93 个“在全局上下文下封闭”，没有 [Axioms:] 块。此段落中的所有数据都未更改。碰撞扫描没有重新运行。未因此而宣称。本文件并未证明 ⊗ 在 [RMod R] 中不是一个范畴积，因此“第一个非笛卡尔闭单体见证”并未在此确立。障碍是具体的而非修辞性的：Instance/Mod/Coproduct.v 注册了 [RMod_Cartesian]，因此 [RMod R] 确实有积，将它们与 ⊗ 区分开来需要一个秩论证（在 ℤ 上，Instance/Mod/Tensor.v 的 [Int_tensor_iso] 给出 ℤ ⊗ ℤ ≅ ℤ，之后还必须驳斥 ℤ ≅ ℤ × ℤ）。真正成立并被测量的是前一段中的较弱的两个事实。宇宙，分别从绑定器和块中测量。标题的约束块不包含方程——`RMod_SymMonClosed@{u u0}`有`u0 < u`和边界——而其绑定器读取`R : RingObject@{u0 u0 u0}`，环的三个宇宙都通过重复使用一个层次变量来标识。仅读取块不会报告任何标识，这是错误的；这是树在Instance/Mod/Monoidal.v和Structure/Ring.v的[dup_left]中记录的陷阱。标识是继承的，并且探针部分将其本地化：

 在`R : RingObject@{rc ra rb}`处为FREE，声明了`ra < rc`——[RMod], [TensorMod], [tensor_gen], [HomMod], [ihom_post], [tensor_med], [mt_fmap], [hm_curry]；
 在那里被拒绝——[ModSymmetric], [RMod_SymMonClosed]。这些两行的早期修订将 [tensor_med]（捐赠者，Instance/Mod/Tensor.v）、[mt_fmap] 和 [hm_curry] 放在拒绝一侧，并得出结论：“所以 [tensor_med] 是 A 捐赠者，独自被拒绝，而 [TensorMod] 和 [tensor_gen] 在完全相同的层次上被接受”。在PR “代数承载体是集合”（2026-09-17）之后，所有三个都重新测量，并且现在都自由了：将 [mt_eq] 移到 [Prop] 意味着 [tensor_med_respects] 将通过 [pequiv] 运行，而不是在 [Type] 值关系上进行归纳到 [Type] 值目标上，归纳所迫使的识别消失了。存留下来的情况是，标题 [RMod_SymMonClosed] 仍然通过 [ModSymmetric] 承载它；因此，剩下的捐赠者位于此文件的上游，在 Instance/Mod/Monoidal.v。没有什么是故意修复的——改进只是一个副作用——而且戒指的三个宇宙的位置也发生了变化：记录的辅助级别现在是第一个参数，而不是第三个，这就是为什么绑定器读取的是 `RingObject@{rc ra rb}` 而不是 `RingObject@{ra rb rc}`。第二次独立观察，它定位了另一半——不在此文件中。[RingObject@{a b c}] 可以在这里获得的两个识别是 FIRST=THIRD 和 FIRST=SECOND，它们来自不同的地方。第一个是上文探针部分确定的。第二个不是闭合部分的：[tensor_med] 以及 [hm_curry] 的每一种成分——[cur_fun]、[cur_at]、[cur_at_smul]、[cur_out_zero]、[cur_out_plus]、[cur_out_smul]——读取 `RingObject@{a b a}`，因此，与假设不同，它们测量得到 [hm_curry] 本身及其 [Program] 义务 [hm_curry_obligation_1]。因此，此文件声明的没有常量能识别前两个。在 [RMod_SymMonClosed] 的 BINDER 中可见的方程 `u = u0` 因此完全继承自 Instance/Mod/Monoidal.v 的 [ModMonoidal]，该文件的头部将其本地化到自身的打包中，下方的探测部分保护了拆分：在声明的 `Constraint rb < ra` 下——这违反了 FIRST=SECOND，同时保持 FIRST=THIRD 不变——ZW151WZZ、ZW152WZZ、ZW153WZZ 和 [ump_exponents_Mod] 都进行了详细说明，而 [ModMonoidal]、ZW156WZZ 和标题 [RMod_SymMonClosed] 都被拒绝。检查时平铺的约束 BLOCK 如下：ZW158WZZ 包裹它，这里相关的方程在第一行之后。没有任何东西被修复，也没有任何东西被认为是不可避免的。未交付的内容。- 没有证明 ⊗ 不是 [RMod R] 的范畴积，因此没有第一个非笛卡尔证据的声明（见上文）。 - 没有 [StarAutonomous] 实例。[RMod R] 在树中没有对偶对象，也没有寻找；该文件提供了 Structure/Monoidal/Dual.v 所需的假设，并在此处停止。 - 没有 [Adjunction] 记录。双射作为 [Sets] 中的 hom-setoid 同构提供，自然地分别对每个变量成立；它未被封装为 Theory/Adjunction.v 中 `− ⊗ W ⊣ HomMod W −` 的形式，也没有为任何一方构建 `RMod R ⟶ RMod R` 函子。 - 因此，没有单位，没有余单位，也没有三角恒等式；并且没有关于 − ⊗ W 保持余极限的内容。- 没有丰富的阅读：[RMod R] 在自身之上未被展示为丰富，而 [HomMod] 与 Construction/Enriched.v 无关。- [HomMod] 没有双函子性。[ihom_post] 和 [ihom_pre] 是它的两个箭头动作，并且在使用时已证明是自然的，但它们没有组合成 `(RMod R)^op ∏ RMod R ⟶ RMod R`，因此这六个方格是关于箭头的引理，而不是关于双函子。- 在 RING 中没有自然性，也没有与 Instance/Rng/Mod.v 的标量限制交互作用。- 没有非交换变体。在一般 R 上，正确的表述应该是双模的；此处没有接近这一点，并且该文件没有展示构造失败的环。- 与 R = ℤ 时的 Instance/Ab/Monoidal.v 无关（早期修订版添加了“[AbObject] 的 ℤ-模结构不在树中”；自 #454 起它在 Instance/Mod/Cogenerator.v 作为 [Ab_to_ZMod]，但关系仍未建立），并且与 Instance/Mod/Free.v 的自由模或 Instance/FdVect/DoubleDual.v 的对偶函子也无关，超出上文所述的文字识别之外。 - 无宇宙修复；该识别是经过测量和固定的，而非提升的，这里没有任何标注。 - 无 [Instance] 注册。像 Instance/Mod/Monoidal.v 的三种结构一样，[RMod_SymMonClosed] 是一个普通的 [Definition]：注册它会在抽象环上留下无法解决的类型类解析交换性子目标。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Monoidal.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.AbCategory.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Engineering note (c): [mt_eq_Equivalence] (Instance/Mod/Tensor.v) is
 a Lemma, not an Instance, so [transitivity] and setoid [rewrite] cannot
 see it on goals that have unfolded to [mt_eq] — and the error names the
 wrong culprit when they cannot. 

 --------
 工程注释 (c)：[mt_eq_Equivalence] (Instance/Mod/Tensor.v) 是一个引理，而不是一个实例，因此 [transitivity] 和集合同构 [rewrite] 无法在已经展开为 [mt_eq] 的目标上看到它——当它们看不到时，错误会指向错误的元凶。
*)
#[local] Existing Instance mt_eq_Equivalence.

(*
   * ** The internal hom

   The module of R-linear maps V ⟶ W.  Carrier, addition, zero and
   negation are Instance/Mod.v's own hom-algebra; the ACTION is the
   pointwise (r · φ) v := r · φ v, and that is where commutativity
   lands. 

   --------
   * ** 内部同态

   R 线性映射 V ⟶ W 的模。载体、加法、零元和取反是 Instance/Mod.v 自身的同态代数；作用是逐点作用 (r · φ) v := r · φ v，这就是交换性所在。
*)

Section InternalHom.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

(*
 Negation of a module homomorphism.  Instance/Mod.v supplies
 [rmod_hom_add] and [rmod_hom_zero] but no negation, and the obvious name
 [rmod_hom_neg] is taken by Instance/FdVect/DoubleDual.v — hence the
 local name. 

 --------
 模块同态的取反。Instance/Mod.v 提供了 [rmod_hom_add] 和 [rmod_hom_zero]，但没有取反，而显而易见的名称 [rmod_hom_neg] 已被 Instance/FdVect/DoubleDual.v 占用——因此使用了本地名称。
*)
Program Definition hm_neg {M N : RModObject R} (f : RModHom M N) :
  RModHom M N := {|
  rm_hom := ab_hom_neg (rm_hom f)
|}.
Next Obligation.
  intros M N f r m; simpl.
  rewrite (rm_map_smul f r m).
  symmetry; apply rm_smul_neg_r.
Qed.

(* The carrier setoid: two homomorphisms agree when they agree pointwise. / 载体集合：当两个同态在每一点上都相同时，它们就被认为是相同的。 *)
Definition hm_setoid (V W : RModObject R) : SetoidObject := {|
  carrier   := RModHom V W;
  is_setoid := @RModHom_Setoid R V W
|}.

Program Definition hm_cmon (V W : RModObject R) : CMonObject := {|
  cmon_setoid := hm_setoid V W;
  cmon_zero   := @rmod_hom_zero R V W;
  cmon_plus   := @rmod_hom_add R V W
|}.
Next Obligation.
  intros V W f f' Hf g g' Hg v; simpl.
  now rewrite (Hf v), (Hg v).
Qed.
Next Obligation. intros V W f g h v; simpl; apply cmon_plus_assoc. Qed.
Next Obligation. intros V W f g v; simpl; apply cmon_plus_comm. Qed.
Next Obligation. intros V W f v; simpl; apply cmon_plus_zero_l. Qed.

Program Definition hm_ab (V W : RModObject R) : AbObject := {|
  ab_cmon := hm_cmon V W;
  ab_neg  := @hm_neg V W
|}.
Next Obligation.
  intros V W f g Hfg v; simpl.
  now rewrite (Hfg v).
Qed.
Next Obligation. intros V W f v; simpl; apply ab_neg_left. Qed.

(*
   * *** The pointwise action, and the one use of commutativity

   Preservation of zero and of addition are annihilation and
   distributivity in W, and neither mentions [Rcomm] — the two lemmas
   below are what the probe section uses as controls.  The remaining
   clause, that r · φ is still LINEAR, is the one that does. 

   --------
   * *** 点对点作用，以及交换律的唯一使用

   保持零和加法是 W 中的消去性和分配性，两者都未提及 [Rcomm] —— 下面的两个引理是探针部分用作控制的。剩下的部分，即 r · φ 仍然是线性的，则是那个起作用的部分。
*)

Lemma hm_smul_zero (V W : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (f : RModHom V W) :
  rm_smul W r (cmon_map (rm_hom f) (cmon_zero V)) ≈ cmon_zero W.
Proof.
  rewrite (cmon_map_zero (rm_hom f)).
  apply rm_smul_zero_r.
Qed.

Lemma hm_smul_plus (V W : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (f : RModHom V W) :
  ∀ v w, rm_smul W r (cmon_map (rm_hom f) (cmon_plus V v w))
           ≈ cmon_plus W (rm_smul W r (cmon_map (rm_hom f) v))
                         (rm_smul W r (cmon_map (rm_hom f) w)).
Proof.
  intros v w.
  rewrite (cmon_map_plus (rm_hom f) v w).
  apply rm_smul_distr_l.
Qed.

(*
 THE ONE USE OF COMMUTATIVITY IN THE WHOLE FILE.

 The `Proof using R Rcomm` annotation is LOAD-BEARING and is the
 instrument the header describes: Lib.v sets
 [Default Proof Using “Type”], [Rcomm] occurs in no statement here, and
 without the annotation this lemma fails at [Qed] with “The following
 section variable is used but not declared: Rcomm.”  Do not remove it,
 and do not silence it with `Set Default Proof Using “All”` — that would
 destroy the measurement rather than pass it. 

 --------
 整个文件中交换律的唯一用法。

 `Proof using R Rcomm` 注释是承重的，并且是头文件描述的工具：Lib.v 设置了 [Default Proof Using “Type”]，[Rcomm] 在此处没有任何语句中出现，如果没有该注释，这个引理将在 [Qed] 处失败，并显示“以下节变量被使用但未声明：Rcomm。”不要移除它，也不要用 `Set Default Proof Using “All”` 将其静音——那样会破坏测量而不是使其通过。
*)
Lemma hm_smul_linear (V W : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (f : RModHom V W) :
  ∀ s v, rm_smul W r (cmon_map (rm_hom f) (rm_smul V s v))
           ≈ rm_smul W s (rm_smul W r (cmon_map (rm_hom f) v)).
Proof using R Rcomm.
  intros s v.
  rewrite (rm_map_smul f s v).
  rewrite <- (rm_smul_assoc W r s (cmon_map (rm_hom f) v)).
  rewrite (Rcomm r s).
  apply (rm_smul_assoc W s r (cmon_map (rm_hom f) v)).
Qed.

Program Definition hm_smul (V W : RModObject R)
        (r : carrier (rig_setoid (ring_rig R))) (f : RModHom V W) :
  RModHom V W := {|
  rm_hom := {|
    cmon_map      := {| morphism := fun v =>
                          rm_smul W r (cmon_map (rm_hom f) v) |};
    cmon_map_zero := hm_smul_zero V W r f;
    cmon_map_plus := hm_smul_plus V W r f
  |};
  rm_map_smul := hm_smul_linear V W r f
|}.
Next Obligation.
  intros V W r f v w Hvw; simpl.
  now rewrite Hvw.
Qed.

(* * *** The internal hom module Every module law below is the corresponding law of W read at each vector; none of them needs [Rcomm] again. / * *** 内部同模模块 下面的每个模定律都是在每个向量上读取 W 的对应定律；它们都不需要再次使用 [Rcomm]。 *)
Program Definition HomMod (V W : RModObject R) : RModObject R := {|
  rm_ab   := hm_ab V W;
  rm_smul := hm_smul V W
|}.
Next Obligation.
  intros V W r s Hrs f g Hfg v; simpl.
  now rewrite Hrs, (Hfg v).
Qed.
Next Obligation. intros V W r f g v; simpl; apply rm_smul_distr_l. Qed.
Next Obligation. intros V W r s f v; simpl; apply rm_smul_distr_r. Qed.
Next Obligation. intros V W r s f v; simpl; apply rm_smul_assoc. Qed.
Next Obligation. intros V W f v; simpl; apply rm_smul_one. Qed.

(* The carrier IS the hom-set, on the nose. / 承载体就是同态集，确切无误。 *)
Example HomMod_carrier (V W : RModObject R) :
  carrier (cmon_setoid (HomMod V W)) = RModHom V W := eq_refl.

End InternalHom.

(*
   * ** Currying and uncurrying

   [hm_curry] sends f : V ⊗ W ⟶ X to v ↦ (w ↦ f (v ⊗ w)); [hm_uncurry]
   factors the bilinear map (v, w) ↦ (g v) w through the tensor.  Both
   round trips are below, and both are cheap for the reason the header
   gives: [tensor_med] computes on generators. 

   --------
   * ** 柯里化与逆柯里化

   [hm_curry] 将 f : V ⊗ W ⟶ X 发送为 v ↦ (w ↦ f (v ⊗ w))；[hm_uncurry] 
   通过张量分解双线性映射 (v, w) ↦ (g v) w。两个
   往返操作如下，并且两者都很简便，原因如标题所示：
   [tensor_med] 在生成元上进行计算。
*)

Section Adjunction.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Notation IH := (HomMod R Rcomm).

Section Curry.

Context {V W X : RModObject R}.
Context (f : TensorMod V W ~{RMod R}~> X).

(* [mval] is Instance/Mod/Monoidal.v's name for the underlying function of a module homomorphism; it is imported, not redeclared. / [mval] 是 Instance/Mod/Monoidal.v 中模块同态的底层函数的名称；它是导入的，而不是重新声明的。 *)
Definition cur_fun (v : carrier (cmon_setoid V))
  (w : carrier (cmon_setoid W)) : carrier (cmon_setoid X) :=
  mval f (mt_gen v w).

(*
 w ↦ f (v ⊗ w) is a module homomorphism W ⟶ X: each clause is one
 clause of [tensor_gen] pushed through f. 

 --------
 w ↦ f (v ⊗ w) 是一个模同态 W ⟶ X：每一个子句都是通过 f 推送的 [tensor_gen] 的一个子句。
*)

Lemma cur_at_zero (v : carrier (cmon_setoid V)) :
  cur_fun v (cmon_zero W) ≈ cmon_zero X.
Proof.
  unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f) (cmon_zero (TensorMod V W))).
  - apply proper_morphism, (rbl_zero_r tensor_gen v).
  - apply (cmon_map_zero (rm_hom f)).
Qed.

Lemma cur_at_plus (v : carrier (cmon_setoid V)) :
  ∀ w w', cur_fun v (cmon_plus W w w')
            ≈ cmon_plus X (cur_fun v w) (cur_fun v w').
Proof.
  intros w w'; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (TensorMod V W) (mt_gen v w) (mt_gen v w'))).
  - apply proper_morphism, (rbl_add_r tensor_gen v w w').
  - apply (cmon_map_plus (rm_hom f)).
Qed.

Lemma cur_at_smul (v : carrier (cmon_setoid V)) :
  ∀ r w, cur_fun v (rm_smul W r w) ≈ rm_smul X r (cur_fun v w).
Proof.
  intros r w; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f)
                  (rm_smul (TensorMod V W) r (mt_gen v w))).
  - apply proper_morphism, (rbl_smul_r tensor_gen r v w).
  - apply (rm_map_smul f r (mt_gen v w)).
Qed.

Program Definition cur_at (v : carrier (cmon_setoid V)) : RModHom W X := {|
  rm_hom := {|
    cmon_map      := {| morphism := cur_fun v |};
    cmon_map_zero := cur_at_zero v;
    cmon_map_plus := cur_at_plus v
  |};
  rm_map_smul := cur_at_smul v
|}.
Next Obligation.
  intros v w w' Hw; unfold cur_fun, mval; simpl.
  apply proper_morphism, (rbl_respects tensor_gen); [reflexivity | exact Hw].
Qed.

(* And v ↦ cur_at v is a module homomorphism V ⟶ IH W X: the same three clauses of [tensor_gen] in the OTHER variable. / 并且 v ↦ cur_at v 是一个模同态 V ⟶ IH W X：在另一个变量中是 [tensor_gen] 的相同三条子句。 *)

Lemma cur_out_zero : cur_at (cmon_zero V) ≈ cmon_zero (IH W X).
Proof.
  intro w; simpl; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f) (cmon_zero (TensorMod V W))).
  - apply proper_morphism, (rbl_zero_l tensor_gen w).
  - apply (cmon_map_zero (rm_hom f)).
Qed.

Lemma cur_out_plus : ∀ v v',
  cur_at (cmon_plus V v v') ≈ cmon_plus (IH W X) (cur_at v) (cur_at v').
Proof.
  intros v v' w; simpl; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (TensorMod V W) (mt_gen v w) (mt_gen v' w))).
  - apply proper_morphism, (rbl_add_l tensor_gen v v' w).
  - apply (cmon_map_plus (rm_hom f)).
Qed.

Lemma cur_out_smul : ∀ r v,
  cur_at (rm_smul V r v) ≈ rm_smul (IH W X) r (cur_at v).
Proof.
  intros r v w; simpl; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f)
                  (rm_smul (TensorMod V W) r (mt_gen v w))).
  - apply proper_morphism, (rbl_smul_l tensor_gen r v w).
  - apply (rm_map_smul f r (mt_gen v w)).
Qed.

Program Definition hm_curry : V ~{RMod R}~> IH W X := {|
  rm_hom := {|
    cmon_map      := {| morphism := cur_at |};
    cmon_map_zero := cur_out_zero;
    cmon_map_plus := cur_out_plus
  |};
  rm_map_smul := cur_out_smul
|}.
Next Obligation.
  intros v v' Hv w; simpl; unfold cur_fun, mval.
  apply proper_morphism, (rbl_respects tensor_gen); [exact Hv | reflexivity].
Qed.

End Curry.

Arguments hm_curry {V W X} f.

Section Uncurry.

Context {V W X : RModObject R}.
Context (g : V ~{RMod R}~> IH W X).

(*
 (v, w) ↦ (g v) w is bilinear: linearity in w is g v's own linearity,
 linearity in v is g's, read at w. 

 --------
 （v， w） ↦ （g v） w 是双线性：W 中的线性是 G V 自身的线性，
 V中的线性是g，读作w。
*)
Program Definition uncur_bilinear : RBilinear V W X := {|
  rbl_map := fun v w => mval (mval g v) w
|}.
Next Obligation.
  intros v v' Hv w w' Hw; simpl; unfold mval.
  transitivity (cmon_map (rm_hom (cmon_map (rm_hom g) v)) w').
  - apply proper_morphism, Hw.
  - exact (proper_morphism (cmon_map (rm_hom g)) v v' Hv w').
Qed.
Next Obligation.
  intros v v' w; simpl.
  exact (cmon_map_plus (rm_hom g) v v' w).
Qed.
Next Obligation.
  intros v w w'; simpl.
  apply (cmon_map_plus (rm_hom (cmon_map (rm_hom g) v)) w w').
Qed.
Next Obligation.
  intros r v w; simpl.
  exact (rm_map_smul g r v w).
Qed.
Next Obligation.
  intros r v w; simpl.
  apply (rm_map_smul (cmon_map (rm_hom g) v) r w).
Qed.

Definition hm_uncurry : TensorMod V W ~{RMod R}~> X :=
  tensor_med uncur_bilinear.

End Uncurry.

Arguments hm_uncurry {V W X} g.

(*
 The uncurried map's value at a generator is φ applied to the argument,
 at LEIBNIZ equality.  This is [tensor_med]'s own `eq_refl` generator
 equation (Instance/Mod/Tensor.v) instantiated, and it is what makes
 everything below cheap. 

 --------
 未柯里化的 map 在生成器上的值是 φ 应用于参数，在莱布尼茨相等下。这是 [tensor_med] 自己的 `eq_refl` 生成器方程（Instance/Mod/Tensor.v）的实例化，它使得下文的所有操作都变得廉价。
*)
Example hm_uncurry_gen {V W X : RModObject R}
  (g : V ~{RMod R}~> IH W X) v w :
  mval (hm_uncurry g) (mt_gen v w) = mval (mval g v) w := eq_refl.

(* Round trip one: extensionality, then the generator computation. / 往返一次：先是外延性，然后是生成器计算。 *)
Lemma hm_uncurry_curry {V W X : RModObject R}
  (f : TensorMod V W ~{RMod R}~> X) : hm_uncurry (hm_curry f) ≈ f.
Proof.
  refine (tensor_hom_ext (hm_uncurry (hm_curry f)) f _).
  intros v w; reflexivity.
Qed.

(* Round trip two: pointwise definitional, no extensionality needed. / 往返二：逐点定义，不需要外延性。 *)
Lemma hm_curry_uncurry {V W X : RModObject R}
  (g : V ~{RMod R}~> IH W X) : hm_curry (hm_uncurry g) ≈ g.
Proof. intros v w; reflexivity. Qed.

End Adjunction.

(* * ** The bijection, evaluation, and the universal property / * ** 双射、评价以及泛性质 *)

Section ExpIso.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Notation IH  := (HomMod R Rcomm).
Notation cur := (hm_curry R Rcomm).
Notation unc := (hm_uncurry R Rcomm).

Program Definition exp_to (V W X : RModObject R) :
  {| carrier := TensorMod V W ~{RMod R}~> X |}
    ~{Sets}~> {| carrier := V ~{RMod R}~> IH W X |} := {|
  morphism := @hm_curry R Rcomm V W X
|}.
Next Obligation.
  intros V W X f f' Hf v w; simpl.
  exact (Hf (mt_gen v w)).
Qed.

Program Definition exp_from (V W X : RModObject R) :
  {| carrier := V ~{RMod R}~> IH W X |}
    ~{Sets}~> {| carrier := TensorMod V W ~{RMod R}~> X |} := {|
  morphism := @hm_uncurry R Rcomm V W X
|}.
Next Obligation.
  intros V W X g g' Hg.
  refine (tensor_hom_ext (unc g) (unc g') _).
  intros v w; exact (Hg v w).
Qed.

Program Definition exp_iso_Mod (V W X : RModObject R) :
  @Isomorphism Sets
    {| carrier := TensorMod V W ~{RMod R}~> X |}
    {| carrier := V ~{RMod R}~> IH W X |} := {|
  to   := exp_to V W X;
  from := exp_from V W X
|}.
Next Obligation.
  intros V W X g; exact (hm_curry_uncurry R Rcomm g).
Qed.
Next Obligation.
  intros V W X f; exact (hm_uncurry_curry R Rcomm f).
Qed.

(*
   * Evaluation is the uncurried identity — which is exactly what the class
   takes [eval'] to be, so [smc_eval] below is `eq_refl`. 

   --------
   * 评估是未柯里化的身份——这正是类所认为的 [eval']，因此下面的 [smc_eval] 是 `eq_refl`。
*)
Definition eval_Mod (W X : RModObject R) :
  TensorMod (IH W X) W ~{RMod R}~> X :=
  unc (@id (RMod R) (IH W X)).

Example eval_Mod_gen (W X : RModObject R)
  (phi : carrier (cmon_setoid (IH W X))) (w : carrier (cmon_setoid W)) :
  mval (eval_Mod W X) (mt_gen phi w) = mval phi w := eq_refl.

(* The beta law. [mt_fmap] is Instance/Mod/Monoidal.v's arrow action, and `bimap h id` reduces to it — see [smc_bimap] below. / 贝塔定律。[mt_fmap] 是 Instance/Mod/Monoidal.v 的箭头作用，`bimap h id` 可以归约为它 — 见下方的 [smc_bimap]。 *)
Lemma ump_beta (V W X : RModObject R) (f : TensorMod V W ~{RMod R}~> X) :
  f ≈ eval_Mod W X ∘ mt_fmap (cur f) (@id (RMod R) W).
Proof.
  refine (tensor_hom_ext f
            (eval_Mod W X ∘ mt_fmap (cur f) (@id (RMod R) W)) _).
  intros v w; reflexivity.
Qed.

(* Uniqueness: evaluate the hypothesis at a generator. Nothing else. / 独特性：在生成器上评估假设。仅此而已。 *)
Lemma ump_uniq (V W X : RModObject R) (f : TensorMod V W ~{RMod R}~> X)
  (h : V ~{RMod R}~> IH W X) :
  f ≈ eval_Mod W X ∘ mt_fmap h (@id (RMod R) W) → cur f ≈ h.
Proof.
  intros Hh v w.
  exact (Hh (mt_gen v w)).
Qed.

Theorem ump_exponents_Mod (V W X : RModObject R)
  (f : TensorMod V W ~{RMod R}~> X) :
  ∃! h : V ~{RMod R}~> IH W X,
    f ≈ eval_Mod W X ∘ mt_fmap h (@id (RMod R) W).
Proof.
  exists (cur f).
  - exact (ump_beta V W X f).
  - intros h Hh; exact (ump_uniq V W X f h Hh).
Qed.

End ExpIso.

(*
   * ** THE HEADLINE

   Every field is filled by `:=` with no tactic and no transport.  The
   underlying symmetric monoidal structure is Instance/Mod/Monoidal.v's
   [ModSymmetric] itself, not a copy; the internal hom is [HomMod]; the
   bijection is [exp_iso_Mod]; the universal property is
   [ump_exponents_Mod].  A plain [Definition] rather than an [Instance],
   for the reason the header gives. 

   --------
   * **标题

   每个字段都由 `:=` 填写，没有策略也没有传输。
   底层的对称幺半范畴结构是 Instance/Mod/Monoidal.v 中的
   [ModSymmetric] 本身，而不是副本；内部 Hom 是 [HomMod]；双射是 [exp_iso_Mod]；普遍性是
   [ump_exponents_Mod]。使用普通的 [Definition] 而不是 [Instance]，
   原因如标题所示。
*)

Definition RMod_SymMonClosed (R : RingObject)
  (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
      rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a) :
  @SymMonClosed (RMod R) := {|
  smc_is_symmetric := ModSymmetric Rcomm;
  exponent_obj     := HomMod R Rcomm;
  exp_iso          := @exp_iso_Mod R Rcomm;
  ump_exponents'   := @ump_exponents_Mod R Rcomm
|}.

(*
   * *** What the class returns, measured at [eq_refl]

   Seven identifications.  Three of them concern the class's DEFINED
   fields — [curry'], [uncurry'] and [eval'] have bodies rather than being
   arguments, so a consumer could have received a repackaging; these
   record that they receive this file's own constants instead.  Two more
   check the join with Instance/Mod/Monoidal.v: the tensor's object action
   and the reduction of `bimap h id` to [mt_fmap h id]. 

   --------
   * *** 该类返回的内容，在 [eq_refl] 处测量

   七个标识。其中三个涉及该类的已定义字段——[curry']、[uncurry'] 和 [eval'] 具有主体而不是参数，因此使用者可能会收到重新打包的内容；这些记录表明它们接收到的是该文件自身的常量。还有两个检查与 Instance/Mod/Monoidal.v 的连接：张量的对象操作以及将 `bimap h id` 化简为 [mt_fmap h id]。
*)

Section Slot.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Notation SMC := (RMod_SymMonClosed R Rcomm).

Example smc_symmetric :
  @smc_is_symmetric (RMod R) SMC = ModSymmetric Rcomm := eq_refl.

Example smc_exponent (V W : RModObject R) :
  @exponent_obj (RMod R) SMC V W = HomMod R Rcomm V W := eq_refl.

Example smc_curry (V W X : RModObject R)
  (f : TensorMod V W ~{RMod R}~> X) :
  @curry' (RMod R) SMC V W X f = hm_curry R Rcomm f := eq_refl.

Example smc_uncurry (V W X : RModObject R)
  (g : V ~{RMod R}~> HomMod R Rcomm W X) :
  @uncurry' (RMod R) SMC V W X g = hm_uncurry R Rcomm g := eq_refl.

Example smc_eval (W X : RModObject R) :
  @eval' (RMod R) SMC W X = eval_Mod R Rcomm W X := eq_refl.

Example smc_tensor (V W : RModObject R) :
  fobj[@tensor (RMod R) SMC] (V, W) = TensorMod V W := eq_refl.

Example smc_bimap (V W X : RModObject R)
  (h : V ~{RMod R}~> HomMod R Rcomm W X) :
  @bimap _ _ _ (@tensor (RMod R) SMC) _ _ _ _ h (@id (RMod R) W)
    = mt_fmap h (@id (RMod R) W) := eq_refl.

End Slot.

(* * ** Naturality in all three variables The internal hom's two arrow actions, and then the six squares. See the header for why both legs are stated. / * ** 三个变量的自然性 内部 Hom 的两个箭头作用，然后是六个方形。参见标题了解为什么两条腿都被说明。 *)

Section Naturality.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Notation IH   := (HomMod R Rcomm).
Notation cur  := (hm_curry R Rcomm).
Notation unc  := (hm_uncurry R Rcomm).

(* Postcomposition: covariant in the target. / 后置组成：在目标中协变。 *)
Program Definition ihom_post {W X X' : RModObject R}
  (k : X ~{RMod R}~> X') : IH W X ~{RMod R}~> IH W X' := {|
  rm_hom := {| cmon_map := {| morphism := fun phi =>
    @rmod_hom_compose R W X X' k phi |} |}
|}.
Next Obligation.
  intros W X X' k phi psi Hphi w; simpl; unfold Basics.compose.
  apply proper_morphism, (Hphi w).
Qed.
Next Obligation.
  intros W X X' k w; simpl; unfold Basics.compose.
  apply (cmon_map_zero (rm_hom k)).
Qed.
Next Obligation.
  intros W X X' k phi psi w; simpl; unfold Basics.compose.
  apply (cmon_map_plus (rm_hom k)).
Qed.
Next Obligation.
  intros W X X' k r phi w; simpl; unfold Basics.compose.
  apply (rm_map_smul k).
Qed.

(*
 Precomposition: contravariant in the source.  Every clause is
 [reflexivity] — precomposition moves no structure. 

 --------
 预组合：在源中是反变的。每个子句都是[reflexivity]——预组合不移动任何结构。
*)
Program Definition ihom_pre {W W' X : RModObject R}
  (j : W' ~{RMod R}~> W) : IH W X ~{RMod R}~> IH W' X := {|
  rm_hom := {| cmon_map := {| morphism := fun phi =>
    @rmod_hom_compose R W' W X phi j |} |}
|}.
Next Obligation.
  intros W W' X j phi psi Hphi w; simpl; unfold Basics.compose.
  exact (Hphi _).
Qed.
Next Obligation. intros W W' X j w; simpl; reflexivity. Qed.
Next Obligation. intros W W' X j phi psi w; simpl; reflexivity. Qed.
Next Obligation. intros W W' X j r phi w; simpl; reflexivity. Qed.

(*
   * *** The three FORWARD squares

   Each holds by [reflexivity]: the two sides are pointwise the same
   term.  Note that this is agreement in the hom-SETOID; the whole
   morphism records are NOT Leibniz-equal, and the probe section pins
   that. 

   --------
   * *** 三个前进方格

   每个由 [reflexivity] 保持：两边在每一点上是相同的项。注意，这是在同调 SEToid 中的一致性；整个态射记录并不与莱布尼兹相等，探针部分固定了这一点。
*)

(* (a) In V, contravariantly: precomposing with i ⊗ id downstairs is precomposing with i upstairs. / (a) 在 V 中，反变地：在底下与 i ⊗ id 进行前合成相当于在上面与 i 进行前合成。 *)
Theorem cur_natural_V {V V' W X : RModObject R}
  (i : V' ~{RMod R}~> V) (f : TensorMod V W ~{RMod R}~> X) :
  cur (f ∘ mt_fmap i (@id (RMod R) W)) ≈ cur f ∘ i.
Proof. intros v w; reflexivity. Qed.

(* (b) In W, contravariantly: precomposing with id ⊗ j downstairs is postcomposing with [ihom_pre j] upstairs. / (b) 在 W 中，逆变地：在下方与 id ⊗ j 预组合相当于在上方与 [ihom_pre j] 后组合。 *)
Theorem cur_natural_W {V W W' X : RModObject R}
  (j : W' ~{RMod R}~> W) (f : TensorMod V W ~{RMod R}~> X) :
  cur (f ∘ mt_fmap (@id (RMod R) V) j) ≈ ihom_pre j ∘ cur f.
Proof. intros v w; reflexivity. Qed.

(* (c) In X, covariantly: postcomposing with k downstairs is postcomposing with [ihom_post k] upstairs. / (c) 在 X 中，共变地：在底层与 k 后组合相当于在顶层与 [ihom_post k] 后组合。 *)
Theorem cur_natural_X {V W X X' : RModObject R}
  (k : X ~{RMod R}~> X') (f : TensorMod V W ~{RMod R}~> X) :
  cur (k ∘ f) ≈ ihom_post k ∘ cur f.
Proof. intros v w; reflexivity. Qed.

(*
   * *** The three BACKWARD squares

   NOT definitional.  Both sides are recursions over [MTerm] — the
   left-hand one built from a single bilinear map, the right-hand one a
   composite — so they agree at every generator but are different terms
   at a variable tensor.  Each needs one [tensor_hom_ext] and then
   [reflexivity], and nothing else: no [tensor_factor_commutes], no
   transitivity chain. 

   --------
   * *** 三个逆方块

   不是定义性的。两边都是对 [MTerm] 的递归 —— 左边的是由单个双线性映射构建的，右边的是复合的 —— 所以它们在每个生成元上都是相同的，但在变量张量上是不同的项。每个都需要一个 [tensor_hom_ext]，然后是 [reflexivity]，其它都不需要：不需要 [tensor_factor_commutes]，也不需要传递链。
*)

Theorem unc_natural_V {V V' W X : RModObject R}
  (i : V' ~{RMod R}~> V) (g : V ~{RMod R}~> IH W X) :
  unc (g ∘ i) ≈ unc g ∘ mt_fmap i (@id (RMod R) W).
Proof.
  refine (tensor_hom_ext (unc (g ∘ i))
            (unc g ∘ mt_fmap i (@id (RMod R) W)) _).
  intros v w; reflexivity.
Qed.

Theorem unc_natural_W {V W W' X : RModObject R}
  (j : W' ~{RMod R}~> W) (g : V ~{RMod R}~> IH W X) :
  unc (ihom_pre j ∘ g) ≈ unc g ∘ mt_fmap (@id (RMod R) V) j.
Proof.
  refine (tensor_hom_ext (unc (ihom_pre j ∘ g))
            (unc g ∘ mt_fmap (@id (RMod R) V) j) _).
  intros v w; reflexivity.
Qed.

Theorem unc_natural_X {V W X X' : RModObject R}
  (k : X ~{RMod R}~> X') (g : V ~{RMod R}~> IH W X) :
  unc (ihom_post k ∘ g) ≈ k ∘ unc g.
Proof.
  refine (tensor_hom_ext (unc (ihom_post k ∘ g)) (k ∘ unc g) _).
  intros v w; reflexivity.
Qed.

End Naturality.

(*
   * ** Acceptance tests over ℤ

   ℤ is commutative (Instance/Rng.v's [Int_Ring_commutative]), so the
   whole structure is inhabited at a concrete base.  The bilinear map is
   Instance/Mod/Tensor.v's own [Int_mul_bilinear] — nothing is
   rebuilt — and every Example below closes by `eq_refl`: these are
   computations, not equational arguments. 

   --------
   * ** 关于 ℤ 的验收测试

   ℤ 是交换的（Instance/Rng.v 的 [Int_Ring_commutative]），因此整个结构在具体基底下都是存在的。双线性映射是 Instance/Mod/Tensor.v 自身的 [Int_mul_bilinear] —— 没有任何重建 —— 并且下面的每个示例都是通过 `eq_refl` 结束的：这些都是计算，不是方程论证。
*)

Local Notation Zc := Int_Ring_commutative.
Local Notation ZIH := (HomMod Int_Ring Zc).
Local Notation zg := (@mt_gen Int_Ring Int_RMod Int_RMod).

Definition Int_Mod_SymMonClosed : @SymMonClosed (RMod Int_Ring) :=
  RMod_SymMonClosed Int_Ring Int_Ring_commutative.

(* The ℤ-linear endomorphisms of ℤ, as a ℤ-module. / 作为 ℤ-模的 ℤ 的 ℤ 线性自同态。 *)
Definition ZEnd : RModObject Int_Ring := ZIH Int_RMod Int_RMod.

(* The pointwise action COMPUTES: (3 · id) 5 = 15. / 逐点作用计算： (3 · id) 5 = 15。 *)
Example Zsmul_computes :
  mval (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z = 15%Z
  := eq_refl.

(* Two elements of the internal hom that are provably distinct, so it is not a subsingleton and the computations above are not degenerate. / 内部 Hom 的两个元素可以证明是不同的，因此它不是单子集，上述计算也不是退化的。 *)
Example ZEnd_nontrivial :
  mval (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 1%Z
    ≈ mval (@id (RMod Int_Ring) Int_RMod) 1%Z → False.
Proof. simpl; discriminate. Qed.

Definition Zmul_tensor_hom :
  TensorMod Int_RMod Int_RMod ~{RMod Int_Ring}~> Int_RMod :=
  tensor_med Int_mul_bilinear.

(* Currying computes: cur(multiplication) at 2, applied to 3, is 6. / 柯里化计算：cur(乘法)在2时应用于3，结果是6。 *)
Example Zcur_computes :
  mval (mval (hm_curry Int_Ring Zc Zmul_tensor_hom) 2%Z) 3%Z = 6%Z
  := eq_refl.

(* And so does the round trip, at a generator. / 在发电机处，往返也是如此。 *)
Example Zuncur_computes :
  mval (hm_uncurry Int_Ring Zc (hm_curry Int_Ring Zc Zmul_tensor_hom))
       (zg 4%Z 5%Z) = 20%Z := eq_refl.

(* Evaluation computes, through the file's own [eval_Mod] ... / 评估通过文件自身的 [eval_Mod] 进行计算... *)
Example Zeval_computes :
  mval (eval_Mod Int_Ring Zc Int_RMod Int_RMod)
       (@mt_gen Int_Ring ZEnd Int_RMod
          (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z)
    = 15%Z := eq_refl.

(* ... and through the CLASS's [eval'], which is the same term. / ...并通过CLASS的[eval']，这与同一术语相同。 *)
Example Zsmc_eval :
  mval (@eval' (RMod Int_Ring) Int_Mod_SymMonClosed Int_RMod Int_RMod)
       (@mt_gen Int_Ring ZEnd Int_RMod
          (rm_smul ZEnd 4%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z)
    = 20%Z := eq_refl.

Example Zsmc_exp :
  @exponent_obj (RMod Int_Ring) Int_Mod_SymMonClosed Int_RMod Int_RMod
    = ZEnd := eq_refl.

(*
   * ** Probes

   THIRTEEN negatives of THREE KINDS — two TYPING, three CONVERSION,
   eight FORMABILITY — kept lexically apart, each beside an APPLIED
   positive control, plus a scope-free instrument check.  With
   Instance/Mod/Monoidal.v's eight that is twenty-one negatives across the
   pair, in four kinds; the two instrument checks are guards and are not
   counted among them, so the two files carry twenty-three [Fail]
   commands in all.  A [Fail] that succeeds prints nothing under this
   repository's [coqc], so each negative below
   was stripped of its [Fail] and compiled alone, and its failure KIND
   read off the WHOLE error message rather than the tail: the TYPING two
   report a bare type mismatch with no `cannot unify` and no universe
   clause, the CONVERSION three end in `cannot unify`, and the
   FORMABILITY eight end in a universe inconsistency naming the levels
   the probe section declared — `Cannot enforce rc = ra because
   ra < rc` for the five that test FIRST=THIRD, and `Cannot enforce
   rb = ra because rb < ra` for the three that test FIRST=SECOND. 

   --------
   * ** 探针三种类型的十三个负面——两个打字错误，三个转换错误，八个可形成性错误——在词汇上分开，每个旁边都有一个应用的正控制，以及一个无范围的仪器检查。加上 Instance/Mod/Monoidal.v 的八个负面，总共有二十一种负面在这两个文件中，分为四类；两个仪器检查是保护措施，不计入其中，因此这两个文件总共有二十三个 [Fail] 命令。一个成功的 [Fail] 在这个仓库的 [coqc] 下不会打印任何内容，因此下面的每个失败项都被剥离了它的 [Fail] 并单独编译，其失败的 KIND 会从完整的错误信息中读取，而不是只看尾部：TYPING 的两个报告一个裸类型不匹配，没有 `cannot unify`，也没有宇宙条款；CONVERSION 的三个以 `cannot unify` 结束；FORMABILITY 的八个以宇宙不一致结束，命名了探测部分声明的层级——`无法强制 rc = ra 因为 ra < rc ` for the five that test FIRST=THIRD, and ` 无法强制 rb = ra 因为 rb < ra` 对于测试 FIRST=SECOND 的三个实例。
*)

(* INSTRUMENT CHECK — scope-free, guards that [Fail] is doing anything. / 仪器检查——无范围，防护装置确保 [Fail] 没有进行任何操作。 *)
Fail Example mod_closed_instrument : (true = false) := eq_refl.

(** *** Kind 1: TYPING / *** 类型 1：打字 *)

Section ProbeTyping.

Context (R : RingObject).
Context (V W : RModObject R).
Context (r : carrier (rig_setoid (ring_rig R))).
Context (f : RModHom V W).

(*
 NEGATIVE 1.  The [Default Proof Using] instrument, read from outside
 the proof: [hm_smul_linear] carries [Rcomm] as an ARGUMENT, so [V]
 lands in the commutativity slot and the application is ill-typed. 

 --------
 否定 1.  从外部证明读取 [Default Proof Using] 仪器：[hm_smul_linear] 带有 [Rcomm] 作为参数，因此 [V] 落在交换性插槽中，且应用类型错误。
*)
Fail Check (@hm_smul_linear R V W r f).

(*
 CONTROLS.  Its two siblings — same section, same statement shape, same
 [Program] block — do not, because their PROOFS do not use it. 

 --------
 控制。它的两个兄弟——同一部分、相同的陈述形式、相同的 [Program] 块——则没有，因为它们的证明没有使用它。
*)
Check (@hm_smul_zero R V W r f).
Check (@hm_smul_plus R V W r f).

End ProbeTyping.

(*
 NEGATIVE 2.  Engineering note: [mt_gen] at a hom-module needs explicit
 indices — the inner generator elaborates before the outer tensor is
 known, and the error blames the second argument. 

 --------
 负 2。工程说明：[mt_gen] 在同态模上需要显式的索引 — 内部生成器会在外部张量已知之前展开，而错误归咎于第二个参数。
*)
Fail Check (mt_gen (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z).

(* CONTROL: the annotated form. / 控制：带注释的表格。 *)
Check (@mt_gen Int_Ring ZEnd Int_RMod
         (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z).

(** *** Kind 2: CONVERSION / *** 类型 2：转换 *)

(*
 NEGATIVE 3.  The round trip is an `≈`, not a Leibniz identity of
 morphism records: [hm_uncurry (hm_curry f)] is a [tensor_med] over
 [uncur_bilinear], while [Zmul_tensor_hom] is one over
 [Int_mul_bilinear], and the two bilinear records are different terms. 

 --------
 否定 3. 往返是一个 `≈`，而不是形态记录的莱布尼茨恒等式：[hm_uncurry (hm_curry f)] 是 [tensor_med] 在 [uncur_bilinear] 上的一个，而 [Zmul_tensor_hom] 是 [Int_mul_bilinear] 上的一个，这两个双线性记录是不同的项。
*)
Fail Example probe_rt_strict :
  hm_uncurry Int_Ring Zc (hm_curry Int_Ring Zc Zmul_tensor_hom)
    = Zmul_tensor_hom := eq_refl.

(*
 CONTROL: at a generator it IS a Leibniz identity, so the obstruction is
 exactly extensionality and not the generator computation. 

 --------
 控制：在生成元上，它是一个莱布尼茨恒等式，因此障碍恰好是外延性，而不是生成元计算。
*)
Example probe_rt_gen :
  mval (hm_uncurry Int_Ring Zc (hm_curry Int_Ring Zc Zmul_tensor_hom))
       (zg 2%Z 3%Z)
    = mval Zmul_tensor_hom (zg 2%Z 3%Z) := eq_refl.

Section ProbeConversion.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).
Context (V V' W X : RModObject R).
Context (i : V' ~{RMod R}~> V).
Context (g : V ~{RMod R}~> HomMod R Rcomm W X).
Context (v : carrier (cmon_setoid V')) (w : carrier (cmon_setoid W)).

(*
 NEGATIVE 4.  [unc_natural_V] at Leibniz strength: refuted.  This is
 what the [tensor_hom_ext] in its proof is buying. 

 --------
 负 4. [unc_natural_V] 在莱布尼茨强度下：被驳斥。这就是 [tensor_hom_ext] 在其证明中所依赖的。
*)
Fail Example probe_unc_nat_strict :
  hm_uncurry R Rcomm (g ∘ i)
    = hm_uncurry R Rcomm g ∘ mt_fmap i (@id (RMod R) W) := eq_refl.

(* CONTROL: the same statement at a generator, at Leibniz `=`. / 控制：在发电机上相同的声明，在莱布尼茨 `=`。 *)
Example probe_unc_nat_gen :
  mval (hm_uncurry R Rcomm (g ∘ i)) (mt_gen v w)
    = mval (hm_uncurry R Rcomm g ∘ mt_fmap i (@id (RMod R) W))
           (mt_gen v w) := eq_refl.

(*
 NEGATIVE 5.  The FORWARD square is `≈` by [reflexivity], but the two
 morphism RECORDS are still not Leibniz-equal — so “holds by
 [reflexivity]” must not be over-read as “is the same term”. 

 --------
 负 5。正向方格是 `≈` 乘以 [reflexivity]，但这两个态射记录仍然不是莱布尼茨相等的——所以“由 [reflexivity] 保持”不能被过度解读为“是相同的项”。
*)
Fail Example probe_cur_nat_strict :
  hm_curry R Rcomm (hm_uncurry R Rcomm g ∘ mt_fmap i (@id (RMod R) W))
    = hm_curry R Rcomm (hm_uncurry R Rcomm g) ∘ i := eq_refl.

(*
 CONTROL: pointwise, at Leibniz `=`, which is what [cur_natural_V]'s
 [reflexivity] actually discharges. 

 --------
 控制：逐点，在莱布尼茨 `=`，这是 [cur_natural_V] 的 [reflexivity] 实际释放的内容。
*)
Example probe_cur_nat_at :
  mval (mval (hm_curry R Rcomm
                (hm_uncurry R Rcomm g ∘ mt_fmap i (@id (RMod R) W))) v) w
    = mval (mval (hm_curry R Rcomm (hm_uncurry R Rcomm g) ∘ i) v) w
  := eq_refl.

End ProbeConversion.

(*
   * *** Kind 3: FORMABILITY (universes)

   The header's measurement, guarded.  A library file CAN carry a
   section-local [Universes]/[Constraint] block without constraining
   itself — Instance/Fun/Group.v establishes that, and the two
   Test/Probe files that claimed otherwise are corrected there — so the
   probes live here rather than in a separate file.  All five controls
   are APPLIED, at the very levels where the five negatives are
   rejected. 

   --------
   * *** 类型 3：可成形性（宇宙）

   标题的测量，受到保护。一个库文件可以携带一个部分局部的 [Universes] / [Constraint] 块而不受约束——Instance/Fun/Group.v 已经证明了这一点，而之前声称相反的两个 Test/Probe 文件已经在其中得到纠正——因此探测器就放在这里，而不是放在单独的文件中。所有五个控制都已应用，在拒绝五个负面值的相同级别上。
*)

Section ProbeUniverses.

Universes ra rb rc.
Constraint ra < rc.

Context (Ru : RingObject@{rc ra rb}).
Context (Rcu : ∀ a b : carrier (rig_setoid (ring_rig Ru)),
            rig_mul (ring_rig Ru) a b ≈ rig_mul (ring_rig Ru) b a).
Context (V W : RModObject Ru).

(* CONTROLS: formable with the ring's first and third universes declared strictly apart. / 控制：可以在戒指的第一个和第三个宇宙明确分开声明的情况下形成 *)
Check (RMod Ru).
Check (TensorMod V W).
Check (@tensor_gen Ru V W).
Check (HomMod Ru Rcu V W).
Check (@ihom_post Ru Rcu V W W).

(*
 CONTROLS 6, 7 and 8, WHICH USED TO BE NEGATIVES.  An earlier revision read:
 “NEGATIVE 6.  The DONOR.  [tensor_med] (Instance/Mod/Tensor.v) already
 identifies the ring's first and third universes, while [TensorMod] and
 [tensor_gen] above do not”; “NEGATIVE 7.  Instance/Mod/Monoidal.v's arrow
 action inherits it”; “NEGATIVE 8.  Hence this file's currying.”  All three
 were re-measured after the PR “algebraic carriers are sets” (2026-09-17)
 and all three are now FORMABLE at the declared separation.  The cause is
 the move of [mt_eq] to [Prop]: [tensor_med_respects] no longer inducts on a
 [Type]-valued relation into a [Type]-valued goal but runs through [pequiv],
 and the identification the old proof forced is gone.  Negatives 9 and 10
 below still fire, which is the instrument check that the section still
 constrains anything at all. 

 --------
 控件 6、7 和 8，过去是负面的。早期的修订内容是：
 “负面 6。捐赠者。[tensor_med]（Instance/Mod/Tensor.v）已经识别出环的第一个和第三个宇宙，而上面的 [TensorMod] 和 [tensor_gen] 没有”；“负面 7。Instance/Mod/Monoidal.v 的箭头操作继承了它”；“负面 8。因此这个文件的柯里化。”在 PR “代数载体是集合”（2026-09-17）之后，所有三个都重新测量过，并且现在在声明的分离处都可以形成。原因是 [mt_eq] 移动到 [Prop]：[tensor_med_respects] 不再在 [Type] 值的关系上进行归纳以达到 [Type] 值的目标，而是通过 [pequiv] ，旧证明强制的识别也消失了。负数9和10下面仍然触发，这是仪器检查，表明这一部分仍然约束任何东西。
*)
Check (@tensor_med Ru V W).
Check (@mt_fmap Ru V W).
Check (@hm_curry Ru Rcu V W W).

(*
 NEGATIVE 9.  Instance/Mod/Monoidal.v's symmetric structure.  The ring
 is given EXPLICITLY: written `ModSymmetric Rcu` this probe is a FALSE
 GUARD — it still fails, but on an unresolved implicit (`?R`) with a
 plain type mismatch and no universe clause at all, so it would say
 nothing about the constraint.  Compare the trap
 Structure/Limit/Product/Finite.v records. 

 --------
 NEGATIVE 9. Instance/Mod/Monoidal.v 的对称结构。该环明确定义：写作 `ModSymmetric Rcu`，这个探测器是一个错误的保护——它仍然失败，但是在一个未解析的隐式（`?R`）上，具有普通的类型不匹配且完全没有宇宙子句，因此它不会对约束有任何说明。对比 Structure/Limit/Product/Finite.v 记录中的陷阱。
*)
Fail Check (@ModSymmetric Ru Rcu).

(*
 NEGATIVE 10.  And therefore the headline.  Note the binder/block trap:
 `RMod_SymMonClosed@{u u0}`'s constraint block carries no equation at
 all, and only the binder `R : RingObject@{u0 u0 u0}` reveals this. 

 --------
 负10。因此是标题。注意绑定器/块陷阱：
 `RMod_SymMonClosed@{u u0}` 的约束块根本不包含任何方程，只有绑定器 `R : RingObject@{u0 u0 u0}` 才显示出这一点。
*)
Fail Check (RMod_SymMonClosed Ru Rcu).

End ProbeUniverses.

(*
   * The OTHER identification, guarded separately.

   The section above declares the ring's FIRST and THIRD universes apart
   and so tests only that equation.  This one declares the FIRST and
   SECOND apart, which is the identification the header attributes to
   Instance/Mod/Monoidal.v's [ModMonoidal] rather than to anything
   declared here.  Without this section that attribution would be
   measured and unguarded, and nothing in the build would notice an
   upstream annotation changing it. 

   --------
   * 另一个识别，单独保护。

   上面的部分将环的第一个和第三个宇宙分开，因此只测试那个方程。这个部分将第一个和第二个宇宙分开，这是标题中归于 Instance/Mod/Monoidal.v 的 [ModMonoidal] 的识别，而不是归于此处声明的任何内容。没有这一部分，这种归属将是未测量且不受保护的，并且构建中的任何内容都不会注意到上游批注的更改。
*)

Section ProbeMiddleUniverse.

Universes ra rb rc.
Constraint rb < ra.

Context (Ru : RingObject@{rc ra rb}).
Context (Rcu : ∀ a b : carrier (rig_setoid (ring_rig Ru)),
            rig_mul (ring_rig Ru) a b ≈ rig_mul (ring_rig Ru) b a).
Context (V W : RModObject Ru).

(*
 CONTROLS: nothing this file declares identifies the ring's first two
 universes, so all four are formable with them declared strictly apart.
 Each is APPLIED to [Ru], which is the argument carrying the levels. 

 --------
 控制：这个文件声明的内容没有标识环的前两个宇宙，所以所有四个宇宙在它们严格分开声明的情况下都是可形成的。每一个都应用于 [Ru]，这是承载级别的参数。
*)
Check (@hm_curry Ru Rcu V W W).
Check (HomMod Ru Rcu V W).
Check (@exp_iso_Mod Ru Rcu).
Check (@ump_exponents_Mod Ru Rcu).

(* NEGATIVE 11. The donor: Instance/Mod/Monoidal.v's packaged monoidal structure, which identifies the first two where none of its own components does. / 负数 11。捐赠者：Instance/Mod/Monoidal.v 的打包单模结构，它识别前两个，而其自身的组件没有任何一个做到了。 *)
Fail Check (@ModMonoidal Ru Rcu).

(* NEGATIVE 12. Inherited by the symmetric packaging. / 负 12。通过对称封装继承。 *)
Fail Check (@ModSymmetric Ru Rcu).

(* NEGATIVE 13. And hence by the headline — whose own constraint block is still empty, the equation living in the binder alone. / 负13。因此通过标题——其自身的约束块仍然是空的，方程仅存在于活页夹中。 *)
Fail Check (@RMod_SymMonClosed Ru Rcu).

End ProbeMiddleUniverse.
