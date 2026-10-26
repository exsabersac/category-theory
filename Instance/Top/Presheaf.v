(* * * Open(X) and the presheaf of continuous real-valued functions / * * Open(X) 与连续实值函数的预层 *)

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §II.2, printed p. 35 (PDF p. 45) — maclane:II.2:construction7
 Book:      Riehl, “Category Theory in Context”, Example 1.3.7,
 clauses (iii)–(v), printed pp. 18–19 (PDF pp. 38–39)
 Book:      Fong–Spivak, “Seven Sketches in Compositionality”, §7.3.2,
 printed p. 236 (PDF p. 248)
 nLab:      https://ncatlab.org/nlab/show/presheaf
 nLab:      https://ncatlab.org/nlab/show/sheaf
 Wikipedia: https://en.wikipedia.org/wiki/Sheaf_(mathematics)

 Mac Lane's §II.2 example: for a topological space X the open sets,
 ordered by inclusion, form a thin category, and assigning to each open U
 the set of continuous real-valued functions on U — with restriction along
 an inclusion as the arrow action — is a contravariant functor into Set,
 the standard first example of a presheaf (and, classically, of a sheaf).
 Riehl's Example 1.3.7 spreads the story across three clauses: (iii)
 the open-set functor with preimage as arrow action, together with its
 closed-set companion — both already in tree as Instance/Top/Closed.v's
 [OpensF], [ClosedsF] and the complementation natural isomorphism
 [complement_natural], with [Opens X] the thin inclusion category
 itself; (iv) Spec, the prime spectrum of a commutative ring with the
 Zariski topology, which stays OUT OF SCOPE here (design note 7); and
 (v) the sheaf of continuous real-valued functions as the typifying
 presheaf.  This file delivers clause (v), Mac Lane's construction:

 [ContinuousPresheaf X : Presheaf (Opens X) Sets]

 sending an open U to the setoid of continuous maps from U (as a subspace)
 to the real line, and an inclusion V ⊆ U to restriction, which is
 precomposition with the continuous inclusion of subspaces.

 Seven Sketches §7.3.2 builds the same [Opens X] preorder and adds its
 ROLE: it is the site over which presheaves and sheaves on a space are
 defined.  That role is visible here in the type of [ContinuousPresheaf];
 the sheaf CONDITION is deliberately not stated (design note 4).

 Contents:
 - [R_Top]: the real line as a topological space (metric topology)
 - [OpenSub U]: an open set as a subspace, with [sub_incl] and the
 restriction morphisms [sub_map]
 - [ContinuousPresheaf X]: the presheaf of continuous real-valued
 functions, with constant sections as inhabitants
 - [OpenSub_whole_iso], [global_sections_iso]: the subspace on the
 whole-space open is the space itself, and its sections are the
 continuous maps X → R — “Γ(X, C(−,ℝ)) = C(X,ℝ)”

 Design:

 1. AN OPEN SUBSPACE IS A SPACE WHOSE OPENS CARRY PROPERNESS.  The
 carrier of [OpenSub U] is the sigma type { x : X & `1 U x } compared
 on first components, and a predicate on it is open when (a) it
 respects that comparison and (b) its extension along the projection —
 the predicate “some membership witness lands in V” — is open in X.
 Conjunct (a) is not decoration: the membership component of a point
 of the subspace is proof DATA, and a bare predicate could distinguish
 two witnesses of the same point, which no topology on the subspace
 setoid may do.  This is the same move Instance/Top.v makes for
 [Discrete_Top], whose opens are EXACTLY the respectful predicates.
 Because U itself is open, the extension-openness conjunct gives the
 standard subspace topology, and the identification is machine-checked
 rather than asserted: the opens of [OpenSub U] correspond to the
 opens of X contained in U ([sub_ext_contained], [sub_ext_recovers],
 [sub_open_of_open], [sub_ext_of_open] below).

 2. THE REAL LINE IS A BALL SPACE.  [R_Top] is Instance/Top/Interval.v's
 [BallTop] applied to R with distance [Rabs (x − y)] — the metric
 topology, with the radius of each interior ball carried as DATA, so
 the union axiom is discharged without any choice principle.  The
 interval file stops at [0,1] because paths need endpoints; the line
 itself is the three-lemma instance below.

 3. RESTRICTION IS PRECOMPOSITION.  An inclusion V ⊆ U induces a
 continuous map of subspaces [sub_map : OpenSub V ~> OpenSub U], and
 the presheaf's arrow action is precomposition with it.  Functoriality
 is thereby inherited from the category laws of [Top] — up to the
 subspace setoid's indifference to membership witnesses — rather than
 proved against a bespoke notion of “restriction of a function”.

 4. THE SHEAF CONDITION IS NOT STATABLE HERE.  Two independent
 obstructions, and the universe one bites first: Theory/Sheaf.v's
 [Sheaf] class carries its own inferred universe signature, which
 constrains its presheaf argument exactly the way the un-annotated
 [Presheaf] alias used to, so [Sheaf (ContinuousPresheaf X)] is a
 universe inconsistency, not a statement a reader could weaken — and
 the still-minimized [Presheaves] alias likewise cannot receive
 [ContinuousPresheaf] as an object.  Structurally, even at shared
 levels, the class records a per-object, per-leg gluing condition
 over the single covering family its [Site] supplies, which
 Theory/Sheaf/Category.v discloses as vacuous beyond subsingleton
 fibres — a donor erratum whose matching-family re-founding is
 deferred with sheafification (ledger item 1).  That re-founding
 will need the same universe generality [Presheaf] now has;
 verifying gluing for this presheaf belongs there.  What Mac Lane's
 p. 35 example asserts is the presheaf, which is delivered in full.
 The smooth-manifold variant (C^∞ functions on a manifold) is
 likewise out of tree: there are no manifolds here, and the example
 would need them before it needs anything categorical.

 5. WHAT IT COSTS.  This is the third file in the tree to import
 Coq.Reals (after Instance/Top/Interval.v and its consumer
 Instance/Top/FundamentalGroupoid.v), and it inherits the axiom set
 of the standard library's construction of R — principally
 [ClassicalDedekindReals.sig_forall_dec] and
 [FunctionalExtensionality.functional_extensionality_dep] — exactly
 as docs/AXIOMS.md's “Stdlib axioms” section documents for the other
 two; the section enumerates this file alongside them.  Constants
 that never touch R (the subspace machinery) remain closed under the
 global context.

 6. UNIVERSES.  [Top]'s hom-sets live strictly above its points
 (Instance/Top.v's header), so a setoid of sections is an object of
 Sets one level up — the same placement Instance/Top/Forgetful.v
 gives [Top_Forget] and Instance/Top/Closed.v gives [OpensF].  The
 polymorphic [Sets] absorbs this silently: [ContinuousPresheaf X]
 lands in the Sets whose objects are section setoids, not the Sets
 whose objects are point setoids.

 7. SPEC STAYS OUT OF SCOPE.  Riehl's clause (iv) is the prime-spectrum
 functor from commutative rings (opposite) to spaces, a ring going to
 its set of prime ideals under the Zariski topology.  The tree now
 has commutative rings (Instance/Rng.v's [CRng]) and, with this
 file, enough topology to state the target — but no ideals, no
 primality, and no spectrum construction: Spec is a development of
 its own (prime ideals as setoid predicates, Zariski opens generated
 by ring elements, contravariant functoriality along ring maps), not
 an increment of the presheaf example, and no in-tree issue currently
 tracks it. 

 --------
 书籍：Mac Lane，《为工作中的数学家准备的范畴论》，第2版，§II.2，第35页（PDF第45页）—— maclane:II.2:construction7
 书籍：Riehl，《语境中的范畴论》，示例1.3.7，第(iii)–(v)条款，第18–19页（PDF第38–39页）
 书籍：Fong–Spivak，《组合性中的七个草图》，§7.3.2，第236页（PDF第248页）
 nLab：https://ncatlab.org/nlab/show/presheaf
 nLab：https://ncatlab.org/nlab/show/sheaf
 维基百科：https://en.wikipedia.org/wiki/Sheaf_(mathematics)Mac Lane 的 §II.2 示例：对于一个拓扑空间 X，其开集按照包含关系排列，形成一个薄范畴，并且将每个开集 U 分配给 U 上的连续实值函数集——以包含映射作为箭头的作用——是一个指向 Set 的逆变函子，这是预层（以及经典的层）的标准第一个例子。Riehl 的例 1.3.7 将故事分布在三个分句中：（iii）具有原像作为箭头作用的开集函子，以及它的闭集伴随——两者都已经作为树中的 Instance/Top/Closed.v 的 [OpensF]、[ClosedsF] 以及补运算自然同构 [complement_natural]，[Opens X] 为薄包含范畴本身；（iv）Spec，一个交换环的素谱，配备 Zariski 拓扑，这里不在讨论范围内（设计说明 7）；以及（v）连续实值函数的层作为典型的预层。该文件提供了分句 (v)，Mac Lane 的构造：

 [ContinuousPresheaf X : Presheaf (Opens X) Sets]

 将开集 U 映射到从 U（作为子空间）到实数直线的连续映射的等价类集合，并将包含 V ⊆ U 映射到限制，即与子空间的连续包含的前复合。七个草图 §7.3.2 构建了相同的 [Opens X]  预序，并增加了它的作用：它是一个空间上预层与层定义的场所。这个作用在 [ContinuousPresheaf] 的类型中可见；层条件故意未被说明（设计说明 4）。

 内容：
 - [R_Top]：作为拓扑空间的实线（度量拓扑）
 - [OpenSub U]：作为子空间的开集，以及 [sub_incl] 和限制态射 [sub_map]
 - [ContinuousPresheaf X]：连续实值函数的预层，其常量截面作为元素
 - [OpenSub_whole_iso]，[global_sections_iso]：整个空间开集上的子空间就是空间本身，其截面是连续映射 X → R — “Γ(X, C(−,ℝ)) = C(X,ℝ)”

 设计：1. 开子空间是一个其开集携带良性（properness）的空间。[OpenSub U] 的承载体是 sigma 类型 { x : X & `1 U x }，根据第一个分量进行比较，并且它上的谓词在以下条件下是开集的：(a) 它尊重该比较，(b) 它沿投影的扩展——谓词“某个成员证据落在 V 中”——在 X 中是开集的。结合条件 (a) 并不是装饰：子空间中一个点的成员组件是证明数据，而裸谓词可能区分同一点的两个证据，这是子空间的集合类拓扑所不允许的。这个操作与 Instance/Top.v 对 [Discrete_Top] 所做的相同，其开集恰好是尊重的谓词。因为 U 本身是开放的，扩展开放性连词给出了标准子空间拓扑，并且该识别是经过机械检查的，而不是主张的：[OpenSub U] 的开集对应于包含在 U 中的 X 的开集（下面的 [sub_ext_contained]、[sub_ext_recovers]、[sub_open_of_open]、[sub_ext_of_open]）。

 2. 实数直线是一个球空间。[R_Top] 是 Instance/Top/Interval.v 中 [BallTop] 应用于 R，度量为 [Rabs (x − y)] ——度量拓扑，每个内部球的半径作为数据携带，因此联合公理可以在没有任何选择原理的情况下满足。区间文件在 [0,1] 停止，因为路径需要端点；直线本身是下面提到的三引理实例。3. 限制是预组合。包含 V ⊆ U 会引起子空间的连续映射 [sub_map : OpenSub V ~> OpenSub U]，并且预层的箭头作用是与它的预组合。因此，函子性是从 [Top] 的范畴法则继承而来的——最多只是因为子空间集合等价对成员证据的不敏感——而不是针对“函数的限制”的特定概念来证明的。4. 在这里无法表述鞘条件。两个独立的阻碍因素，以及宇宙中的一个首先被触发：Theory/Sheaf.v 的 [Sheaf] 类带有其自身推断的宇宙签名，这限制了它的预层参数，就像未注释的 [Presheaf] 别名以前所做的那样，因此 [Sheaf (ContinuousPresheaf X)] 是一个宇宙不一致性，而不是读者可以削弱的陈述——而且经过最小化的 [Presheaves] 别名同样不能将 [ContinuousPresheaf] 作为对象。在结构上，即使在共享层级上，该类也记录了每个对象、每条腿的粘合条件，适用于其 [Site] 提供的单一覆盖族，Theory/Sheaf/Category.v 显示在超出单子纤维的范围时这是空的——这是一个捐赠者勘误，其匹配族的重建将随着层化而被推迟（分类账项 1）。这种重建将需要 [Presheaf] 目前具有的相同宇宙一般性；验证这个预层的粘合性属于那里。Mac Lane 第 35 页的例子所断言的是该预层，它已完整提供。光滑流形变体（流形上的 C^∞ 函数）同样不在该树上：这里没有流形，并且该例子在需要任何范畴内容之前需要这些流形。5. 成本。 这是导入树中的第三个文件 Coq.Reals（在 Instance/Top/Interval.v 及其使用者 Instance/Top/FundamentalGroupoid.v 之后），它继承了标准库对 R 的构造所使用的公理集——主要是 [ClassicalDedekindReals.sig_forall_dec] 和 [FunctionalExtensionality.functional_extensionality_dep]——正如 docs/AXIOMS.md 的“Stdlib 公理”部分为前两个文件所记录的那样；该部分将此文件与它们一并列举。那些从未涉及 R 的常量（子空间机制）在全局上下文中仍然保持封闭。6. 宇宙。[Top] 的同态集严格位于其点之上（Instance/Top.v 的头部），因此一个截面集合的集合同质结构是上一级的 Sets 的对象——Instance/Top/Forgetful.v 给出了 [Top_Forget]，Instance/Top/Closed.v 给出了 [OpensF]。多态的 [Sets] 会默默地吸收这一点：[ContinuousPresheaf X] 落在对象为截面集合同质结构的 Sets 中，而不是对象为点集合同质结构的 Sets 中。7. SPEC 不在范围内。Riehl 的条款 (iv) 是从交换环（对偶）到空间的素谱函子，一个环映射到其在 Zariski 拓扑下的素理想集合。现在的树有交换环（Instance/Rng.v 的 [CRng]）并且有了这个文件，有足够的拓扑来陈述目标——但没有理想，没有素性，也没有谱的构造：Spec 是其自身的发展（素理想作为集合谓词，由环元素生成的 Zariski 开集，沿环映射的逆变函子性），不是挠子示例的一个增量，并且目前树中没有问题跟踪它。
*)

Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Closed.
Require Import Category.Instance.Top.Interval.
Require Import Category.Theory.Sheaf.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * ** The real line as a topological space / * ** 实数直线作为拓扑空间 *)

Definition R_equiv (x y : R) : Type := x = y.

Lemma R_equiv_Equivalence : Equivalence R_equiv.
Proof.
  constructor; unfold R_equiv.
  - intro x; reflexivity.
  - intros x y H; now symmetry.
  - intros x y z H1 H2; now transitivity y.
Qed.

Definition R_Setoid : Setoid R := {|
  equiv        := R_equiv;
  setoid_equiv := R_equiv_Equivalence
|}.

Definition R_Object : SetoidObject := {|
  carrier   := R;
  is_setoid := R_Setoid
|}.

(* Registered for downstream setoid tactics at real points; the proofs in this file use explicit terms instead. / 已注册用于实数点的下游集合论策略；本文件中的证明改为使用显式项。 *)
#[export] Existing Instance R_equiv_Equivalence.

Lemma BS_R_zero (x y : R_Object) : x ≈ y → Rabs (x - y) = 0.
Proof.
  intro H.
  assert (Heq : x = y :> R) by exact H.
  Rlin.
Qed.

Lemma BS_R_sym (x y : R_Object) : Rabs (x - y) = Rabs (y - x).
Proof. Rlin. Qed.

Lemma BS_R_tri (x y z : R_Object) :
  Rabs (x - z) <= Rabs (x - y) + Rabs (y - z).
Proof. Rlin. Qed.

Definition BS_R : BallSpace := {|
  ball_carrier := R_Object;
  bdist        := fun x y => Rabs (x - y);
  bdist_zero   := BS_R_zero;
  bdist_sym    := BS_R_sym;
  bdist_tri    := BS_R_tri
|}.

(* The real line with the metric topology (design note 2). / 带度量拓扑的实数直线（设计说明2）。 *)
Definition R_Top : TopSpace := BallTop BS_R.

(** ** An open set as a subspace / ** 作为子空间的开集 *)

Section OpenSubspace.

Context (X : TopSpace) (U : OpenSet X).

(*
 Points of the subspace: a point of X together with a membership
 witness.  The setoid compares first components only, so the witness is
 invisible to everything downstream — the discipline that design note 1
 then forces on the opens. 

 --------
 子空间的点：X 的一个点以及一个成员证明。集合等价关系只比较第一个分量，因此证明对下游的所有内容都是不可见的——这是设计说明 1 然后在开集上强加的约束。
*)
Definition SubCar : Type := { x : X & `1 U x }.

Definition sub_equiv (s t : SubCar) : Type := `1 s ≈ `1 t.

Lemma sub_equiv_Equivalence : Equivalence sub_equiv.
Proof.
  constructor; unfold sub_equiv.
  - intro s; reflexivity.
  - intros s t H; now symmetry.
  - intros s t u H1 H2; now transitivity (`1 t).
Qed.

Definition Sub_Setoid : Setoid SubCar := {|
  equiv        := sub_equiv;
  setoid_equiv := sub_equiv_Equivalence
|}.

Definition SubOb : SetoidObject := {|
  carrier   := SubCar;
  is_setoid := Sub_Setoid
|}.

(* The extension of a subspace predicate along the projection: it holds at a point of X when some membership witness lands in V. / 沿投影的子空间谓词的延拓：当某个成员资格证明落在 V 中时，它在 X 的一点上成立。 *)
Definition sub_ext (V : SubCar → Type) : X → Type :=
  fun x => { h : `1 U x & V (x; h) }.

(* Openness in the subspace: respect for the point comparison, plus openness of the extension in X (design note 1). / 子空间中的开放性：尊重点比较，加上 X 中扩展的开放性（设计说明 1）。 *)
Definition sub_open (V : SubCar → Type) : Type :=
  (∀ (x y : X) (hx : `1 U x) (hy : `1 U y),
      x ≈ y → V (x; hx) → V (y; hy)) ∧
  IsOpen X (sub_ext V).

Lemma sub_respects (V W : SubCar → Type) :
  (∀ s, V s ↔ W s) → sub_open V → sub_open W.
Proof.
  intros HVW [Vprop Vext]; split.
  - intros x y hx hy Hxy w.
    exact (fst (HVW (y; hy)) (Vprop x y hx hy Hxy (snd (HVW (x; hx)) w))).
  - apply (open_respects X (sub_ext V)); [ | exact Vext ].
    intro x; split.
    + intros [h v]; exact (h; fst (HVW (x; h)) v).
    + intros [h w]; exact (h; snd (HVW (x; h)) w).
Qed.

Lemma sub_proper (V : SubCar → Type) :
  sub_open V → ∀ s t : SubOb, s ≈ t → V s → V t.
Proof.
  intros [Vprop _] [x hx] [y hy] Hst v.
  exact (Vprop x y hx hy Hst v).
Qed.

Lemma sub_union (I : Type) (V : I → (SubCar → Type)) :
  (∀ i, sub_open (V i)) → sub_open (fun s => { i : I & V i s }).
Proof.
  intro HV; split.
  - intros x y hx hy Hxy [i v].
    exact (i; fst (HV i) x y hx hy Hxy v).
  - apply (open_respects X (fun x => { i : I & sub_ext (V i) x })).
    + intro x; split.
      * intros [i [h v]]; exact (h; (i; v)).
      * intros [h [i v]]; exact (i; (h; v)).
    + apply open_union.
      intro i; exact (snd (HV i)).
Qed.

Lemma sub_whole : sub_open (fun _ => poly_unit).
Proof.
  split.
  - intros x y hx hy Hxy w; exact ttt.
  - apply (open_respects X (`1 U)); [ | exact (`2 U) ].
    intro x; split.
    + intro h; exact (h; ttt).
    + intros [h _]; exact h.
Qed.

Lemma sub_inter (V W : SubCar → Type) :
  sub_open V → sub_open W → sub_open (fun s => V s ∧ W s).
Proof.
  intros [Vprop Vext] [Wprop Wext]; split.
  - intros x y hx hy Hxy [v w].
    exact (Vprop x y hx hy Hxy v, Wprop x y hx hy Hxy w).
  - apply (open_respects X (fun x => sub_ext V x ∧ sub_ext W x)).
    + intro x; split.
      * intros [[h v] [k w]].
        exact (h; (v, Wprop x x k h (reflexivity _) w)).
      * intros [h [v w]]; exact ((h; v), (h; w)).
    + exact (open_inter X (sub_ext V) (sub_ext W) Vext Wext).
Qed.

(* The subspace, as a topological space. / 作为拓扑空间的子空间。 *)
Definition OpenSub : TopSpace := {|
  top_carrier   := SubOb;
  IsOpen        := sub_open;
  open_respects := sub_respects;
  open_proper   := sub_proper;
  open_union    := sub_union;
  open_whole    := sub_whole;
  open_inter    := sub_inter
|}.

(*
 The inclusion of the subspace, continuous because the preimage of an
 open W of X is its intersection with U, transported to the subspace. 

 --------
 子空间的包含是连续的，因为 X 的一个开集 W 的原像是它与 U 的交集，这一点被传递到子空间。
*)
Program Definition sub_incl : ContinuousMorphism OpenSub X := {|
  continuous_map := {| morphism := fun s : SubCar => `1 s |}
|}.
Next Obligation.
  intros s t Hst; exact Hst.
Qed.
Next Obligation.
  intros W HW; split.
  - intros x y hx hy Hxy w.
    exact (open_proper X W HW x y Hxy w).
  - apply (open_respects X (fun x => `1 U x ∧ W x)).
    + intro x; split.
      * intros [h w]; exact (h; w).
      * intros [h w]; exact (h, w).
    + exact (open_inter X (`1 U) W (`2 U) HW).
Qed.

(*
 The identification promised by design note 1: subspace opens are
 exactly the opens of X contained in U, pulled back along the
 projection.  Forward: the extension of a subspace open is an open of X
 ([sub_open]'s second conjunct), it is contained in U, and — by the
 properness conjunct — the open it came from is pointwise equivalent to
 its pullback.  Backward: the pullback of any open of X contained in U
 is a subspace open, and its extension recovers the original. 

 --------
 设计说明1所承诺的识别：子空间开集恰好是包含在U中的X的开集，通过投影拉回。正向：子空间开集的扩展是X的一个开集（[sub_open]的第二个合取），它包含在U中，并且——根据适当性合取——它来源的开集在每一点上与其拉回等价。反向：X中包含在U中的任意开集的拉回是一个子空间开集，并且其扩展可以恢复原始开集。
*)

Lemma sub_ext_contained (V : SubCar → Type) (x : X) :
  sub_ext V x → `1 U x.
Proof.
  intros [h _]; exact h.
Qed.

Lemma sub_ext_recovers (V : SubCar → Type) :
  sub_open V → ∀ (x : X) (h : `1 U x), V (x; h) ↔ sub_ext V x.
Proof.
  intros [Vprop _] x h; split.
  - intro v; exact (h; v).
  - intros [k v]; exact (Vprop x x k h (reflexivity _) v).
Qed.

Lemma sub_open_of_open (W : X → Type) :
  IsOpen X W → (∀ x : X, W x → `1 U x) →
  sub_open (fun s => W (`1 s)).
Proof.
  intros HW Hsub; split.
  - intros x y hx hy Hxy w; exact (open_proper X W HW x y Hxy w).
  - apply (open_respects X W); [ | exact HW ].
    intro x; split.
    + intro w; exact (Hsub x w; w).
    + intros [h w]; exact w.
Qed.

Lemma sub_ext_of_open (W : X → Type)
  (Hsub : ∀ x : X, W x → `1 U x) (x : X) :
  sub_ext (fun s => W (`1 s)) x ↔ W x.
Proof.
  split.
  - intros [h w]; exact w.
  - intro w; exact (Hsub x w; w).
Qed.

End OpenSubspace.

Arguments SubCar {X} U.
Arguments sub_ext {X} U V x.
Arguments sub_open {X} U V.
Arguments OpenSub {X} U.
Arguments sub_incl {X} U.

(* Registered for downstream setoid tactics at subspace points, as with [R_equiv_Equivalence] above. / 如上面的 [R_equiv_Equivalence] 所示，已在子空间点注册用于下游集合同态策略。 *)
#[export] Existing Instance sub_equiv_Equivalence.

(* * ** Restriction along an inclusion / * ** 在包含上的限制 *)

Section Restriction.

Context {X : TopSpace} (V U : OpenSet X).
Context (i : ∀ x : X, `1 V x → `1 U x).

(*
 An inclusion of opens induces a continuous map of subspaces: transport
 the membership witness.  Continuity re-runs the design-note-1
 bookkeeping: properness of the preimage is properness of the source
 open, and its extension is (V ∩ extension), open in X. 

 --------
 开集的包含诱导了子空间的连续映射：传递元素的成员资格证明。连续性重新运行设计注释-1的记账：原像的适当性是源开集的适当性，其扩展是（V ∩ 扩展），在 X 中是开集。
*)
Program Definition sub_map : ContinuousMorphism (OpenSub V) (OpenSub U) := {|
  continuous_map :=
    {| morphism := fun s : SubCar V => (`1 s; i (`1 s) (`2 s)) |}
|}.
Next Obligation.
  intros s t Hst; exact Hst.
Qed.
Next Obligation.
  intros P [Pprop Pext]; split.
  - intros x y hx hy Hxy p.
    exact (Pprop x y (i x hx) (i y hy) Hxy p).
  - apply (open_respects X (fun x => `1 V x ∧ sub_ext U P x)).
    + intro x; split.
      * intros [h [k p]].
        exact (h; Pprop x x k (i x h) (reflexivity _) p).
      * intros [h p]; exact (h, (i x h; p)).
    + exact (open_inter X (`1 V) (sub_ext U P) (`2 V) Pext).
Qed.

End Restriction.

(* * ** The presheaf of continuous real-valued functions / * ** 连续实值函数的预层 *)

(*
 The setoid of sections over an open: continuous maps from the subspace
 to the real line, compared pointwise — [Top]'s own hom-setoid, packaged
 as an object of Sets (design note 6). 

 --------
 关于一个开集的截面的集合：从子空间到实数轴的连续映射，逐点比较——[Top] 自身的同态集合，被封装为 Sets 的一个对象（设计说明 6）。
*)
Definition SectionsOb (X : TopSpace) (U : OpenSet X) : obj[Sets] := {|
  carrier   := ContinuousMorphism (OpenSub U) R_Top;
  is_setoid := ContinuousMorphism_Setoid
|}.

(*
 Mac Lane's presheaf: U ↦ continuous real-valued functions on U,
 inclusions to restriction, i.e. precomposition with [sub_map].  The
 Opens-side hom-setoid is trivial, and honestly so: two parallel
 inclusions may differ as functions on witnesses, but the subspace
 setoid does not see witnesses, so their restrictions agree. 

 --------
 麦克·莱恩的预层：U ↦ U 上的连续实值函数，包含映射对应于限制，即与 [sub_map] 的预组合。开集侧的同类集合是平凡的，并且确实如此：两个平行的包含映射作为见证的函数可能不同，但子空间的同类集合看不到见证，因此它们的限制是一致的。
*)
Program Definition ContinuousPresheaf (X : TopSpace) :
  Presheaf (Opens X) Sets := {|
  fobj := fun U => SectionsOb X U;
  fmap := fun U V (f : U ~{(Opens X)^op}~> V) =>
    {| morphism := fun s : ContinuousMorphism (OpenSub U) R_Top =>
         top_compose s (sub_map V U f) |}
|}.
Next Obligation.
  (* precomposition respects pointwise equality of sections / 预组合尊重截面的逐点相等性 *)
  intros X U V f s t Hst p; exact (Hst (sub_map V U f p)).
Qed.
Next Obligation.
  (* any two parallel inclusions restrict identically / 任何两个平行的夹杂物限制是相同的 *)
  intros X U V f g _ s p; simpl.
  apply (proper_morphism (continuous_map s)).
  exact (reflexivity (`1 p)).
Qed.
Next Obligation.
  (* restriction along the identity inclusion is the identity / 沿身份包含的限制是身份 *)
  intros X U s p; simpl.
  apply (proper_morphism (continuous_map s)).
  exact (reflexivity (`1 p)).
Qed.
Next Obligation.
  (* restriction along a composite is the composite of restrictions / 沿复合的限制是限制的复合 *)
  intros X U V W f g s p; simpl.
  apply (proper_morphism (continuous_map s)).
  exact (reflexivity (`1 p)).
Qed.

(** ** Constant sections / ** 常量部分 *)

(*
 Every hom-setoid of the presheaf is inhabited: the constant functions
 are continuous, because the preimage of an open is constantly true or
 constantly false — [open_const]'s union trick, run through the subspace
 packaging. 

 --------
 预层的每个同态集都是有元素的：常值函数是连续的，因为开集的原像总是恒真或恒假——[open_const] 的并集技巧，通过子空间打包运行。
*)
Program Definition const_section (X : TopSpace) (U : OpenSet X) (c : R) :
  ContinuousMorphism (OpenSub U) R_Top := {|
  continuous_map := {| morphism := fun _ => c |}
|}.
Next Obligation.
  intros X U c s t Hst; reflexivity.
Qed.
Next Obligation.
  intros X U c W HW; split.
  - intros x y hx hy Hxy w; exact w.
  - apply (open_respects X (fun x => `1 U x ∧ W c)).
    + intro x; split.
      * intros [h w]; exact (h; w).
      * intros [h w]; exact (h, w).
    + exact (open_inter X (`1 U) (fun _ => W c) (`2 U) (open_const X (W c))).
Qed.

(*
 Restriction of a constant is the constant — the presheaf's arrow action
 computes on the nose here. 

 --------
 常数的限制就是常数——预层的箭头作用在这里准确地计算。
*)
Example const_restrict (X : TopSpace) (U V : OpenSet X)
  (f : U ~{(Opens X)^op}~> V) (c : R) :
  fmap[ContinuousPresheaf X] f (const_section X U c) ≈ const_section X V c.
Proof.
  intro p; reflexivity.
Qed.

(** ** Global sections / ** 全局部分 *)

(* The whole space, as an object of [Opens X]. / 整个空间，作为 [Opens X] 的对象。 *)
Definition whole_open (X : TopSpace) : OpenSet X :=
  ((fun _ => poly_unit); open_whole X).

(*
 The subspace on the whole-space open is the space itself: the inclusion
 is an isomorphism of [Top], the inverse adjoining the trivial witness. 

 --------
 整体空间上的子空间是其自身：包含映射是 [Top] 的同构，逆映射附加平凡证明。
*)
Program Definition OpenSub_whole_iso (X : TopSpace) :
  OpenSub (whole_open X) ≅[Top] X := {|
  to   := sub_incl (whole_open X);
  from := {| continuous_map := {| morphism := fun x : X => (x; ttt) |} |}
|}.
Next Obligation.
  intros X x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros X P [Pprop Pext].
  apply (open_respects X (sub_ext (whole_open X) P)); [ | exact Pext ].
  intro x; split.
  - intros [h p].
    exact (Pprop x x h ttt (reflexivity _) p).
  - intro p; exact (ttt; p).
Qed.
Next Obligation.
  intros X x; simpl; reflexivity.
Qed.
Next Obligation.
  intros X s; simpl.
  exact (reflexivity (`1 s)).
Qed.

(* The continuous maps X → R, as an object of Sets. / 连续映射 X → R，作为集合的一个对象。 *)
Definition Maps_to_R (X : TopSpace) : obj[Sets] := {|
  carrier   := ContinuousMorphism X R_Top;
  is_setoid := ContinuousMorphism_Setoid
|}.

(*
 Sections over the whole space ARE the continuous real-valued functions
 on X — the “Γ(X, C(−,ℝ)) = C(X,ℝ)” sanity theorem, an isomorphism of
 section setoids in Sets by conjugation with [OpenSub_whole_iso]. 

 --------
 整个空间上的截面是 X 上的连续实值函数——“Γ(X, C(−,ℝ)) = C(X,ℝ)” 理智定理，一个通过与 [OpenSub_whole_iso] 共轭得到的集合中截面集合同构。
*)
Program Definition global_sections_iso (X : TopSpace) :
  SectionsOb X (whole_open X) ≅[Sets] Maps_to_R X := {|
  to   := {| morphism := fun s =>
               top_compose s (from (OpenSub_whole_iso X)) |};
  from := {| morphism := fun m =>
               top_compose m (to (OpenSub_whole_iso X)) |}
|}.
Next Obligation.
  intros X s t Hst x; exact (Hst (x; ttt)).
Qed.
Next Obligation.
  intros X m n Hmn s; exact (Hmn (`1 s)).
Qed.
Next Obligation.
  intros X m x; simpl; reflexivity.
Qed.
Next Obligation.
  intros X s p; simpl.
  apply (proper_morphism (continuous_map s)).
  exact (reflexivity (`1 p)).
Qed.
