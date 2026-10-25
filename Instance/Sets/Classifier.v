Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.

Generalizable All Variables.

(* * * The cross-universe subobject classifier of [Sets] / * * [Sets] 的跨宇宙子对象分类器 *)

(*
 nLab:      https://ncatlab.org/nlab/show/subobject+classifier
 Wikipedia: https://en.wikipedia.org/wiki/Subobject_classifier

 A subobject classifier for a category C is an object Ω together with a point
 true : 1 ~> Ω such that every monomorphism m : A ~> B arises as the pullback
 of true along a unique characteristic map χ_m : B ~> Ω.  This file proves the
 classifier theorems for the setoid category [Sets] — as honest CROSS-UNIVERSE
 theorems, not as a [SubobjectClassifier Sets] instance at a single level: the
 canonical candidate provably cannot fit at one level (below).  A DIFFERENT
 candidate does fit, CONDITIONALLY: Instance/Sets/Classifier/OneLevel.v
 delivers a genuine [SubobjectClassifier Sets] instance at one universe level
 under an explicit hypothesis — [Untruncate] (every impredicative truncation
 at level o can be inverted) or, with a two-element truth object, [DecImage]
 (every mono's image membership is decidable), each implied by informative
 excluded middle at level o — and proves there that a one-level classifier for
 [Sets] is inter-derivable with a resizing-shaped structure.  Neither
 hypothesis has an axiom-free inhabitant in this tree, so nothing below is
 weakened: the theorems in this file stay unconditional, and they are related
 to that instance as one story — its characteristic map is the truncation of
 [char_setoid] below, at [eq_refl] on values.  (That NO small classifier can
 exist over predicative Type — setoids there form a ΠW-pretopos, and a
 classifier needs impredicativity — is standard but is folklore relative to
 this development: it is not proven in-tree, and this file does not claim it
 as a theorem.)

 WHY ONE LEVEL DOES NOT SUFFICE UNCONDITIONALLY.  Morphism equivalence
 `≈` in this library is Type@{o}-valued (a [crelation]; see
 Lib/Setoid.v — equivalence proofs may carry computational content), so
 the characteristic predicate of a mono m : A ~> B in Sets@{o so},
 namely λ b, ∃ a, m a ≈ b, is itself a
 Type@{o}-valued predicate on the carrier of B.  A truth-value object able
 to receive this predicate must have carrier Type@{o} (with equivalence
 iffT), and Type@{o} : Type@{o+1} — one universe up — so the resulting
 setoid is a SetoidObject@{so so}, an object of Sets@{so sso}, and NOT an
 obj[Sets@{o so}] (which is SetoidObject@{o o}).  Taking Prop as the
 carrier instead is not an escape: landing ∃ a, m a ≈ b in Prop would
 require truncating a Type-valued sigma, and the pullback property below
 must extract the witness back out of the truth value.

 This obstruction is specific to the classifier, and the end of this file
 records where its reach stops: epis-are-surjections was long thought to
 inherit it, but that theorem has a probe which is not a truth-value
 object, and it is proved at one universe in Instance/Sets.v.

 WHAT IS TRUE, AND WHERE EACH PIECE LIVES:

 - [PropSetoid]      the truth-value setoid: carrier Type@{o} under iffT,
 a SetoidObject@{so so} (o < so) — one universe up.
 - [char_setoid]     the characteristic map of m : A ~> B, a morphism
 Setoid_Lift B ~> PropSetoid of Sets@{so sso}, where
 [Setoid_Lift] re-types a SetoidObject@{o o} at the
 higher level (the library's records are not
 cumulative, so the lift is by rebuilding).
 - [sets_char_pullback]  the full pullback square, via Stability.v's
 apex-pinned [IsPullback] in Sets@{so sso}: the lift
 of A, with the lift of m and the terminal map, IS the
 pullback of true along char_setoid m.  The one-level
 IsPullback form is not statable — its ambient
 category would have to contain PropSetoid — but the
 apex, legs and cone quantification all live honestly
 one level up, so nothing is weakened beyond the
 forced lifting.
 - [sets_char_subobject]  the one-level shadow: the pullback APEX (unlike
 the truth-value object) is small — the sub-setoid
 {b : B & ∃ a, m a ≈ b} is [Sets_Image m] of
 Instance/Sets/Image.v — and (A, m) is equal to it in
 the subobject setoid [SubObj_Setoid] of B, already in
 Sets@{o so}.
 - [sets_char_unique]    uniqueness: any χ making the lifted square a
 pullback agrees with char_setoid m up to iff on
 components (the hom-setoid of Sets@{so sso}).

 No universe hacks are used: no impredicativity, no cumulativity, no
 disabling of universe checking.  The universe binders below are explicit,
 and each carries only the constraints the statements force (essentially
 o < so < sso). 

 --------
 nLab:       https://ncatlab.org/nlab/show/subobject+classifier 
 维基百科:  https://en.wikipedia.org/wiki/Subobject_classifier类别 C 的子对象分类器是一个对象 Ω，以及一个点 true : 1 ~> Ω，使得每一个单射 m : A ~> B 都源于 true 沿着唯一特征映射 χ_m : B ~> Ω 的拉回。这份文件证明了集合范畴 [Sets] 的分类器定理——作为诚实的跨宇宙定理，而不是在单一层级上的 [SubobjectClassifier Sets] 实例：可以证明标准候选者不能适合在一个层级上（如下所示）。一个不同的候选者有条件地适用：Instance/Sets/Classifier/OneLevel.v 在一个宇宙层级下，在一个明确的假设下提供了一个真正的 [SubobjectClassifier Sets] 实例——[Untruncate]（每个在 o 层级的自参截断都可以被反转）或者在有一个两元素真值对象时，[DecImage]（每个单射的像的隶属关系可判定），每个都由层级 o 的信息化排中律所蕴含——并且在那里证明了 [Sets] 的一层分类器与一个调整形状的结构可以互相推导。任何一个假设在该树中都没有无公理居所，因此下面的内容都未被削弱：该文件中的定理保持无条件，并且它们与那个实例作为一个整体相关——其特征映射是 [char_setoid] 以下的截断，在 [eq_refl] 值上。（没有小型分类器能够存在于谓词类型之上——那里集合体形成一个 ΠW-前拓扑，并且分类器需要自反性——这是标准的，但相对于这个发展来说是传说性的：它在树中没有被证明，并且这个文件不将其声明为定理。）为什么单一级别并非无条件足够。这个库中的态射等价 `≈` 是 Type@{o}-值的（一个 [crelation]；见 Lib/Setoid.v——等价证明可能包含计算内容），所以 Sets@{o} 中单态射 m : A ~> B 的特征谓词，即 λ b, ∃ a, m a ≈ b，本身是 B 的承载对象上的 Type@{o}-值谓词。能够接收该谓词的真值对象必须具有承载 Type@{o}（用 iffT 等价），并且 Type@{o} : Type@{o+1}——比一个宇宙上升一级——所以由此得到的集合对象是 SetoidObject@{so so}，是 Sets@{so sso} 的对象，而不是 obj [Sets@{o so}]（它是 SetoidObject@{o o}）。将 Prop 作为载体取而代之并不是一种逃避：在 Prop 中着陆 ∃ a, m 使 a ≈ b 将需要截断一个类型值的 Σ 类型，而下面的拉回属性必须从真值中提取见证。 这种阻碍是针对分类器特有的，而本文件末尾记录了其影响的范围：epis-are-surjections 曾长期被认为会继承它，但该定理有一个探针，它不是一个真值对象，并且它在 Instance/Sets.v 的一个宇宙中被证明。 真实的情况是什么，以及每一部分的位置:-  [PropSetoid] 真值等值类：在 iffT 下的承载类型 Type@{o}，一个 SetoidObject@{so so}（o < so）— 高一层的宇宙。-  [char_setoid] m : A ~> B 的特征映射，一个态射 Setoid_Lift B ~> Sets@{so sso} 的 PropSetoid，其中 [Setoid_Lift] 重新指定高层级的 SetoidObject@{o o} 类型（库的记录不是累积的，因此提升是通过重建实现的）。-  [sets_char_pullback] 完整拉回方形，通过 Stability.v 的顶点固定 [IsPullback] 在 Sets@{so sso} 中：A 的提升，连同 m 的提升和终态射，构成 true 沿 char_setoid m 的拉回。一层级
 IsPullback 形式无法声明——它的环境类别必须包含 PropSetoid——但顶点、腿和锥形量化都诚实地位于更高一级，因此除了强制提升之外，没有任何东西被削弱。- [sets_char_subobject] 一层级阴影：拉回顶点（APEX）（与真值对象不同）是小的——子集合子集 {b : B & ∃ a, m a ≈ b} 是 [Sets_Image m] 的 Instance/Sets/Image.v——并且 (A, m) 在 B 的子对象子集 [SubObj_Setoid] 中等于它，这已经在 Sets@{o so} 中。-  [sets_char_unique]     唯一性：使得提升的平方为拉回的任意 χ，与 char_setoid m 在分量上（Sets@{so sso} 的同态集合）同构条件下是一致的。

 未使用任何宇宙技巧：没有使用全称归纳性，没有使用累积性，也没有禁用宇宙检查。下面的宇宙绑定是显式的，并且每个绑定只包含语句强制的约束（本质上是 o < so < sso）。
*)

(* ------------------------------------------------------------------------ *)
(* * ** Lifting setoids one universe up / * ** 将集合等构提升一个宇宙 *)

(*
 [SetoidObject] is a non-cumulative record, so a SetoidObject@{o o} is not
 itself a SetoidObject@{so so} even when o ≤ so; but its carrier and
 equivalence re-typecheck at the higher level, so the lift is a rebuild.
 The carrier and the relation are definitionally unchanged. 

 --------
 [SetoidObject] 是一个非累积记录，因此即使 o ≤ so，SetoidObject@{o o} 本身也不是 SetoidObject@{so so}；但是它的承载体和等价关系在更高层次会重新类型检查，因此提升是一个重建。承载体和关系在定义上保持不变。
*)
(*
 The lift is assembled from named, universe-annotated pieces.  Writing it
 as one nested record expression makes the elaborator unify the low- and
 high-level class heads first-order, which collapses the levels to o = so;
 ascribing each piece its high-level type separately (with the class heads
 η-expanded away, so conversion goes through δ on the definitional classes
 [Reflexive]/[Symmetric]/[Transitive]) keeps the honest o ≤ so. 

 --------
 该电梯是由带有名称和宇宙注释的零件组装而成的。将其写成一个嵌套的记录表达式会让推导器首先将低级和高级类头统一为一阶，这会将级别折叠为 o = so；分别为每个零件指定其高级类型（类头经过 η 展开，因此转换通过定义类 [Reflexive] / [Symmetric] / [Transitive] 的 δ 进行）可以保持真实的 o ≤ so。
*)

Definition equiv_lift@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  crelation@{so so} A := λ a b, @equiv A S a b.

Definition reflexive_lift@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  Reflexive@{so so} (equiv_lift@{o so} S) :=
  λ a, @Equivalence_Reflexive _ _ (@setoid_equiv _ S) a.

Definition symmetric_lift@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  Symmetric@{so so} (equiv_lift@{o so} S) :=
  λ a b Hab, @Equivalence_Symmetric _ _ (@setoid_equiv _ S) a b Hab.

Definition transitive_lift@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  Transitive@{so so} (equiv_lift@{o so} S) :=
  λ a b c Hab Hbc, @Equivalence_Transitive _ _ (@setoid_equiv _ S) a b c Hab Hbc.

Definition Setoid_Lift_instance@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  Setoid@{so so} A :=
  {| equiv        := equiv_lift@{o so} S
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := reflexive_lift@{o so} S
        ; Equivalence_Symmetric  := symmetric_lift@{o so} S
        ; Equivalence_Transitive := transitive_lift@{o so} S |} |}.

Definition Setoid_Lift@{o so} (X : SetoidObject@{o o}) : SetoidObject@{so so} :=
  {| carrier   := carrier X
   ; is_setoid := Setoid_Lift_instance@{o so} (is_setoid X) |}.

(*
 A setoid morphism between level-o setoids re-typechecks between their
 lifts: carrier function and respectfulness are reused verbatim. 

 --------
 在层级为 0 的集合基元之间的集合基元态射，在它们的提升之间重新类型检查：载体函数和尊重性被逐字重用。
*)
Definition SetoidMorphism_Lift@{o so} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y) :
  SetoidMorphism@{so so so} (Setoid_Lift@{o so} X) (Setoid_Lift@{o so} Y) :=
  @Build_SetoidMorphism@{so so so}
    (carrier X) (Setoid_Lift_instance@{o so} (is_setoid X))
    (carrier Y) (Setoid_Lift_instance@{o so} (is_setoid Y))
    (λ a, f a)
    (λ a b Hab, @proper_morphism _ _ _ _ f a b Hab).

(* ------------------------------------------------------------------------ *)
(* * ** The truth-value object, one universe up / * ** 真值对象，高一个宇宙 *)

(*
 The setoid of truth values: carrier Type@{o} — the type of the library's
 Type-valued propositions at level o — under bi-implication [iffT] (which
 is what `↔` denotes in this library, cf. Lib/Foundation.v).  Its carrier
 forces o < so, which is exactly the classifier's size obstruction: this
 is a SetoidObject@{so so}, i.e. an object of Sets one universe up, and
 provably not an obj[Sets@{o so}].  Prop (with `iff`) would fit at level o
 size-wise, but could not receive the Type@{o}-valued characteristic
 predicate λ b, ∃ a, m a ≈ b without truncating away the witness that
 [sets_char_pullback] and [sets_char_unique] must recover; Type@{o} with
 iffT is the strongest formulation the universe checker accepts WITHOUT
 a hypothesis.  With one, the truncated [Powerset_Omega] of
 Instance/Sets/Powerset/Universal.v — carrier [Prop], hence an object of
 [Sets] at level o — serves at ONE level instead, once the truncation
 can be inverted; that is exactly what
 Instance/Sets/Classifier/OneLevel.v's [Untruncate] buys, and its
 [Sets_Classifier] is the resulting instance. 

 --------
 真值的集合等价体：承载类型 Type@{o} — 这是库中级别为 o 的类型值命题的类型 — 在双重蕴涵下 [iffT]（这也是在此库中 `↔` 所表示的，参见 Lib/Foundation.v）。它的承载类型要求 o < so，这正是分类器的大小限制：这是一个 SetoidObject@{so so}，即提升一个宇宙后的集合对象，并且可证明它不是 obj [Sets@{o so}] 。Prop（使用 `iff`）在大小上适合层 o，但无法接收类型为 Type@{o} 的特征谓词 λ b, ∃ a, m a ≈ b，而不截断 [sets_char_pullback] 和 [sets_char_unique] 必须恢复的见证；带 iffT 的 Type@{o} 是宇宙检查器在没有假设的情况下接受的最强表述。使用一个，截断的 [Powerset_Omega] 来自 Instance/Sets/Powerset/Universal.v——载体 [Prop]，因此在层次 o 下是 [Sets] 的一个对象——相反地可以在 ONE 层次上使用，一旦截断可以被逆转；这正是 Instance/Sets/Classifier/OneLevel.v 的 [Untruncate] 实现的功能，其 [Sets_Classifier] 是由此得到的实例。
*)

Definition PropSetoid_equiv@{o so} : crelation@{so so} Type@{o} :=
  λ P Q : Type@{o}, P ↔ Q.

Lemma PropSetoid_equivalence@{o so} :
  Equivalence@{so so} PropSetoid_equiv@{o so}.
Proof. unfold PropSetoid_equiv; equivalence. Qed.

Definition PropSetoid@{o so} : SetoidObject@{so so} :=
  {| carrier   := Type@{o}
   ; is_setoid := {| equiv        := PropSetoid_equiv@{o so}
                   ; setoid_equiv := PropSetoid_equivalence@{o so} |} |}.

(* The point true : 1 ~> Ω, selecting the (canonically) inhabited truth value [poly_unit]. Any inhabited type would do, up to iffT. / 真正的点：1 ~> Ω，选择（典型地）有元素的真值 [poly_unit]。任何有元素的类型都可以，至 iffT 为止。 *)
Definition sets_true@{o so} :
  SetoidMorphism@{so so so} unit_setoid_object@{so so} PropSetoid@{o so}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       poly_unit@{so} unit_setoid@{so so}
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ _, poly_unit@{o}) _).
  intros ? ? ?; split; intros ?; exact ttt.
Defined.

(* The terminal map: every setoid maps to the singleton. / 终端图：每个等价集合映射到单元素集合。 *)
Definition sets_to_unit@{so} {X : SetoidObject@{so so}} :
  SetoidMorphism@{so so so} X unit_setoid_object@{so so} :=
  @Build_SetoidMorphism@{so so so}
    (carrier X) (is_setoid X)
    poly_unit@{so} unit_setoid@{so so}
    (λ _, ttt) (λ _ _ _, eq_refl).

(* ------------------------------------------------------------------------ *)
(** ** The characteristic map / ** 特征图 *)

(*
 The characteristic map of m : A ~> B sends b to the truth value
 "b is in the image of m", i.e. the Type@{o}-valued ∃ a, m a ≈ b.  It is
 a morphism of Sets ONE UNIVERSE UP: its domain is the lift of B and its
 codomain is [PropSetoid].  Note that no monicity is needed for the map
 itself to be well-defined — [Monic] enters only in the classification
 theorems below. 

 --------
 映射 m : A ~> B 的特征映射将 b 映射为真值“b 在 m 的像中”，即 Type@{o}-值的 ∃ a, m a ≈ b。它是 Sets 单一宇宙上的一个态射：其定义域是 B 的提升，余域是 [PropSetoid]。请注意，该映射本身的定义不需要单射性——[Monic] 仅出现在下面的分类定理中。
*)
Definition char_setoid@{o so} {A B : SetoidObject@{o o}}
  (m : A ~{Sets@{o so}}~> B) :
  SetoidMorphism@{so so so} (Setoid_Lift@{o so} B) PropSetoid@{o so}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier B) (Setoid_Lift_instance@{o so} (is_setoid B))
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ b, ∃ a : carrier A, @equiv _ (is_setoid B) (m a) b) _).
  intros b b' Hbb'; split; intros [a Ha]; exists a.
  - transitivity b.
    + exact Ha.
    + exact Hbb'.
  - transitivity b'.
    + exact Ha.
    + now symmetry.
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** The classifying pullback square / * ** 分类拉回图 *)

(*
 The full subobject-classifier pullback property, at cross-universe
 strength: in Sets@{so sso} — one level above the mono's home Sets@{o so} —
 the square

 Setoid_Lift A ── sets_to_unit ──> 1
 |                           |
 SetoidMorphism_Lift m           sets_true
 v                           v
 Setoid_Lift B ── char_setoid m ─> PropSetoid

 is a pullback in the apex-pinned sense of Theory/Morphisms/Stability.v.
 The one-level [IsPullback] form is not statable: its ambient category
 would have to contain [PropSetoid], and no obj[Sets@{o so}] can (see the
 header).  Everything else — apex, legs, and the cones quantified over —
 lives honestly at the higher level, so beyond the forced lifting nothing
 is weakened.  Monicity of m enters exactly twice: to make the mediator
 well-defined on setoids, and to make it unique. 

 --------
 全集对象分类器的拉回性质，在跨宇宙强度下：在 Sets@{so sso} —— 比单射所在的 Sets@{o so} 高一级 —— 该方形图

 Setoid_Lift A ── sets_to_unit ──> 1
 |                           |
 SetoidMorphism_Lift m           sets_true
 v                           v
 Setoid_Lift B ── char_setoid m ─> PropSetoid在理论/态射/稳定性.v 中的顶点固定意义上是一个拉回。一个层级的 [IsPullback] 形式是无法表述的：它的环境范畴必须包含 [PropSetoid]，而没有对象 [Sets@{o so}] 可以（见标题）。其他一切——顶点、腿，以及量化的锥——都真实地存在于更高层级，所以除了强制提升之外，没有任何事物被弱化。m 的单射性正好出现两次：一次是为了使中介在集合等价类上定义良好，另一次是为了使其唯一。
*)
Theorem sets_char_pullback@{o so sso} {A B : SetoidObject@{o o}}
  (m : A ~{Sets@{o so}}~> B) (Hm : @Monic Sets@{o so} A B m) :
  @IsPullback Sets@{so sso}
    (Setoid_Lift@{o so} B) unit_setoid_object@{so so} PropSetoid@{o so}
    (char_setoid@{o so} m) sets_true@{o so}
    (Setoid_Lift@{o so} A)
    (SetoidMorphism_Lift@{o so} m) sets_to_unit@{so}.
Proof.
  pose proof (snd (injectivity_is_monic m) Hm) as inj.
  constructor.
  - (* the square commutes: for a : A, "m a is in the image of m" iff ⊤ / 这个方形是交换的：对于 a : A，“m a 在 m 的像中”当且仅当 ⊤ *)
    intro a; split.
    + intros _; exact ttt.
    + intros _; exists a; reflexivity.
  - (* the universal property / 通用属性 *)
    intros Q q1 q2 Hq.
    simpl in Hq.
    (* Each x : Q comes with the truth of "q1 x is in the image of m"; extracting its witness defines the mediator. Monicity makes the extraction respect ≈. / 每个 x : Q 都伴随着 “q1 x 属于 m 的像” 的真实性；提取其见证物定义了中介。单射性使得提取尊重 ≈。 *)
    given (u : SetoidMorphism@{so so so} Q (Setoid_Lift@{o so} A)). {
      unshelve refine
        (@Build_SetoidMorphism@{so so so}
           (carrier Q) (is_setoid Q)
           (carrier A) (Setoid_Lift_instance@{o so} (is_setoid A))
           (λ x, `1 (snd (Hq x) ttt)) _).
      intros x y Hxy.
      apply inj.
      transitivity (q1 x).
      { exact (`2 (snd (Hq x) ttt)). }
      transitivity (q1 y).
      { now apply (proper_morphism q1). }
      symmetry.
      exact (`2 (snd (Hq y) ttt)).
    }
    unshelve refine {| unique_obj := u |}.
    + split.
      * intro x; simpl.
        exact (`2 (snd (Hq x) ttt)).
      * intro x; simpl.
        now destruct (q2 x).
    + intros v [Hv1 Hv2] x.
      apply inj.
      transitivity (q1 x).
      { exact (`2 (snd (Hq x) ttt)). }
      symmetry.
      exact (Hv1 x).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Uniqueness of the characteristic map / * ** 特征映射的独特性 *)

(*
 Any χ making the (lifted) square a pullback agrees with [char_setoid m]
 componentwise up to iff — which is exactly morphism equivalence in the
 hom-setoid of Sets@{so sso}.  Forward direction: probe the universal
 property with the subobject {b' : B & χ b'} of truth-values-of-χ; its
 mediator into the apex recovers, for each b with χ b, a preimage under m.
 Backward direction: transport the commuting square's χ (m a) ↔ ⊤ along
 m a ≈ b using the properness of χ.  Monicity of m is not needed here. 

 --------
 任何 χ 使得（提升的）平方是一个拉回时，逐分量地与 [char_setoid m] 一致，条件是 iff——这正好是 Sets@{so sso} 的同态集中态射等价。正向：使用真值χ的子对象 {b' : B & χ b'} 探测泛性质；它进入顶点的中介对于每个 χ b 为真的 b 恢复了 m 的一个原像。反向：沿 m a ≈ b 传递交换平方的 χ (m a) ↔ ⊤，使用 χ 的性质。这里不需要 m 的单射性。
*)
Theorem sets_char_unique@{o so sso} {A B : SetoidObject@{o o}}
  (m : A ~{Sets@{o so}}~> B)
  (chi : Setoid_Lift@{o so} B ~{Sets@{so sso}}~> PropSetoid@{o so})
  (H : @IsPullback Sets@{so sso}
         (Setoid_Lift@{o so} B) unit_setoid_object@{so so} PropSetoid@{o so}
         chi sets_true@{o so}
         (Setoid_Lift@{o so} A)
         (SetoidMorphism_Lift@{o so} m) sets_to_unit@{so}) :
  chi ≈[Sets@{so sso}] char_setoid@{o so} m.
Proof.
  intro b.
  split.
  - (* χ b holds → b is in the image of m / χ b 成立 → b 在 m 的像中 *)
    intro t.
    given (Q : SetoidObject@{so so}). {
      unshelve refine
        {| carrier   := ∃ b' : carrier B, chi b'
         ; is_setoid :=
             {| equiv := λ p q, @equiv _ (is_setoid B) (`1 p) (`1 q) |} |}.
      constructor; repeat intro.
      - reflexivity.
      - now symmetry.
      - etransitivity; eauto.
    }
    given (q1 : Q ~{Sets@{so sso}}~> Setoid_Lift@{o so} B). {
      unshelve refine
        (@Build_SetoidMorphism@{so so so}
           (carrier Q) (is_setoid Q)
           (carrier B) (Setoid_Lift_instance@{o so} (is_setoid B))
           (λ p, `1 p) (λ p q Hpq, Hpq)).
    }
    assert (Hcone : chi ∘[Sets@{so sso}] q1
                      ≈ sets_true@{o so} ∘[Sets@{so sso}] sets_to_unit@{so}). {
      intro p; split.
      - intros _; exact ttt.
      - intros _; exact (`2 p).
    }
    pose proof (is_pullback_ump H Q q1 sets_to_unit@{so} Hcone) as U.
    exists (unique_obj U (b; t)).
    exact (fst (unique_property U) (b; t)).
  - (* b is in the image of m → χ b holds / b 在 m → χ 的像中成立 *)
    intros [a Ha].
    exact (fst (@proper_morphism _ _ _ _ chi (m a) b Ha)
               (snd (is_pullback_commutes H a) ttt)).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The one-level shadow: the classified subobject / * ** 一层阴影：分类子对象 *)

(*
 While the truth-value OBJECT is forced one universe up, the pullback APEX
 is not: the sub-setoid {b : B & ∃ a, m a ≈ b} — carrier-wise the preimage
 of true under [char_setoid m] — involves only level-o data, and
 Instance/Sets/Image.v already provides it as [Sets_Image m] together with
 its monic first projection.  So at the SAME level Sets@{o so}, the
 subobject (A, m) of B equals the image subobject in the subobject setoid
 of Theory/Subobject.v.  The domain isomorphism is a ↦ (m a; (a; _)) with
 inverse (b; (a; _)) ↦ a; monicity of m makes the inverse respect ≈.
 Ends in Defined: the equivalence transports an isomorphism. 

 --------
 当真值对象被强制提升一个宇宙时，拉回顶点（APEX）并不会被提升：子集合体 {b : B & ∃ a, m a ≈ b}——作为载体，它是 [char_setoid m] 下的真值的原像——仅涉及零级数据，并且 Instance/Sets/Image.v 已经将其作为 [Sets_Image m] 提供，同时提供其单态的第一个投影。因此，在相同等级 Sets@{o so} 中，B 的子对象 (A, m) 等于 Theory/Subobject.v 的子对象集合体中的像子对象。域同构为 a ↦ (m a; (a; _))，其逆为 (b; (a; _)) ↦ a；m 的单态性保证了逆映射尊重 ≈。定义结束：此等价关系传递了一个同构。
*)
Theorem sets_char_subobject@{o so} {A B : SetoidObject@{o o}}
  (m : A ~{Sets@{o so}}~> B) (Hm : @Monic Sets@{o so} A B m) :
  @equiv _ (@SubObj_Setoid Sets@{o so} B)
    (@Build_SubObj Sets@{o so} B A m Hm)
    (@Build_SubObj Sets@{o so} B (Sets_Image m) (Sets_Image_mono m)
       (Sets_Image_mono_monic m)).
Proof.
  pose proof (snd (injectivity_is_monic m) Hm) as inj.
  (* the inverse of the epi leg, available because m is monic / epi边的逆，因为m是单一的，所以可用 *)
  given (h : Sets_Image m ~{Sets@{o so}}~> A). {
    unshelve refine {| morphism := λ p, `1 `2 p |}.
    intros p q Hpq.
    apply inj.
    transitivity (`1 p).
    { exact (`2 `2 p). }
    transitivity (`1 q).
    { exact Hpq. }
    symmetry.
    exact (`2 `2 q).
  }
  given (iso : A ≅[Sets@{o so}] Sets_Image m). {
    unshelve refine {| to := Sets_Image_epi m; from := h |}.
    - (* epi ∘ h ≈ id, compared on first components / epi ∘ h ≈ id，在第一个分量上比较 *)
      intro p.
      exact (`2 `2 p).
    - (* h ∘ epi ≈ id, on the nose / h ∘ epi ≈ id，字面意思 *)
      intro a.
      reflexivity.
  }
  exists iso.
  exact (Sets_Image_comm m).
Defined.

(* * ** The lift is inert for epicness / * ** 电梯因其史诗般而静止 *)

(*
 A note on scope, because this file is where one would expect the
 epis-are-surjections theorem to live.  It is NOT here: it is proved at one
 universe in Instance/Sets.v as [surjectivity_is_epic], using the cokernel
 pair of h with itself rather than a truth-value object.

 That is worth saying plainly, because the opposite was believed for a long
 time -- long enough that Instance/Sets.v carried an abandoned proof and a
 header note blaming size.  The classifier obstruction this file opens with
 is real: a characteristic map must receive a [Type@{o}]-valued truth value,
 and no object of Sets@{o so} carries one.  But epis-are-surjections does
 NOT inherit it.  The classical truth-value probe is only one probe; the
 cokernel pair `carrier B + carrier B`, glued along the image of h, tests
 the same thing and never leaves the universe of the carriers.

 What this file can still contribute is that lifting is inert for epicness:
 being epic against level-o probes and being epic against level-so probes
 are the same condition.  One direction uses this file's own machinery --
 [char_setoid] against the constantly-true map -- and the other goes through
 the one-universe theorem, whose cokernel-pair probe is itself level-o. 

 --------
 关于范围的说明，因为这个文件是人们通常期望包含 epimorphisms 是满射定理的地方。但它不在这里：它在 Instance/Sets.v 的一个宇宙中被证明为 [surjectivity_is_epic]，使用 h 与其自身的余核对，而不是使用真值对象。这一点值得直说，因为相反的观点曾被相信了很长时间——足够长以至于 Instance/Sets.v 中保留了一个被放弃的证明和一个归咎于大小的标题注释。这个文件一开始提到的分类器障碍是真实存在的：特征映射必须接收一个 [Type@{o}] 值的真值，而 Sets@{o so} 中没有对象携带这样的值。但 epis-are-surjections 并没有继承它。经典真值探针只是其中之一；沿着 h 的像粘接的余核对 `carrier B + carrier B` 测试同样的东西，并且从不离开承载对象的宇宙。这个文件仍然可以贡献的是，提升对史诗感来说是惰性的：
 对 level-o 探针表现出史诗感和对 level-so 探针表现出史诗感
 是相同的条件。一个方向使用这个文件自身的机制——
 [char_setoid] 对着恒为真的映射——而另一个方向通过
 单一宇宙定理，其余核对偶探针本身是 level-o。
*)

(* The constantly-true probe: the terminal map followed by [sets_true]. / 持续为真的探针：终端地图后跟 [sets_true] 。 *)
Definition sets_all_true@{o so sso} (X : SetoidObject@{so so}) :
  X ~{Sets@{so sso}}~> PropSetoid@{o so} :=
  sets_true@{o so} ∘[Sets@{so sso}] sets_to_unit@{so}.

Theorem lifted_epic_implies_epic@{o so sso} {A B : SetoidObject@{o o}}
  (h : A ~{Sets@{o so}}~> B)
  (H : @Epic@{sso so} Sets@{so sso}
         (Setoid_Lift@{o so} A) (Setoid_Lift@{o so} B)
         (SetoidMorphism_Lift@{o so} h)) :
  @Epic@{so o} Sets@{o so} A B h.
Proof.
  apply (surjective_implies_epic@{so o} h).
  intro b.
  assert (Hcomm :
    char_setoid@{o so} h ∘[Sets@{so sso}] SetoidMorphism_Lift@{o so} h
      ≈ sets_all_true@{o so sso} (Setoid_Lift@{o so} B)
          ∘[Sets@{so sso}] SetoidMorphism_Lift@{o so} h). {
    intro a; split.
    - intros _; exact ttt.
    - intros _; exists a; reflexivity.
  }
  exact (snd (@epic _ _ _ _ H PropSetoid@{o so}
                (char_setoid@{o so} h)
                (sets_all_true@{o so sso} (Setoid_Lift@{o so} B))
                Hcomm b) ttt).
Qed.

Theorem epic_implies_lifted_epic@{o so sso} {A B : SetoidObject@{o o}}
  (h : A ~{Sets@{o so}}~> B) (H : @Epic@{so o} Sets@{o so} A B h) :
  @Epic@{sso so} Sets@{so sso}
    (Setoid_Lift@{o so} A) (Setoid_Lift@{o so} B)
    (SetoidMorphism_Lift@{o so} h).
Proof.
  constructor; intros z g1 g2 Hg b.
  destruct (epic_implies_surjective@{so o} h H b) as [a Ha].
  rewrite <- Ha.
  exact (Hg a).
Qed.
