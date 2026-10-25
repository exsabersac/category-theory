Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Polynomial.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * Pointed rings, and the polynomial functor as a left adjoint

   Book: Awodey, "Category Theory", §9.3, Example 9.10, printed
   pp. 226-227 (PDF pp. 235-236) — awodey:9.3:example10
   nLab:      https://ncatlab.org/nlab/show/free+functor
   nLab:      https://ncatlab.org/nlab/show/pointed+object
   Wikipedia: https://en.wikipedia.org/wiki/Polynomial_ring

   THE STATEMENT.  A pointed ring is a ring together with a
   distinguished element; a homomorphism of pointed rings is a ring
   homomorphism carrying the point to the point.  Awodey's example says
   that the forgetful functor which drops the point has a left adjoint,
   sending a ring R to R[x] pointed at the indeterminate, and that the
   transposition is EVALUATION at the point: a homomorphism R ⟶ S and a
   choice of s in S amount to the same thing as a homomorphism of
   pointed rings (R[x], x) ⟶ (S, s), namely the one substituting s for
   x.  This is the adjunction whose unit is the coefficient inclusion
   and whose counit is evaluation, and it is the reason "adjoin an
   indeterminate" is a free construction.

   A SCOPE CORRECTION, DISCLOSED, AND PROVED NECESSARY.  The adjunction
   is stated here over COMMUTATIVE rings — Instance/Rng.v's [CRng] — and
   not over all of [Rng].  It is not a matter of taste.  Over an
   arbitrary ring the backward transpose does not exist: a homomorphism
   R[x] ⟶ S over R must send x to an element commuting with the whole
   image of R, since x is central in R[x] by construction, whereas an
   arbitrary point of an arbitrary ring commutes with nothing in
   particular.  That obstruction is a theorem and not an aside:
   Instance/Rng/Polynomial.v's [poly_hom_value_central] proves that
   EVERY ring homomorphism out of K[x] has its value at x commuting with
   the image of the coefficients, so the hypothesis discharged here by
   commutativity of the target is necessary and not an artifact of the
   proof.

   WHAT THE NON-COMMUTATIVE CASE WOULD NEED, named so that its absence
   is not read as an oversight.  The forgetful functor from pointed
   unital rings to unital rings does have a left adjoint; what it is
   NOT is R ↦ R[x].  The free object there is the free algebra on one
   NON-COMMUTING generator, R⟨x⟩ — the ring of words in x with
   coefficients from R, in which x is not required to commute with the
   coefficients — and that is a different construction from the one
   below, not a relaxation of it: its underlying object is a free
   R-bimodule on the words in x rather than a quotient of formal
   expressions by commutative-ring laws, and [pe_mul_comm] would have to
   be deleted from Instance/Rng/Polynomial.v's relation and the
   coefficient interchange rewritten around its absence.  It is a
   separate issue and no part of it is attempted here.

   (What IS available over all of [Rng] is the ONE-generator case with
   ℤ as the base, where the two constructions coincide: a single
   generator commutes with itself, and the integers are central in
   every unital ring, so ℤ⟨x⟩ IS ℤ[x] and it is free on one generator
   in the category of all unital rings.  That statement lives in
   Instance/Rng/Polynomial.v as [zpoly_universal_element], with
   [zring_central] supplying the centrality, and it is Riehl's Example
   2.1.5(v).)

   THE CATEGORY OF POINTED RINGS IS NOT NEW MACHINERY.  A pointed object
   of a category C with respect to an underlying-set functor
   U : C ⟶ Sets is precisely an object of Construction/Elements.v's
   category of elements of U: its objects are the pairs (A, a) with a an
   element of U A, and its morphisms are the C-morphisms f with
   U f a ≈ b — which is the point-preservation condition, verbatim.  So
   [CRngPt] is [Elements CRng_Forget], the forgetful functor is
   [Elements_proj], and both come with their laws already proved.  The
   hom-setoid of [Elements] compares only the underlying morphism, which
   is the right convention here: two homomorphisms of pointed rings are
   equal when they are equal as homomorphisms.

   WHAT IS DELIVERED.

   - [CRng_Forget], [CRngPt], [CRngPt_Forget];
   - [poly_pointed_universal_arrow], a universal arrow from every
   commutative ring to the forgetful functor, in the comma-packaged
   encoding of Theory/Universal/Arrow.v;
   - [PolyPointed], the left adjoint it induces, and
   [poly_pointed_adjunction : PolyPointed ⊣ CRngPt_Forget];
   - evaluation as the transpose: [poly_pointed_transpose_is_evaluation]
   identifies any morphism realizing the transposition with the
   evaluation homomorphism, and [poly_pointed_adj_transpose_evaluates]
   instantiates that at the adjunction's own backward transpose;
   - strength measurements, and a ℤ witness that computes.

   STRENGTHS, MEASURED.

   - [eq_refl]: the left adjoint's object part is the pointed
   polynomial ring ([PolyPointed_obj]); the universal arrow IS the
   coefficient inclusion ([poly_pointed_arrow_is_const]); the unit
   ACTS as that inclusion on every coefficient
   ([poly_pointed_unit_is_const]); and the point of the free object
   is the indeterminate ([poly_pointed_point_is_x]).
   - NOT [eq_refl], measured: the unit as a MORPHISM.
   [poly_pointed_unit A = poly_pointed_arrow A] is rejected — the
   unit's underlying homomorphism is a composite record, not the
   inclusion's record — so the [eq_refl] claim above is about the
   action and is stated that way.  Test/ProbePolynomial.v pins it.
   - `≈` only: the backward transpose.  It is
   [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows]
   is [Qed]-opaque, so it does not compute; what is proved is that
   it evaluates ([poly_pointed_adj_transpose_evaluates]).  This is
   the same seam Instance/Mod/Free.v records for the counit of the
   free-module adjunction.
   - `≈` only, and not for want of trying: the action of [PolyPointed]
   on a morphism, which [LeftAdjointFunctorFromUniversalArrows]
   defines by universal factorization rather than by a formula.
   That it relabels coefficients is [poly_pointed_fmap_const], a
   theorem.

   WHAT IS NOT DELIVERED.  No pointed-ring analogue for [Rng] — that
   needs R⟨x⟩, the free algebra on a non-commuting generator, which is a
   different construction and is described but not built (see above); no
   monad or Eilenberg-Moore reading of the induced
   comonad/monad; no statement that [PolyPointed] is faithful or that
   the adjunction is monadic; and no several-indeterminate version —
   R[x, y] would be the free pointed ring on R[x], which follows by
   composing the adjunction with itself, but the resulting object is not
   identified with a two-variable polynomial ring here. 

   --------
   * * 带单位的环，以及多项式函子作为左伴随

   书籍：Awodey，《范畴论》，§9.3，例 9.10，印刷版第226-227页（PDF第235-236页）— awodey:9.3:example10
   nLab：https://ncatlab.org/nlab/show/free+functor
   nLab：https://ncatlab.org/nlab/show/pointed+object
   维基百科：https://en.wikipedia.org/wiki/Polynomial_ring该陈述。带点环是带有一个指定元素的环；带点环的同态是将点映射到点的环同态。Awodey 的例子说明，放弃点的忘记函子有一个左伴随函子，它将环 R 发送到以不定元为点的 R [x]，并且换位是对该点的求值：环同态 R ⟶ S 与 S 中一个元素 s 的选择，相当于带点环同态 (R [x], x) ⟶ (S, s)，也就是用 s 代替 x 的同态。这就是其单位是系数包含、余单位是求值的伴随关系，也解释了“添加一个不定元”为什么是一种自由构造。一个范围修正，被披露，并且被证明是必要的。这里的伴随被陈述在交换环上——Instance/Rng.v 的 [CRng]——而不是在所有 [Rng] 上。这不是品味问题。在任意环上，反向转置并不存在：一个 R 上的同态 R [x] ⟶ S 必须将 x 映射到与 R 的整个像交换的元素，因为 x 在 R [x] 中是中心元素，而任意环的任意点并不与任何特定元素交换。这个阻碍是一个定理，而不是附带说明：
   Instance/Rng/Polynomial.v 的 [poly_hom_value_central] 证明了
   来自 K [x] 的每个环同态在 x 的值与系数的像是交换的，所以这里通过目标的交换性解除的假设是必要的，而不是证明的产物。非交换情况所需要的，被如此命名，以便其缺失不会被认为是疏忽。从有基环到环的遗忘函子确实有一个左伴随；但它不是 R ↦ R [x]。那里的自由对象是一元非交换生成元上的自由代数，R⟨x⟩——由 x 组成的词构成的环，系数来自 R，其中 x 不要求与系数交换——这与下面的构造不同，而不是它的放宽：其底层对象是 x 的词组成的自由 R 双模，而不是通过交换环的定律对形式表达式取商，而 [pe_mul_comm] 将必须从 Instance/Rng/Polynomial.v 的关系中删除，并且系数交换需要围绕其缺失重新编写。这是一个独立的问题，这里没有涉及其中的任何部分。

   （在整个 [Rng] 上可用的是带有 ℤ 作为底的单生成元情况，其中两种构造是一致的：一个生成元与自身交换，并且整数在每个幺环中都是中心元素，所以 ℤ⟨x⟩ 确实是 ℤ [x]，并且它在所有幺环的范畴中是一个单生成元的自由对象。该陈述记录在 Instance/Rng/Polynomial.v 中作为 [zpoly_universal_element]，其中 [zring_central] 提供了中心性，并且它是 Riehl 的例子 2.1.5(v)。）尖环的范畴并不是新机制。在关于基础集合函子 U : C ⟶ Sets 的范畴 C 中的一个指向对象，恰好是 Construction/Elements.v 中 U 的元素范畴的一个对象：它的对象是 (A, a) 对，其中 a 是 U A 的一个元素，它的态射是满足 U f a ≈ b 的 C-态射 f——这就是逐字的点保持条件。因此 [CRngPt] 是 [Elements CRng_Forget]，遗忘函子是 [Elements_proj]，并且它们的定律已经被证明。[Elements] 的同态集合只比较基础态射，这是这里的正确约定：当两个尖环的同态作为同态相等时，它们就相等。  

   交付的内容是什么。- [CRng_Forget]、[CRngPt]、[CRngPt_Forget]；
   - [poly_pointed_universal_arrow]，从每个交换环到遗忘函子的一般箭头，在 Theory/Universal/Arrow.v 的逗号打包编码中；
   - [PolyPointed]，它所诱导的左伴随，以及 [poly_pointed_adjunction : PolyPointed ⊣ CRngPt_Forget]；
   - 作为转置的求值：[poly_pointed_transpose_is_evaluation] 将实现转置的任何态射与求值同态对应起来，[poly_pointed_adj_transpose_evaluates] 在伴随自身的逆转置上实例化它；
   - 强度测量，以及计算的ℤ证据。

   强度，已测量。-  [eq_refl]：左伴随的对象部分是带底点的多项式环（[PolyPointed_obj]）；普适箭头是系数包含（[poly_pointed_arrow_is_const]）；单位在每个系数上表现为该包含（[poly_pointed_unit_is_const]）；自由对象的底点是未定元（[poly_pointed_point_is_x]）。- 不是[eq_refl]，测量为：单位作为一个态射。[poly_pointed_unit A = poly_pointed_arrow A] 被拒绝——单位的底层同态是复合记录，而不是包含的记录——所以上述[eq_refl] 的说法关于作用，并以这种方式陈述。Test/ProbePolynomial.v 固定了它。- 仅`≈`：后向转置。它是[unique_obj (ump_universal_arrows …)]，而[ump_universal_arrows] 是[Qed]-不透明，所以它不计算；证明的是它的求值（[poly_pointed_adj_transpose_evaluates]）。这是自由模伴随的余单位的相同缝合实例/模/Free.v 记录。- 仅限 `≈`，并不是因为没有尝试：[PolyPointed] 对一个态射的作用，[LeftAdjointFunctorFromUniversalArrows] 通过普适分解而不是公式来定义。它重标记系数是 [poly_pointed_fmap_const]，一个定理。未交付的内容。没有 [Rng] 的有尖环类比——那需要 R⟨x⟩，即非交换生成元上的自由代数，这是一个不同的构造，虽有描述但未构建（见上文）；没有诱导的余单子/单子的幺函子或 Eilenberg-Moore 解读；没有声明 [PolyPointed] 是忠实的，或者该伴随是单子的；也没有多不定元版本——R [x, y] 将是 R [x] 上的自由有尖环，通过将伴随自身组合可以得到，但此处未将生成的对象与二元多项式环对应识别。
*)

(* * ** The underlying-set functor of commutative rings / * ** 交换环的底层集合函子 *)

Program Definition CRng_Forget : CRng ⟶ Sets := {|
  fobj := fun A => rig_setoid (`1 A);
  fmap := fun A B f => rig_map (`1 f)
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

(** ** Pointed commutative rings / ** 尖端交换环 *)

(*
   * Objects are pairs (A, a); morphisms are the ring homomorphisms
   carrying the point.  This is Construction/Elements.v's category of
   elements, not a fresh construction. 

   --------
   * 对象是对 (A, a)；态射是携带该点的环同态。这是 Construction/Elements.v 的元素范畴，而不是一个新的构造。
*)
Definition CRngPt : Category := Elements CRng_Forget.

Definition CRngPt_Forget : CRngPt ⟶ CRng := Elements_proj CRng_Forget.

(** The hom-type is the point-preservation condition, definitionally. / 同态类型是点保留条件，从定义上来说。 *)
Example CRngPt_hom_unfold (P Q : CRngPt) :
  (P ~{CRngPt}~> Q)
    = ∃ f : `1 P ~{CRng}~> `1 Q, rig_map (`1 f) (`2 P) ≈ `2 Q
  := eq_refl.

(* * ** The polynomial ring, pointed at the indeterminate / * ** 指向不定元的多项式环 *)

Definition PolyCRng (A : CRng) : CRng := (PolyRing (`1 A); poly_comm (`1 A)).

Definition PolyPt (A : CRng) : CRngPt := (PolyCRng A; @poly_x (`1 A)).

(*
   * The coefficient inclusion, as a morphism of commutative rings.  The
   membership witness of [CRng_Sub] is trivial. 

   --------
   * 系数包含，作为交换环的一个态射。[CRng_Sub] 的成员见证是平凡的。
*)
Definition poly_pointed_arrow (A : CRng)
  : A ~{CRng}~> CRngPt_Forget (PolyPt A) :=
  (poly_const (`1 A); I).

(*
   * The two packagings of the same construction agree on the nose: Mac
   Lane's K-algebra [PolyAlg] (Instance/Rng/Polynomial.v) and Awodey's
   pointed ring [PolyPt] are built on one [PolyRing], with one
   coefficient inclusion.  What differs is the category the universal
   property is stated in, not the object. 

   --------
   * 两种相同结构的包装完全一致：Mac Lane 的 K-代数 [PolyAlg]（Instance/Rng/Polynomial.v）和 Awodey 的有基环 [PolyPt] 都建立在同一个 [PolyRing] 上，并且有一个系数包含。不同的是陈述普遍性质的范畴，而不是对象本身。
*)
Example poly_packagings_agree_ring (A : CRng) :
  kalg_ring (PolyAlg A) = `1 (`1 (PolyPt A)) := eq_refl.

Example poly_packagings_agree_unit (A : CRng) :
  kalg_unit (PolyAlg A) = `1 (poly_pointed_arrow A) := eq_refl.

(*
   * ** Awodey's universal property

   Given a pointed commutative ring (B, b) and a homomorphism h : A ⟶ B,
   substituting b for x is the one and only homomorphism of pointed
   rings (A[x], x) ⟶ (B, b) restricting to h on the coefficients.  The
   commutation hypothesis that [poly_extend] requires is discharged by
   commutativity of B. 

   --------
   * ** Awodey 的泛性质

   给定一个有基点的交换环 (B, b) 和一个同态 h : A ⟶ B，将 b 代入 x 是唯一的一个有基点环同态 (A⟶⟶, x) ⟶ (B, b)，在系数上限制为 h。[poly_extend] 所要求的交换假设由 B 的交换性消除。
*)
Lemma poly_pointed_universal (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q) :
  ∃! g : PolyPt A ~{CRngPt}~> Q,
    h ≈ fmap[CRngPt_Forget] g ∘ poly_pointed_arrow A.
Proof.
  unshelve econstructor.
  - unshelve refine ((_; I); _).
    + refine (poly_extend (`1 h) (`2 Q) (`2 A) _).
      intro c; exact (`2 (`1 Q) (`2 Q) (rig_map (`1 h) c)).
    + simpl; reflexivity.
  - intro c; simpl; reflexivity.
  - intros v Hv t; simpl.
    symmetry.
    apply (poly_extend_unique (`1 h) (`2 Q) (`1 (`1 v))).
    + intro c; symmetry; exact (Hv c).
    + exact (`2 v).
Defined.

Definition poly_pointed_universal_arrow (A : CRng)
  : UniversalArrow A CRngPt_Forget :=
  universal_arrow_from_UMP A CRngPt_Forget (PolyPt A)
    (poly_pointed_arrow A) (poly_pointed_universal A).

(*
   * ** The left adjoint and the adjunction

   Both come out of the generic machinery with no further proof — the
   route Construction/Free/Quiver.v and Instance/Mod/Free.v take. 

   --------
   * ** 左伴随与伴随

   两者都是由通用机制得出的，无需进一步证明——路径是 Construction/Free/Quiver.v 和 Instance/Mod/Free.v 所采用的。
*)

Definition PolyPointed : CRng ⟶ CRngPt :=
  LeftAdjointFunctorFromUniversalArrows CRngPt_Forget
    poly_pointed_universal_arrow.

Definition poly_pointed_adjunction : PolyPointed ⊣ CRngPt_Forget :=
  AdjunctionFromUniversalArrows CRngPt_Forget poly_pointed_universal_arrow.

(*
   * The left adjoint's object part is the pointed polynomial ring, and
   the universal arrow is the coefficient inclusion — both on the nose. 

   --------
   * 左伴随的对象部分是带基元的多项式环，普遍箭头是系数包含——完全对应。
*)
Example PolyPointed_obj (A : CRng) : PolyPointed A = PolyPt A := eq_refl.

Example poly_pointed_point_is_x (A : CRng) :
  `2 (PolyPointed A) = @poly_x (`1 A) := eq_refl.

Example poly_pointed_arrow_is_const (A : CRng) :
  @arrow _ _ A CRngPt_Forget (poly_pointed_universal_arrow A)
    = poly_pointed_arrow A := eq_refl.

(*
   * The unit is DERIVED in Theory/Adjunction.v (it is the transpose of
   the identity), not a field, so what it computes to has to be checked
   — and the answer is a measurement, not a slogan.  What holds by
   [eq_refl] is its ACTION: the unit sends each coefficient to the
   corresponding constant.  What does NOT hold by [eq_refl] is the
   equation of MORPHISMS [poly_pointed_unit A = poly_pointed_arrow A]:
   the unit is [fmap[U] id ∘ arrow], whose underlying ring homomorphism
   is the record [rig_hom_compose rig_hom_id (poly_const _)], and that
   record is not the term [poly_const _] however equal the two maps are
   on elements.  Test/ProbePolynomial.v pins both sides. 

   --------
   * 该单位在 Theory/Adjunction.v 中被导出（它是恒等映射的转置），而不是一个域，因此必须检查它的计算结果——答案是一个测量值，而不是口号。通过 [eq_refl] 所成立的是它的作用：单位将每个系数发送到相应的常数。通过 [eq_refl] 不成立的是 MORPHISMS [poly_pointed_unit A = poly_pointed_arrow A] 的方程：该单位是 [fmap[U] id ∘ arrow，其底层环同态是记录 [rig_hom_compose rig_hom_id (poly_const _)]，并且该记录不是项 [poly_const _]，无论两个映射在元素上如何相等。Test/ProbePolynomial.v 固定了双方。
*)
Definition poly_pointed_unit (A : CRng)
  : A ~{CRng}~> CRngPt_Forget (PolyPointed A) :=
  @Category.Theory.Adjunction.unit _ _ _ _ poly_pointed_adjunction A.

Example poly_pointed_unit_is_const (A : CRng)
  (c : carrier (rig_setoid (`1 A))) :
  rig_map (`1 (poly_pointed_unit A)) c = @pt_const (`1 A) c := eq_refl.

(*
   * ** Evaluation is the transpose

   Awodey's clause in the form the setoid presentation permits: any
   morphism of pointed rings realizing the transposition of h IS the
   evaluation homomorphism.  The backward transpose of the adjunction
   satisfies its hypothesis, so the corollary below applies it there. 

   --------
   * ** 评估是转置

   Awodey 的从集合化表示形式允许的条款：实现 h 转置的任何有指环的态射都是评估同态。伴随的逆向转置满足其假设，因此下面的推论将其应用于那里。
*)
Theorem poly_pointed_transpose_is_evaluation (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q)
  (g : PolyPt A ~{CRngPt}~> Q)
  (Hg : h ≈ fmap[CRngPt_Forget] g ∘ poly_pointed_arrow A)
  (t : @PTerm (`1 A)) :
  rig_map (`1 (`1 g)) t ≈ peval (`1 h) (`2 Q) t.
Proof.
  apply (poly_extend_unique (`1 h) (`2 Q) (`1 (`1 g))).
  - intro c; symmetry; exact (Hg c).
  - exact (`2 g).
Qed.

Corollary poly_pointed_adj_transpose_evaluates (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q) (t : @PTerm (`1 A)) :
  rig_map (`1 (`1 (from (@adj _ _ _ _ poly_pointed_adjunction A Q) h))) t
    ≈ peval (`1 h) (`2 Q) t.
Proof.
  apply poly_pointed_transpose_is_evaluation.
  symmetry.
  exact (iso_to_from (@adj _ _ _ _ poly_pointed_adjunction A Q) h).
Qed.

(*
   * ** The left adjoint relabels coefficients

   [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
   factorization, not by a formula, so what the functor does to a
   constant has to be proved. 

   --------
   * ** 左伴随重标记系数

   [LeftAdjointFunctorFromUniversalArrows] 通过普遍分解定义 [fmap]，而不是通过公式，因此必须证明函子对一个常数的作用。
*)
Lemma poly_pointed_fmap_const {A B : CRng} (u : A ~{CRng}~> B)
  (c : carrier (rig_setoid (`1 A))) :
  rig_map (`1 (`1 (fmap[PolyPointed] u))) (@pt_const (`1 A) c)
    ≈ @pt_const (`1 B) (rig_map (`1 u) c).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (poly_pointed_universal_arrow A)
              (@arrow _ _ B CRngPt_Forget
                 (poly_pointed_universal_arrow B) ∘ u)) c).
Qed.

(*
   * ** The witness over ℤ

   The free pointed commutative ring on ℤ is ℤ[x] pointed at x, and
   substituting 3 for x evaluates polynomials.  The evaluation
   homomorphism is Instance/Rng/Polynomial.v's, exhibited here as an
   arrow of [CRngPt]. 

   --------
   * ** 证据关于 ℤ

   在 ℤ 上的自由有点交换环是以 x 为基点的 ℤ [x]，
   将 3 代入 x 就可以对多项式进行求值。
   这个求值同态是 Instance/Rng/Polynomial.v 中的，在此作为 [CRngPt] 的箭头展示。
*)

Definition Int_pointed (b : Z) : CRngPt := (Int_CRng; b).

Definition zpoly_pointed_eval (b : Z)
  : PolyPt Int_CRng ~{CRngPt}~> Int_pointed b.
Proof.
  unshelve refine ((_; I); _).
  - exact (zpoly_eval Int_Ring b).
  - simpl; reflexivity.
Defined.

Example zpoly_pointed_eval_computes :
  rig_map (`1 (`1 (zpoly_pointed_eval 3%Z))) zpoly_sample = 16%Z := eq_refl.

Example zpoly_pointed_eval_at_x (b : Z) :
  rig_map (`1 (`1 (zpoly_pointed_eval b))) (@poly_x Int_Ring) = b := eq_refl.
