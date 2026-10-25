(*
 [Coq.QArith.QArith] is imported FIRST, before [Category.Lib]: it exports
 an [equiv] that shadows [Setoid]'s otherwise.  This is the import-order
 discipline Instance/FdVect.v records at its own head. 

 --------
 [Coq.QArith.QArith] 首先被导入，在 [Category.Lib] 之前：它导出一个 [equiv]，该 [equiv] 会覆盖 [Setoid] 的其它。这个导入顺序的规范被 Instance/FdVect.v 在其自身开头记录。
*)
Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Mod.Free.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * The free vector space on a set, as a universal arrow and as an
   adjunction

   nLab:      https://ncatlab.org/nlab/show/free+module
   nLab:      https://ncatlab.org/nlab/show/basis+of+a+vector+space
   Wikipedia: https://en.wikipedia.org/wiki/Free_module
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   GTM 5, §III.1, printed p. 56 — maclane:III.1:construction1
   Book: Mac Lane, ibid., §IV.1, printed p. 79 —
   maclane:IV.1:construction1
   Book: Riehl, Category Theory in Context, §4.0, printed p. 131 —
   riehl:4.0:construction-free-vector-space

   THE HEADLINE.  Mac Lane's §III.1 asks for the vector space V_X of
   formal K-linear combinations on a set X together with its insertion
   of a basis j : X → U(V_X), and for the proof that ⟨V_X, j⟩ is a
   universal arrow from X to the forgetful functor Vect_K ⟶ Set; his
   §IV.1 asks for the SAME content presented as an adjunction, with the
   bijection Vect_K(V_X, W) ≅ Set(X, U W) natural in each variable
   separately; Riehl's §4.0 asks for k[S], its functoriality in S, and
   the adjunction as the headline.  All of that is delivered here, and
   the adjunction — [free_vect_adjunction] — is the principal artifact.

   WHERE THE WORK ACTUALLY IS.  Instance/FdVect.v defines
   [Vct_F F := RMod (field_ring F)]: a vector space over F IS an
   F-module, by DEFINITION and not by an isomorphism of categories.  The
   construction of the free object therefore uses nothing about fields,
   and it is carried out over an arbitrary [RingObject] in
   Instance/Mod/Free.v — the formal-expression carrier, the linear
   extension, the universal property, the functor, the adjunction, both
   naturality clauses, the finite-linear-combination normal form and the
   non-degeneracy results all live there.  This file is the vector-space
   reading, and because the two categories are the same term, every
   specialization below is a CONVERSION: each definition is stated with
   its [Vct_F]-level type and inhabited by the [RMod]-level term, so the
   kernel checks the identification rather than a transport doing it.
   Nothing here re-proves anything.

   WHAT THE FIELD LAYER BUYS.  Exactly one thing, for exactly one
   theorem, and it is worth naming precisely.  Instance/Mod/Free.v's
   BASIS-INJECTIVITY result — and only that one — is stated under the
   hypothesis 1 ≉ 0 in the ring, because over the zero ring every module
   is trivial and that statement is genuinely false there.  (Its
   linear-independence sibling needs no such hypothesis: over the zero
   ring every scalar is already 0, so that statement degenerates to a
   truth rather than to a falsehood and survives unassisted.)  A
   [FieldObject] carries [field_one_neq_zero] as a FIELD, so over a
   field that hypothesis is discharged for free and the only remaining
   cost is a decider for the generating setoid's [≈] — see
   [free_vect_basis_distinct], the one witness below that passes
   [field_one_neq_zero Q_Field], and it passes it with no work.
   Nothing else in the development spends
   commutativity, [finv], or any other field structure — and the
   witnesses below do not either: [free_vect_half_not_one] uses a proper
   fraction as a scalar to show that the scalar ring really is ℚ, but it
   never inverts anything, so no claim is made here that [finv] is
   exercised.

   THE ℚ WITNESS, AND WHY IT IS NOT DEGENERATE.  A free vector space on
   the empty or a one-element set proves nothing, so the generating
   setoid has TWO elements and the target is ℚ regarded as a
   one-dimensional ℚ-vector space (Instance/Mod.v's [Ring_RMod] at
   [field_ring Q_Field]).  The linear extension of the assignment
   e₀ ↦ 3, e₁ ↦ 5 sends 2·e₀ + e₁ to 11, and that COMPUTES: the
   [Example]s below close by [eq_refl] on the carrier ℚ, which is the
   convertibility exception, not a claim about morphisms.  Beyond
   computation, three separations are recorded: the two basis vectors
   are distinct ([free_vect_basis_distinct]), they are linearly
   independent ([free_vect_basis_independent] — the statement a reader
   of §III.1 wants, and the one that spends no 1 ≉ 0, precisely because
   over a degenerate scalar ring it would reduce to a truth rather than
   to a falsehood), and distinct scalars give distinct multiples of one
   basis vector even when the scalars are proper fractions
   ([free_vect_half_not_one]).

   WHAT IS NOT DELIVERED.  Everything Instance/Mod/Free.v's closing
   section disclaims, in particular coefficient uniqueness and therefore
   dimension; additionally, no comparison with Instance/FdVect.v's
   [FdVectObject] (which carries a chosen coordinate isomorphism to Fⁿ),
   so it is NOT proved here that the free vector space on a finite
   generating setoid is finite-dimensional in that file's sense.  That
   comparison needs the coefficient uniqueness just disclaimed, and it
   is the natural next issue. 

   --------
   * * 集上的自由向量空间，作为一个普遍箭头和作为一个伴随关系

   nLab:       https://ncatlab.org/nlab/show/free+module 
   nLab:       https://ncatlab.org/nlab/show/basis+of+a+vector+space 
   Wikipedia:  https://en.wikipedia.org/wiki/Free_module 
   书籍: Mac Lane，《面向数学工作者的范畴论》，第二版，GTM 5，第III.1节，印刷第56页 — maclane:III.1:construction1 
   书籍: Mac Lane，同上，第IV.1节，印刷第79页 — maclane:IV.1:construction1 
   书籍: Riehl，《背景下的范畴论》，第4.0节，印刷第131页 — riehl:4.0:construction-free-vector-space标题。Mac Lane 的 §III.1 要求给定集合 X 的形式 K 线性组合的向量空间 V_X，以及其基的插入 j : X → U(V_X)，并证明 ⟨V_X, j⟩ 是从 X 到忘记函子 Vect_K ⟶ Set 的一个普遍箭；他的 §IV.1 要求以伴随的形式呈现相同的内容，其中 Vect_K(V_X, W) ≅ Set(X, U W) 在每个变量中自然双射；Riehl 的 §4.0 要求 k [S] 及其在 S 中的函子性，以及作为标题的伴随。这里提供了所有这些内容，而伴随 — [free_vect_adjunction] — 是主要成果。工作的具体所在。Instance/FdVect.v 定义了 [Vct_F F := RMod (field_ring F)]：一个 F 上的向量空间是一个 F-模，这是按定义而不是通过范畴同构获得的。因此，自由对象的构造并不涉及任何关于域的内容，并且它是在 Instance/Mod/Free.v 中的任意 [RingObject] 上进行的——形式表达载体、线性扩展、泛性质、函子、伴随、自然而然的两个条件、有限线性组合的标准形式以及非退化结果都在其中。此文件是向量空间阅读，并且因为这两个类别是相同的术语，下面的每个专门化都是一种转换：每个定义都以 [Vct_F] 级别类型陈述，并由 [RMod] 级别术语包含，所以内核检查标识，而不是由传输执行。这里没有重新证明任何内容。字段层购买的内容。恰好一件事，针对恰好一个定理，并且值得精确命名。Instance/Mod/Free.v 的 BASIS-INJECTIVITY 结果——仅此一个——是在环中假设 1 ≉ 0 的条件下陈述的，因为在零环上，每个模都是平凡的，而且该命题在那里实际上是错误的。（它的线性无关兄弟命题不需要这样的假设：在零环上，每个标量已经是 0，因此该命题退化为真理而非错误，并且无需辅助即可成立。）一 [FieldObject] 将 [field_one_neq_zero] 作为一个域，因此在域上，这个假设自动成立，唯一剩下的成本是生成集合的 [≈] 的判定器——参见 [free_vect_basis_distinct]，下面的一个证人通过 [field_one_neq_zero Q_Field]，并且无需任何工作就通过了。在该开发中没有其他内容使用交换律、[finv] 或任何其他场结构——下面的见证者也没有使用：[free_vect_half_not_one] 使用了一个适当的分数作为标量来表明标量环实际上是 ℚ，但它从未对任何东西进行求逆，因此这里没有声称 [finv] 被使用。ℚ 证人，以及它为何不是退化的。在空集或单元素集上的自由向量空间无法证明任何事情，因此生成集合具有两个元素，且目标是作为一维 ℚ-向量空间的 ℚ（Instance/Mod.v 中的 [Ring_RMod] 在 [field_ring Q_Field]）。将赋值 e₀ ↦ 3, e₁ ↦ 5 进行线性扩展，会把 2·e₀ + e₁ 送到 11，并且那可以被计算：下面的 [Example] 通过 [eq_refl] 在承载 ℚ 上闭合，这就是可转换性异常，而不是关于态射的声明。超出计算范围，记录了三种分离：两个基向量是不同的（[free_vect_basis_distinct]），它们是线性无关的（[free_vect_basis_independent] —— 这是§III.1的读者想要的陈述，也是那个在 1 ≉ 0 时不会消耗任何东西的陈述，正因为在一个简并标量环上它会化为真理而非谬误），并且即使当标量是真分数时，不同的标量也会给出一个基向量的不同倍数（[free_vect_half_not_one]）。未交付的内容。Every Instance/Mod/Free.v 的结束部分声明不承担任何责任，特别是系数唯一性，因此也不保证维度；此外，也没有与 Instance/FdVect.v 的 [FdVectObject] 进行比较（该文件带有到 Fⁿ 的选定坐标同构），所以在该文件中并未证明有限生成集合上的自由向量空间是有限维的。该比较需要刚才声明不承担的系数唯一性问题，这是自然的下一个问题。
*)

Section FreeVect.

Context (F : FieldObject).

(*
   * ** Vector spaces over F are F-modules, definitionally

   Not an isomorphism of categories and not a transport: the two are the
   same term, which is what makes every specialization below a
   conversion. 

   --------
   * ** F 上的向量空间在定义上是 F-模

   不是范畴的同构，也不是迁移：两者是相同的术语，这就是使下面的每一个特例都是一次转换的原因。
*)
Example Vct_F_is_RMod : Vct_F F = RMod (field_ring F) := eq_refl.

Definition Vct_Forget : Vct_F F ⟶ Sets := RMod_Forget (field_ring F).

Example Vct_Forget_is_RMod_Forget :
  Vct_Forget = RMod_Forget (field_ring F) := eq_refl.

(* * ** The free vector space on a set, and its basis insertion / * ** 集合上的自由向量空间及其基的插入 *)

Definition FreeVectObject (X : Sets) : Vct_F F := FreeModObject X.

Definition free_vect_insert (X : Sets)
  : X ~{Sets}~> Vct_Forget (FreeVectObject X) := fv_insert X.

(*
   * ** Mac Lane §III.1: ⟨V_X, j⟩ is a universal arrow

   Every function from X into the underlying set of a vector space W
   extends to one and only one linear map V_X ⟶ W. 

   --------
   * ** Mac Lane §III.1: ⟨V_X, j⟩ 是一个泛箭头

   从 X 到向量空间 W 的底集合的每一个函数
   都可以唯一地扩展为线性映射 V_X ⟶ W。
*)
Theorem free_vect_universal (X : Sets) :
  ∀ (W : Vct_F F) (h : X ~{Sets}~> Vct_Forget W),
    ∃! g : FreeVectObject X ~{Vct_F F}~> W,
      h ≈ fmap[Vct_Forget] g ∘ free_vect_insert X.
Proof. exact (free_module_universal X). Qed.

Definition free_vect_universal_arrow (X : Sets)
  : UniversalArrow X Vct_Forget := free_module_universal_arrow X.

(*
   * The same content in the direct encoding, where the universal object
   is named rather than projected out of a comma category. 

   --------
   * 直接编码中的相同内容，其中通用对象被命名，而不是从逗号类别中投射出来。
*)
Definition free_vect_AUniversalArrow (X : Sets)
  : AUniversalArrow X Vct_Forget (FreeVectObject X) :=
  free_module_AUniversalArrow (field_ring F) X.

(*
   * ** Mac Lane §IV.1 and Riehl §4.0: the adjunction

   The principal artifact of this issue. 

   --------
   * ** Mac Lane §IV.1 和 Riehl §4.0：对偶

   这个问题的主要产物。
*)

Definition FreeVect : Sets ⟶ Vct_F F := FreeMod (field_ring F).

Definition free_vect_adjunction : FreeVect ⊣ Vct_Forget :=
  free_module_adjunction (field_ring F).

Example FreeVect_obj (X : Sets) : FreeVect X = FreeVectObject X := eq_refl.

Example free_vect_arrow_is_insert (X : Sets) :
  @arrow _ _ X Vct_Forget (free_vect_universal_arrow X)
    = free_vect_insert X := eq_refl.

(*
   * ** Unit and counit

   The unit is the insertion of the basis, definitionally; the counit
   evaluates a formal linear combination, up to [≈] only, for the reason
   Instance/Mod/Free.v gives ([ump_universal_arrows] is [Qed]-opaque). 

   --------
   * ** 单位与余单位

   单位是基的插入，从定义上讲；余单位对形式线性组合进行评估，仅限于  [≈] ，原因是 Instance/Mod/Free.v 给出（[ump_universal_arrows] 是 [Qed] 的不透明部分）。
*)

Definition free_vect_unit (X : Sets)
  : X ~{Sets}~> Vct_Forget (FreeVect X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_vect_adjunction X.

Example free_vect_unit_is_insert (X : Sets) (x : carrier X) :
  free_vect_unit X x = free_vect_insert X x := eq_refl.

Definition free_vect_counit (W : Vct_F F)
  : FreeVect (Vct_Forget W) ~{Vct_F F}~> W :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_vect_adjunction W.

Theorem free_vect_counit_evaluates (W : Vct_F F)
  (t : @FVTerm (field_ring F) (Vct_Forget W)) :
  cmon_map (rm_hom (free_vect_counit W)) t
    ≈ fv_eval (@id Sets (Vct_Forget W)) t.
Proof. exact (free_module_counit_evaluates (field_ring F) W t). Qed.

(* * ** Riehl's functoriality on maps of generating sets Relabelling the generating set relabels the basis vectors. / * ** Riehl 关于生成集映射的函子性 重新标记生成集会重新标记基向量。 *)
Lemma free_vect_fmap_generators {X Y : Sets} (u : X ~{Sets}~> Y)
  (x : carrier X) :
  cmon_map (rm_hom (fmap[FreeVect] u)) (fv_gen x) ≈ fv_gen (u x).
Proof. exact (@free_module_fmap_generators (field_ring F) X Y u x). Qed.

(*
   * ** §IV.1's bijection, and its two naturality clauses

   Restriction to the basis is the adjunction's forward transpose, and
   it is a bijection with linear extension as its inverse.  The two
   naturality clauses are stated separately, as §IV.1 asks; each is the
   corresponding theorem of Instance/Mod/Free.v read at [Vct_F F], and
   each of those was proved there in the free module's own vocabulary
   rather than by citing the adjunction class. 

   --------
   * ** §IV.1 的双射及其两个自然性条款

   将其限制到基上是该伴随的正向转置，并且它是一个双射，其逆是线性扩展。两个自然性条款分别陈述，如 §IV.1 所要求的；每一个都是在 [Vct_F F] 处阅读 Instance/Mod/Free.v 的相应定理，并且其中每一个都是在自由模自身的词汇中证明的，而不是通过引用伴随类。
*)

Definition free_vect_restrict {X : Sets} {W : Vct_F F}
  (g : FreeVect X ~{Vct_F F}~> W) : X ~{Sets}~> Vct_Forget W :=
  fv_transpose g.

Example free_vect_restrict_is_adj {X : Sets} {W : Vct_F F}
  (g : FreeVect X ~{Vct_F F}~> W) :
  to (@adj _ _ _ _ free_vect_adjunction X W) g = free_vect_restrict g
  := eq_refl.

Lemma free_vect_restrict_extend {X : Sets} {W : Vct_F F}
  (h : X ~{Sets}~> Vct_Forget W) : free_vect_restrict (fv_extend h) ≈ h.
Proof. exact (fv_transpose_extend (field_ring F) h). Qed.

Lemma free_vect_extend_restrict {X : Sets} {W : Vct_F F}
  (g : FreeVect X ~{Vct_F F}~> W) : fv_extend (free_vect_restrict g) ≈ g.
Proof. exact (fv_extend_transpose (field_ring F) g). Qed.

(* * *** Naturality in the set variable / * *** 集合变量的自然性 *)
Theorem free_vect_naturality_in_set {X Y : Sets} {W : Vct_F F}
  (g : FreeVect Y ~{Vct_F F}~> W) (u : X ~{Sets}~> Y) :
  free_vect_restrict (g ∘ fmap[FreeVect] u) ≈ free_vect_restrict g ∘ u.
Proof. exact (free_module_naturality_in_set (field_ring F) g u). Qed.

(* * *** Naturality in the target space / * *** 目标空间的自然性 *)
Theorem free_vect_naturality_in_space {X : Sets} {W W' : Vct_F F}
  (k : W ~{Vct_F F}~> W') (g : FreeVect X ~{Vct_F F}~> W) :
  free_vect_restrict (k ∘ g) ≈ fmap[Vct_Forget] k ∘ free_vect_restrict g.
Proof. exact (free_module_naturality_in_module (field_ring F) k g). Qed.

(** ** The triangle identities / ** 三角形恒等式 *)

Corollary free_vect_triangle_left (X : Sets) :
  free_vect_counit (FreeVect X) ∘ fmap[FreeVect] (free_vect_unit X)
    ≈ @id (Vct_F F) (FreeVect X).
Proof. exact (free_module_triangle_left (field_ring F) X). Qed.

Corollary free_vect_triangle_right (W : Vct_F F) :
  fmap[Vct_Forget] (free_vect_counit W)
    ∘ free_vect_unit (Vct_Forget W) ≈ @id Sets (Vct_Forget W).
Proof. exact (free_module_triangle_right (field_ring F) W). Qed.

(*
   * ** Riehl's k[S]: every vector is a finite linear combination of basis
   vectors

   The half of the classical "finitely supported k-valued functions"
   description that does not need a decider on the generating setoid.
   Instance/Mod/Free.v's closing note says what the other half costs. 

   --------
   * ** Riehl 的 k [S]：每个向量都是基向量的有限线性组合

   经典“有限支撑 k 值函数”描述的一半，不需要生成集合上的判定器。
   Instance/Mod/Free.v 的结尾说明了另一半的代价。
*)
Theorem free_vect_finite_combination (X : Sets)
  (t : @FVTerm (field_ring F) X) :
  ∃ l : list (fv_pair (field_ring F) X), fv_eq t (fv_lc l).
Proof. exact (fv_normal_form t). Qed.

End FreeVect.

(* Only the one that changes anything: everything else discharged from the section already has [F] explicit. / 只有那个会改变任何东西的：其他从该部分释放的东西已经明确标注了 [F]。 *)
Arguments free_vect_restrict {F X W} g.

(*
   * ** The rational witness

   Two basis vectors over ℚ, and a target that is ℚ itself read as a
   one-dimensional ℚ-vector space.  The generating setoid is
   Instance/Mod/Free.v's [TwoGens] (bool under Leibniz equality),
   reused rather than rebuilt. 

   --------
   * ** 有理见证

   两个有理数上的基向量，以及一个作为一维有理数向量空间的目标 ℚ 本身。生成的集合是 Instance/Mod/Free.v 中的 [TwoGens]（Leibniz 等价下的布尔值），重复使用而非重新构建。
*)

(* Index arguments supplied once, as NOTATIONS (so each unfolds to the constructor itself) — see the same device in Instance/Mod/Free.v. / 索引参数仅提供一次，作为符号（因此每个都会展开为构造函数本身）——参见 Instance/Mod/Free.v 中的相同方法。 *)
Local Notation qgen  := (@fv_gen (field_ring Q_Field) TwoGens).
Local Notation qsmul := (@fv_smul (field_ring Q_Field) TwoGens).
Local Notation qplus := (@fv_plus (field_ring Q_Field) TwoGens).
Local Notation qzero := (@fv_zero (field_ring Q_Field) TwoGens).

(** ℚ as a vector space over itself. / ℚ 作为自身上的向量空间。 *)
Definition QLine : Vct_F Q_Field := Ring_RMod (field_ring Q_Field).

(** The assignment e₀ ↦ 3, e₁ ↦ 5. / 分配 e₀ ↦ 3, e₁ ↦ 5。 *)
Definition q_probe : TwoGens ~{Sets}~> Vct_Forget Q_Field QLine.
Proof.
  unshelve refine {| morphism := fun b : carrier TwoGens => if b then (3 # 1)%Q else (5 # 1)%Q |}.
  all: intros x y H; simpl in H; subst y; reflexivity.
Defined.

(*
   * The linear extension computes: 2·e₀ + e₁ ↦ 2·3 + 5 = 11.  This is
   [eq_refl] on the CARRIER ℚ — the convertibility exception, not a
   statement about morphisms. 

   --------
   * 线性扩展计算：2·e₀ + e₁ ↦ 2·3 + 5 = 11。这是在载体 ℚ 上的 [eq_refl] —— 可转换性例外，而不是关于态射的陈述。
*)
Example q_free_extend_computes :
  fv_eval q_probe (qplus (qsmul (2 # 1)%Q (qgen true)) (qgen false))
  = (11 # 1)%Q := eq_refl.

Example q_free_extend_generator_true :
  fv_eval q_probe (qgen true) = (3 # 1)%Q := eq_refl.

Example q_free_extend_generator_false :
  fv_eval q_probe (qgen false) = (5 # 1)%Q := eq_refl.

(*
 [TwoGens] and its distinctness are facts about the generating setoid
 alone, with no ring in them, so both come from Instance/Mod/Free.v
 ([two_gens_dec], [two_gens_distinct]) rather than being restated here. 

 --------
 [TwoGens] 及其区别性是关于生成的集合的事实，本身不涉及环，所以两者都来自 Instance/Mod/Free.v ([two_gens_dec], [two_gens_distinct])，而不是在这里重新说明。
*)

(*
   * *** The basis insertion does not collapse

   The [1 ≉ 0] premise of Instance/Mod/Free.v's general theorem is
   [field_one_neq_zero], a FIELD of [FieldObject], so over a field it
   costs nothing; only the decider is supplied. 

   --------
   * *** 基础插入不会坍塌

   Instance/Mod/Free.v 的一般定理的 [1 ≉ 0] 前提是
   [field_one_neq_zero]，一个 [FieldObject] 的域，因此在一个域上
   它没有任何成本；只提供决策器。
*)
Theorem free_vect_basis_distinct :
  fv_eq (qgen true) (qgen false) → False.
Proof.
  intro He.
  pose proof (free_module_basis_injective two_gens_dec
                (field_one_neq_zero Q_Field) true false He) as Hb.
  compute in Hb; discriminate Hb.
Qed.

(*
   * *** The basis is linearly independent

   The statement §III.1's reader wants: if r·e₀ + s·e₁ vanishes then
   both coefficients vanish.  Only the decider is spent — not
   [field_one_neq_zero] — and the reason none is needed is that over a
   trivial scalar ring every scalar is already 0, so the statement
   degenerates to a truth rather than to a falsehood.  Its content is
   therefore carried entirely by the nondegenerate case, which ℚ is. 

   --------
   * *** 基本是线性无关的

   §III.1 的读者想要的说法是：如果 r·e₀ + s·e₁ 为零，则
   两个系数都为零。只有判定器被使用——而不是
   [field_one_neq_zero]——而且之所以不需要任何理由，是因为在一个
   平凡的标量环上，每个标量已经是 0，因此该陈述
   退化为一个真理，而不是一个谬误。其内容因此完全
   由非退化情况承载，而 ℚ 就是非退化的情况。
*)
Theorem free_vect_basis_independent (r s : Q) :
  fv_eq (qplus (qsmul r (qgen true)) (qsmul s (qgen false))) qzero →
  ((r == 0)%Q * (s == 0)%Q)%type.
Proof.
  exact (@free_module_two_independent (field_ring Q_Field) TwoGens
           two_gens_dec true false two_gens_distinct r s).
Qed.

(*
   * *** Distinct scalars give distinct multiples of one basis vector

   With proper fractions, so that the scalars are visibly rational and
   not merely integers.  No decidability and no [1 ≉ 0] are spent here. 

   --------
   * *** 不同的标量给出一个基向量的不同倍数

   使用适当的分数，使得标量明显是有理数，而不仅仅是整数。在这里没有花费可判定性和 [1 ≉ 0]。
*)
Theorem free_vect_half_not_one :
  fv_eq (qsmul (1 # 2)%Q (qgen true)) (qsmul (1 # 1)%Q (qgen true)) → False.
Proof.
  intro He.
  pose proof (@free_module_scalars_faithful (field_ring Q_Field) TwoGens
                (1 # 2)%Q (1 # 1)%Q true He) as Hq.
  compute in Hq; discriminate Hq.
Qed.
