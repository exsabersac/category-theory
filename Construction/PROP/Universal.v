Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.Structural.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
Require Import Category.Construction.PROP.Instance.
Require Import Category.Construction.PROP.Interp.

From Coq Require Import Arith.

Generalizable All Variables.

(* * * The universal property of the free PROP / * * 自由 PROP 的泛性质 *)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/free+category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 Given a signature [S], a PROP [P], and a valuation [v] of the
 generators, this file packages the interpretation
 [interp : Term S m n → (⟦m⟧ ~{P}~> ⟦n⟧)] of
 [Construction/PROP/Interp.v] into a functor [InterpF : FreeCat S ⟶ P]
 and equips it with the full strict-symmetric-monoidal structure,
 then proves it UNIQUE among such functors: the free PROP [FreePROP S]
 is initial among PROPs that are equipped with an [S]-valuation and
 satisfy two side conditions on the target [P]: decidable object
 equality ([ObjDecEq], powering the axiom-free UIP on [obj P]) and a
 [Prop] reflection of the hom equivalence ([HomEqProp], powering
 [InterpF]'s respectfulness field [interp_sound]).  The free
 instance provides both by construction ([FreeCat_HomEqProp] /
 [FreeCat_ObjDecEq] in [Instance.v]).  The [Proof using] lines
 witness the split: uniqueness ([interp_unique] and its corollaries)
 needs only [ObjDecEq]; [HomEqProp] enters only through [InterpF]
 itself.

 The strictness comparisons of [InterpF] ride the PROP class fields
 VERBATIM: [strict_pure_obj] is [prop_unit_zero] and [strict_ap_obj]
 is [prop_tensor_plus] (machine-checked by [Example]s below), so the
 universal property really is stated against the strict object
 equalities every PROP carries.

 ** Design note: how "strict symmetric monoidal functor" is phrased

 A PROP carries two [Monoidal] structures on the same category — the
 strict path [MP P] and the braided/symmetric path [MB P] — related
 only by the propositional equality [prop_monoidal_coherence].  The
 classes [StrictMonoidalFunctor] (at [MP P];
 Functor/Structure/Monoidal/Strict.v) and [BraidedMonoidalFunctor]
 (at [MB P]; Functor/Structure/Monoidal/Braided.v) therefore carry
 INDEPENDENT [MonoidalFunctor] fields over propositionally-different
 target monoidals, and a hypothesis pack made of one instance of each
 would be underdetermined (nothing would relate their two tensor
 comparisons).  Uniqueness is instead phrased against ONE
 [StrictMonoidalFunctor] plus [SymmetricStrict]: the braid
 compatibility square over that SAME [ap_iso], with the braiding
 re-indexed to the strict path by [strict_braid] (the transport of
 [Interp.v]).  For competitors arriving with a genuine
 [BraidedMonoidalFunctor], the converse bridge
 [SymmetricStrict_of_Braided] converts (given the agreement of the
 two tensor comparisons across the coherence transport), and
 [InterpF_Braided] / [InterpF_Symmetric] deliver [InterpF] itself in
 those classes via the match-based [MonoidalFunctor_transport].

 ** Uniqueness

 [interp_unique] pins any [SymmetricStrict] competitor [G] that
 agrees with [v] on generators: the object agreement is a family
 [Hobj : ∀ n, G n = ⟦n⟧] of Leibniz equalities, and the morphism
 agreement is phrased by conjugating with [hom_cast] along it.  The
 theorem holds for an ARBITRARY such family — axiom-free UIP on
 [obj P] (the [ObjDecEq] class) makes any two proofs of the same
 object equality interchangeable — and the corollary
 [interp_unique_from_one] derives the whole family from the single
 datum [G 1 = ⟦1⟧] via the [G_obj] fixpoint.  [interp_unique2] is the
 resulting agreement of any two competitors.  The existence half is
 named as well: [InterpF_extends_valuation] records (by [eq_refl])
 that [InterpF] extends the valuation, and
 [InterpF_interp_unique_self] instantiates the hypothesis pack of
 [interp_unique] at [InterpF] itself, with [Hobj := eq_refl].

 The named coherence lemmas of section 2 ([interp_ap_natural],
 [interp_monoidal_unit_left/right], [interp_monoidal_assoc],
 [interp_braid_ap]) are deliberately standalone: their statements are
 purely target-side, so [Construction/PROP/Presentation/Universal.v]
 reuses them verbatim for the presented PROP. 

 --------
 nLab：https://ncatlab.org/nlab/show/PROP
 nLab：https://ncatlab.org/nlab/show/free+category
 维基百科：https://en.wikipedia.org/wiki/PROP_(category_theory)给定一个签名 [S]、一个 PROP [P]，以及生成元的一个估值 [v]，本文件将解释 [interp : Term S m n → (⟦m⟧ ~{P}~> ⟦n⟧)] 的 [Construction/PROP/Interp.v] 封装成一个函子 [InterpF : FreeCat S ⟶ P]，并为其配备完整的严格对称单体结构，然后证明它在此类函子中是唯一的：自由 PROP [FreePROP S] 在配备了 [S]-估值并满足目标 [P] 上两个附加条件的 PROP 中是初始的：可判定的对象相等性（[ObjDecEq]，为 [obj P] 上无公理 UIP 提供支持）以及同态等价的 [Prop] 反射（[HomEqProp]，为 [InterpF] 的守敬字段 [interp_sound] 提供支持）。自由实例通过构造提供两者（[FreeCat_HomEqProp] / [FreeCat_ObjDecEq] 在 [Instance.v] 中）。[Proof using] 线路
 见证了分裂：唯一性（[interp_unique] 及其推论）
 只需要 [ObjDecEq]；[HomEqProp] 仅通过 [InterpF] 本身进入。

 [InterpF] 的严格性比较依赖于 PROP 类字段
 逐字：[strict_pure_obj] 是 [prop_unit_zero]，且 [strict_ap_obj] 是 [prop_tensor_plus]（由下面的 [Example] 进行机器检查），因此普适性实际上是针对每个 PROP 所具有的严格对象相等性陈述的。

 ** 设计说明：“严格对称单体函子”如何表述一个 PROP 在同一类别上携带两个 [Monoidal] 结构——严格路径 [MP P] 和编织/对称路径 [MB P]——它们仅通过命题等式 [prop_monoidal_coherence] 相关联。因此，类 [StrictMonoidalFunctor]（位于 [MP P]；Functor/Structure/Monoidal/Strict.v）和 [BraidedMonoidalFunctor]（位于 [MB P]；Functor/Structure/Monoidal/Braided.v）在命题上不同的目标幺半群上携带独立的 [MonoidalFunctor] 字段，由每个实例组成的假设包将是不充分的（没有什么能联系它们的两个张量比较）。唯一性相反是针对一个 [StrictMonoidalFunctor] 加 [SymmetricStrict] 来表述的：在同一个 [ap_iso] 上的编织兼容性平方，其中通过 [strict_braid]（[Interp.v] 的迁移）将编织重新索引到严格路径。对于携带真正 [BraidedMonoidalFunctor] 到达的竞争者，相反的桥 [SymmetricStrict_of_Braided] 会转换（在两个张量比较在相干传输中达成一致的情况下），并且 [InterpF_Braided] / [InterpF_Symmetric] 通过基于匹配的 [MonoidalFunctor_transport] 在这些类中交付 [InterpF] 本身。

 ** 唯一性[interp_unique] 固定任何 [SymmetricStrict] 竞争者 [G]，该竞争者在生成元上同意 [v]：对象一致性是一个 Leibniz 等式的族，态射一致性通过沿着 [hom_cast] 共轭来表述。该定理对于任意这样的族都成立——在 [obj P]（[ObjDecEq] 类）上不依赖公理的 UIP 使得同一对象等式的任意两个证明可互换——并且推论 [interp_unique_from_one] 通过 [G_obj] 不动点从单一数据 [G 1 = https://ncatlab.org/nlab/show/free+category] 推导整个族。[interp_unique2] 是任意两个竞争者的结果一致性。存在性部分也被命名：[InterpF_extends_valuation] （通过 [eq_refl]）记录 [InterpF] 延伸了赋值，并且 [InterpF_interp_unique_self] 在 [InterpF] 本身实例化了 [interp_unique] 的假设包，带有 [Hobj := eq_refl]。第2节的命名一致性引理（[interp_ap_natural]、[interp_monoidal_unit_left/right]、[interp_monoidal_assoc]、[interp_braid_ap]）是刻意独立的：它们的陈述完全是目标端的，因此[Construction/PROP/Presentation/Universal.v]在所呈现的PROP中原样复用了它们。
*)

(*
   * ** Transporting a [MonoidalFunctor] across a [Monoidal] equality

   The coherence [prop_monoidal_coherence] of a PROP is a
   propositional equality between two [Monoidal] records on the same
   category.  A monoidal functor into one of them transports to the
   other by dependent elimination; as in the [BraidTransport] section
   of [Interp.v], every lemma about the transport destructs a VARIABLE
   equality, so the concrete coherence proof is never eliminated in
   any goal. 

   --------
   * ** 在  [Monoidal] 等式之间运输 [MonoidalFunctor]

   PROP 的相干性 [prop_monoidal_coherence] 是同一范畴上两个 [Monoidal] 记录之间的命题等式。到其中一个记录的幺半范子函子可以通过依赖消去运输到另一个；正如 [Interp.v] 的 [BraidTransport] 部分所示，每个关于运输的引理都会析构一个 VARIABLE 等式，因此具体的相干性证明在任何目标中都不会被消去。
*)

Definition MonoidalFunctor_transport {C D : Category} {MC : @Monoidal C}
  {N1 N2 : @Monoidal D} (e : N1 = N2) {F : C ⟶ D} :
  @MonoidalFunctor C D MC N1 F → @MonoidalFunctor C D MC N2 F :=
  match e in _ = N
        return @MonoidalFunctor C D MC N1 F → @MonoidalFunctor C D MC N F
  with eq_refl => fun X => X end.

(*
   * The tensor comparison of the transported functor is the original
   one, transported along the same equality.  Exported kit with no
   in-tree consumer yet: the braid-square transfers below are
   discharged by [SymmetricStrict_square_transport] and
   [SymmetricStrict_untransport], which move whole squares across the
   coherence rather than lone comparisons. 

   --------
   * 被传送函子的张量比较是原始的那个，沿着相同的等式传送。导出的工具包尚未在项目树中被使用：下方的编织-方形传输由 [SymmetricStrict_square_transport] 和 [SymmetricStrict_untransport] 处理，它们将整个方形整体移动通过相干性，而不是单独的比较。
*)
Lemma ap_iso_transport {C D : Category} {MC : @Monoidal C}
  {N1 N2 : @Monoidal D} (e : N1 = N2) {F : C ⟶ D}
  (MF : @MonoidalFunctor C D MC N1 F) (x y : C) :
  to (@ap_iso C D MC N2 F (MonoidalFunctor_transport e MF) x y)
  = match e in _ = N
          return ((F x ⨂[N] F y)%object ~{D}~> F ((x ⨂[MC] y)%object))
    with eq_refl => to (@ap_iso C D MC N1 F MF x y) end.
Proof. destruct e; reflexivity. Qed.

Section Universal.

Context (S : Signature).
Context (P : PROP).
Context {HP : HomEqProp P}.
Context {OD : @ObjDecEq P}.
Context (v : Valuation P S).

Open Scope nat_scope.

Notation "⟦ n ⟧" := (@prop_of_nat P n) (at level 0, format "⟦ n ⟧").

(*
   * ** 1. The interpretation functor

   Objects go to [prop_of_nat]; morphisms go through [interp].
   Respectfulness is exactly the soundness theorem of [Interp.v], and
   the functor laws hold by computation, because [interp] reduces on
   the [T_id] and [T_comp] constructors. 

   --------
   * ** 1. 解释函子

   对象映射到 [prop_of_nat]；态射通过 [interp] 映射。
   保持性恰好是 [Interp.v] 的正确性定理，并且
   由于 [interp] 在 [T_id] 和 [T_comp] 构造子上归约，因此函子定律通过计算成立。
*)

Lemma InterpF_fmap_id (n : nat) :
  interp P S v (T_id n) ≈ id[⟦n⟧].
Proof. reflexivity. Qed.

Lemma InterpF_fmap_comp {m n p : nat} (f : Term S n p) (g : Term S m n) :
  interp P S v (T_comp f g) ≈ interp P S v f ∘ interp P S v g.
Proof. reflexivity. Qed.

(*
 Built with an explicit [Build_Functor] so that the source and target
 categories are pinned (the [QuotientProj] discipline of
 [Construction/Quotient.v]); a bare record literal would try to infer
 them from the field values, which live in [nat] and [P]. 

 --------
 使用显式的 [Build_Functor] 构建，以便源类别和目标类别被固定（[QuotientProj] 领域的 [Construction/Quotient.v]）；一个裸记录字面量会尝试从字段值推断它们，这些字段值位于 [nat] 和 [P] 中。
*)
Definition InterpF : FreeCat S ⟶ P :=
  Build_Functor (FreeCat S) P
    (@prop_of_nat P)
    (fun m n t => interp P S v t)
    (fun m n s t Hst => interp_sound P S v Hst)
    InterpF_fmap_id
    (fun m n p f g => InterpF_fmap_comp f g).

(*
   * Machine-checked: [InterpF] EXTENDS the valuation — every generator
   is sent to its assigned morphism, definitionally.  Together with
   [InterpF_interp_unique_self] below, this is the existence half of
   the universal property in named form. 

   --------
   * 机器检查：[InterpF] 扩展了估值——每个生成元都被发送到其定义上的态射。结合下面的 [InterpF_interp_unique_self]，这是以命名形式表示的泛性质的存在性部分。
*)
Example InterpF_extends_valuation (m n : nat) (g : S m n) :
  fmap[InterpF] (T_gen g) = v m n g := eq_refl.

(*
   * ** 2. Named coherence lemmas

   Every statement is purely target-side (only [P]-morphisms appear),
   so [Presentation/Universal.v] can reuse them for the presented
   PROP, whose structural maps are the very same [T_cast] terms.

   The [_general] lemmas quantify over the object equalities: after
   destructing them, the single non-destructible residue is aligned
   with the canonical strict equality by [obj_uip] (axiom-free UIP on
   [obj P], from [ObjDecEq]). 

   --------
   * ** 2. 命名的相干引理

   每个陈述完全是目标侧的（只出现 [P] -态射），
   因此 [Presentation/Universal.v] 可以将它们用于所呈现的
   PROP，其结构映射正是 [T_cast] 项。

   [_general] 引理对对象等式进行量化：在析构它们之后，唯一无法析构的剩余部分与规范严格等式通过 [obj_uip] 对齐（在 [obj P] 上的无公理UIP，由 [ObjDecEq] 提供）。
*)

(*
   * Naturality of the tensor-comparison cast against [interp]: the
   conjugating cast of [⊞] cancels its inverse. 

   --------
   * 张量比较在 [interp] 上的自然性：[⊞] 的共轭变换抵消了它的逆变换。
*)
Lemma interp_ap_natural {m n m' n'} (f : Term S m m') (g : Term S n n') :
  interp P S v (T_tens f g) ∘ id_cast (prop_tensor_plus m n)
    ≈ id_cast (prop_tensor_plus m' n')
        ∘ (interp P S v f ⨂[MP P] interp P S v g).
Proof.
  cbn [interp].
  unfold prop_tensor_hom.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

(** The inverse-direction square, by flipping across the casts. / 反向平方，通过跨模具翻转。 *)
Lemma interp_ap_natural_from {m n m' n'} (f : Term S m m') (g : Term S n n') :
  (interp P S v f ⨂[MP P] interp P S v g)
      ∘ id_cast (eq_sym (prop_tensor_plus m n))
    ≈ id_cast (eq_sym (prop_tensor_plus m' n'))
        ∘ interp P S v (T_tens f g).
Proof.
  apply id_cast_flip.
  apply interp_ap_natural.
Qed.

(*
   * General left-unit coherence: with every comparison an [id_cast],
   the left-unitality square collapses to the strict unitor. 

   --------
   * 一般左单位一致性：每次比较都有一个[id_cast]，
   左单位性方格坍缩为严格酉子。
*)
Lemma to_unit_left_cast_general {u w s : P}
  (eu : @I P (MP P) = u) (e : (u ⨂[MP P] w)%object = s) (d : s = w) :
  to (@unit_left P (MP P) w)
    ≈ id_cast d ∘ id_cast e ∘ (id_cast eu ⨂[MP P] id[w]).
Proof using OD P.
  destruct eu, e.
  rewrite !id_cast_refl.
  rewrite bimap_id_id.
  rewrite (obj_uip d (strict_unit_left_obj w)).
  rewrite !id_right.
  symmetry; apply strict_unitl_cast.
Qed.

(** General right-unit coherence. / 一般右单元一致性。 *)
Lemma to_unit_right_cast_general {u w s : P}
  (eu : @I P (MP P) = u) (e : (w ⨂[MP P] u)%object = s) (d : s = w) :
  to (@unit_right P (MP P) w)
    ≈ id_cast d ∘ id_cast e ∘ (id[w] ⨂[MP P] id_cast eu).
Proof using OD P.
  destruct eu, e.
  rewrite !id_cast_refl.
  rewrite bimap_id_id.
  rewrite (obj_uip d (strict_unit_right_obj w)).
  rewrite !id_right.
  symmetry; apply strict_unitr_cast.
Qed.

(** General associativity coherence. / 一般结合性一致性。 *)
Lemma to_assoc_cast_general {a b c ab bc u w : P}
  (eab : (a ⨂[MP P] b)%object = ab)
  (ebc : (b ⨂[MP P] c)%object = bc)
  (eu : (ab ⨂[MP P] c)%object = u)
  (ew : (a ⨂[MP P] bc)%object = w)
  (d : u = w) :
  id_cast d ∘ id_cast eu ∘ (id_cast eab ⨂[MP P] id[c])
    ≈ id_cast ew ∘ (id[a] ⨂[MP P] id_cast ebc)
        ∘ to (@tensor_assoc P (MP P) a b c).
Proof using OD P.
  destruct eab, ebc, eu, ew.
  rewrite !id_cast_refl.
  rewrite !bimap_id_id.
  rewrite (obj_uip d (strict_assoc_obj a b c)).
  rewrite !id_right, !id_left.
  apply strict_assoc_cast.
Qed.

(*
   * The left-unitality field of [MonoidalFunctor] at [InterpF]. 

   --------
   * 在  [InterpF] 处的  [MonoidalFunctor]  的左单位性场。
*)
Lemma interp_monoidal_unit_left (x : nat) :
  to (@unit_left P (MP P) ⟦x⟧)
    ≈ interp P S v (T_cast (Nat.add_0_l x))
        ∘ id_cast (prop_tensor_plus 0 x)
        ∘ (id_cast (@prop_unit_zero P) ⨂[MP P] id[⟦x⟧]).
Proof using OD P S v.
  rewrite interp_T_cast.
  unfold hcast.
  apply to_unit_left_cast_general.
Qed.

(*
   * The right-unitality field of [MonoidalFunctor] at [InterpF]. 

   --------
   * 在  [InterpF] 上  [MonoidalFunctor] 的右幺元性域。
*)
Lemma interp_monoidal_unit_right (x : nat) :
  to (@unit_right P (MP P) ⟦x⟧)
    ≈ interp P S v (T_cast (Nat.add_0_r x))
        ∘ id_cast (prop_tensor_plus x 0)
        ∘ (id[⟦x⟧] ⨂[MP P] id_cast (@prop_unit_zero P)).
Proof using OD P S v.
  rewrite interp_T_cast.
  unfold hcast.
  apply to_unit_right_cast_general.
Qed.

(*
   * The associativity field of [MonoidalFunctor] at [InterpF]. 

   --------
   * [MonoidalFunctor] 在 [InterpF] 的结合性字段。
*)
Lemma interp_monoidal_assoc (x y z : nat) :
  interp P S v (T_cast (eq_sym (Nat.add_assoc x y z)))
      ∘ id_cast (prop_tensor_plus (x + y) z)
      ∘ (id_cast (prop_tensor_plus x y) ⨂[MP P] id[⟦z⟧])
    ≈ id_cast (prop_tensor_plus x (y + z))
        ∘ (id[⟦x⟧] ⨂[MP P] id_cast (prop_tensor_plus y z))
        ∘ to (@tensor_assoc P (MP P) ⟦x⟧ ⟦y⟧ ⟦z⟧).
Proof using OD P S v.
  rewrite interp_T_cast.
  unfold hcast.
  apply to_assoc_cast_general.
Qed.

(*
   * The braid-compatibility square of [interp] against the target's
   strict-path braiding [strict_braid]. 

   --------
   * [interp] 对目标的严格路径编织 [strict_braid] 的编织兼容性方阵。
*)
Lemma interp_braid_ap (m n : nat) :
  interp P S v (T_braid m n) ∘ id_cast (prop_tensor_plus m n)
    ≈ id_cast (prop_tensor_plus n m) ∘ strict_braid P ⟦m⟧ ⟦n⟧.
Proof.
  cbn [interp].
  unfold prop_braid.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

(*
   * ** 3. The strong and strict monoidal structure on [InterpF]

   The tensor comparison is the [prop_tensor_plus] cast, packaged as
   a natural isomorphism in the functor category. 

   --------
   * ** 3. 在  [InterpF] 上的强且严格的单oidal 结构

   张量比较是  [prop_tensor_plus] 的转换，封装为函子范畴中的自然同构。
*)

Definition InterpF_ap_dom : FreeCat S ∏ FreeCat S ⟶ P :=
  @tensor P (MP P) ◯ InterpF ∏⟶ InterpF.

Definition InterpF_ap_cod : FreeCat S ∏ FreeCat S ⟶ P :=
  InterpF ◯ @tensor (FreeCat S) (FreeCat_Monoidal S).

Definition InterpF_ap_to : InterpF_ap_dom ⟹ InterpF_ap_cod :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) P InterpF_ap_dom InterpF_ap_cod
    (fun mn => id_cast (prop_tensor_plus (fst mn) (snd mn)))
    (fun x y f => interp_ap_natural (fst f) (snd f)).

Definition InterpF_ap_from : InterpF_ap_cod ⟹ InterpF_ap_dom :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) P InterpF_ap_cod InterpF_ap_dom
    (fun mn => id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn))))
    (fun x y f => interp_ap_natural_from (fst f) (snd f)).

(*
   * The two composites are the identity transformation, componentwise.
   (In the functor category the identity's component at [mn] is
   [fmap id], which on each side reduces to a tensor of identities.) 

   --------
   * 这两个复合是逐分量的恒等变换。
   （在函子范畴中，恒等变换在 [mn] 处的分量是 [fmap id]， 在每一边都约简为恒等映射的张量。）
*)
Lemma InterpF_ap_to_from (mn : FreeCat S ∏ FreeCat S) :
  id_cast (prop_tensor_plus (fst mn) (snd mn))
      ∘ id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn)))
    ≈ interp P S v (T_tens (T_id (fst mn)) (T_id (snd mn))).
Proof.
  rewrite id_cast_inv_r.
  symmetry.
  cbn [interp].
  apply tensor_hom_id.
Qed.

Lemma InterpF_ap_from_to (mn : FreeCat S ∏ FreeCat S) :
  id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn)))
      ∘ id_cast (prop_tensor_plus (fst mn) (snd mn))
    ≈ (interp P S v (T_id (fst mn)) ⨂[MP P] interp P S v (T_id (snd mn))).
Proof.
  rewrite id_cast_inv_l.
  symmetry.
  cbn [interp].
  apply bimap_id_id.
Qed.

Program Definition InterpF_ap_iso :
  InterpF_ap_dom ≅[[FreeCat S ∏ FreeCat S, P]] InterpF_ap_cod := {|
  to := InterpF_ap_to;
  from := InterpF_ap_from;
  iso_to_from := InterpF_ap_to_from;
  iso_from_to := InterpF_ap_from_to
|}.

(*
   * The strong monoidal structure.  All proof fields are the named
   lemmas of section 2; the derived-iso data fields are casts. 

   --------
   * 强单体结构。所有证明字段都是第2节的命名引理；派生同构数据字段是类型转换。
*)
Program Definition InterpF_Monoidal :
  @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) InterpF := {|
  pure_iso := id_cast_iso (@prop_unit_zero P);
  ap_functor_iso := InterpF_ap_iso;
  pure_iso_left := fun x : nat => @unit_left P (MP P) ⟦x⟧;
  pure_iso_right := fun x : nat =>
    iso_compose
      (id_cast_iso (f_equal (@prop_of_nat P) (eq_sym (Nat.add_0_r x))))
      (@unit_right P (MP P) ⟦x⟧);
  ap_iso_assoc := fun x y z : nat =>
    id_cast_iso
      (eq_trans
         (f_equal (fun u : P => (u ⨂[MP P] ⟦z⟧)%object)
                  (prop_tensor_plus x y))
         (eq_trans (prop_tensor_plus (x + y) z)
                   (f_equal (@prop_of_nat P)
                            (eq_sym (Nat.add_assoc x y z)))));
  monoidal_unit_left := interp_monoidal_unit_left;
  monoidal_unit_right := interp_monoidal_unit_right;
  monoidal_assoc := interp_monoidal_assoc
|}.

(*
   * The comparisons ARE the PROP's strictness equalities, verbatim. 

   --------
   * 这些比较是道具严格相等性的逐字比较。
*)
Lemma InterpF_strict_pure_iso_id :
  to (@pure_iso _ _ _ _ InterpF InterpF_Monoidal)
    ≈ match @prop_unit_zero P in _ = T return @I P (MP P) ~{P}~> T
      with eq_refl => id end.
Proof. reflexivity. Qed.

Lemma InterpF_strict_ap_iso_id (x y : nat) :
  to (@ap_iso _ _ _ _ InterpF InterpF_Monoidal x y)
    ≈ match @prop_tensor_plus P x y in _ = T
            return ((InterpF x ⨂[MP P] InterpF y)%object ~{P}~> T)
      with eq_refl => id end.
Proof. reflexivity. Qed.

Program Definition InterpF_Strict :
  @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) InterpF := {|
  strict_functor_is_monoidal := InterpF_Monoidal;
  strict_pure_obj := @prop_unit_zero P;               (* the PROP field / PROP字段 *)
  strict_ap_obj := fun x y : nat => @prop_tensor_plus P x y;  (* ditto *)
  strict_pure_iso_id := InterpF_strict_pure_iso_id;
  strict_ap_iso_id := InterpF_strict_ap_iso_id
|}.

(*
   * Machine-checked: the strict object comparisons of [InterpF_Strict]
   are the PROP class fields themselves. 

   --------
   * 机器检查：[InterpF_Strict] 的严格对象比较是 PROP 类字段本身。
*)
Example InterpF_strict_pure_obj_is_prop_unit_zero :
  @strict_pure_obj _ _ _ _ InterpF InterpF_Strict = @prop_unit_zero P
  := eq_refl.

Example InterpF_strict_ap_obj_is_prop_tensor_plus (x y : nat) :
  @strict_ap_obj _ _ _ _ InterpF InterpF_Strict x y = @prop_tensor_plus P x y
  := eq_refl.

(*
   * ** 4. Symmetry

   [SymmetricStrict G MG] is the braid-compatibility square of a
   monoidal functor [G] over ITS OWN tensor comparison, with the
   target braiding re-indexed to the strict path by [strict_braid].
   See the header for why uniqueness is phrased against this bundle
   rather than against the two independent
   [StrictMonoidalFunctor]/[BraidedMonoidalFunctor] classes of
   Functor/Structure/Monoidal/{Strict,Braided}.v. 

   --------
   * ** 4. 对称性

   [SymmetricStrict G MG] 是一个单体函子 [G] 在其自身张量比较上的编织兼容方格，其目标编织通过 [strict_braid] 重新索引到严格路径。请参见标题，了解为什么唯一性是针对该束而不是针对两个独立的 [StrictMonoidalFunctor] / [BraidedMonoidalFunctor] 类 Functor/Structure/Monoidal/{Strict,Braided}.v 进行表述的。
*)

Definition SymmetricStrict (G : FreeCat S ⟶ P)
  (MG : @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) G) : Type :=
  ∀ m n : nat,
    fmap[G] (T_braid m n) ∘ to (@ap_iso _ _ _ _ G MG m n)
      ≈ to (@ap_iso _ _ _ _ G MG n m) ∘ strict_braid P (G m) (G n).

Lemma InterpF_SymmetricStrict : SymmetricStrict InterpF InterpF_Monoidal.
Proof.
  intros m n.
  exact (interp_braid_ap m n).
Qed.

(*
   * *** Bridges to the [BraidedMonoidalFunctor]/[SymmetricMonoidalFunctor]
   classes of Functor/Structure/Monoidal/Braided.v

   The braid square at the transported functor is the braid square at
   the original functor against the transported braid family; both
   lemmas destruct a VARIABLE [Monoidal] equality, so the concrete
   [prop_monoidal_coherence] is never eliminated in a goal. 

   --------
   * *** 到 [BraidedMonoidalFunctor] / [SymmetricMonoidalFunctor] 类别 Functor/Structure/Monoidal/Braided.v 的桥梁

   在传输的函子上的编织平方是原始函子针对传输编织族的编织平方；两个引理都分解了一个 VARIABLE [Monoidal] 等式，因此具体的 [prop_monoidal_coherence] 在目标中从未被消除。
*)

Lemma SymmetricStrict_square_transport
  {N1 N2 : @Monoidal P} (e : N1 = N2)
  (G : FreeCat S ⟶ P)
  (MG : @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) N1 G)
  (b : braid_family N2) (x y : nat) :
  fmap[G] (T_braid x y) ∘ to (@ap_iso _ _ _ _ G MG x y)
      ≈ to (@ap_iso _ _ _ _ G MG y x) ∘ transport_braid e b (G x) (G y) →
  fmap[G] (T_braid x y)
      ∘ to (@ap_iso _ _ _ _ G (MonoidalFunctor_transport e MG) x y)
    ≈ to (@ap_iso _ _ _ _ G (MonoidalFunctor_transport e MG) y x)
        ∘ b (G x) (G y).
Proof.
  revert b; destruct e; intros b H.
  exact H.
Qed.

(*
   * The converse direction: a braid square at the transported functor
   comes back to one at the original, against the transported braid. 

   --------
   * 相反方向：传递函子上的编织平方会回到原来的一个，对抗传递的编织。
*)
Lemma SymmetricStrict_untransport
  {N1 N2 : @Monoidal P} (e : N1 = N2)
  (G : FreeCat S ⟶ P)
  (MG : @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) N1 G)
  (MG' : @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) N2 G)
  (b : braid_family N2)
  (Hap : ∀ x y : nat,
     to (@ap_iso _ _ _ _ G (MonoidalFunctor_transport e MG) x y)
       ≈ to (@ap_iso _ _ _ _ G MG' x y))
  (Hsq : ∀ x y : nat,
     fmap[G] (T_braid x y) ∘ to (@ap_iso _ _ _ _ G MG' x y)
       ≈ to (@ap_iso _ _ _ _ G MG' y x) ∘ b (G x) (G y)) :
  ∀ x y : nat,
    fmap[G] (T_braid x y) ∘ to (@ap_iso _ _ _ _ G MG x y)
      ≈ to (@ap_iso _ _ _ _ G MG y x) ∘ transport_braid e b (G x) (G y).
Proof.
  revert MG' b Hap Hsq; destruct e; intros MG' b Hap Hsq x y.
  simpl in Hap.
  rewrite (Hap x y), (Hap y x).
  exact (Hsq x y).
Qed.

(*
   * [InterpF] as a [BraidedMonoidalFunctor]: the underlying
   strong structure is [InterpF_Monoidal] transported across the
   coherence, and the braid square is [InterpF_SymmetricStrict]. 

   --------
   *  [InterpF] 作为  [BraidedMonoidalFunctor] ：其底层的强结构是  [InterpF_Monoidal] ，通过相干性进行传递，且编结平方是  [InterpF_SymmetricStrict] 。
*)
Program Definition InterpF_Braided :
  @BraidedMonoidalFunctor (FreeCat S) P (FreeCat_Braided S)
    (@symmetric_is_braided P (@prop_symmetric P)) InterpF := {|
  braided_is_strong :=
    MonoidalFunctor_transport (@prop_monoidal_coherence P) InterpF_Monoidal
|}.
Next Obligation.
  exact (SymmetricStrict_square_transport (@prop_monoidal_coherence P)
           InterpF InterpF_Monoidal
           (fun a b : P =>
              @braid P (@symmetric_is_braided P (@prop_symmetric P)) a b)
           x y (InterpF_SymmetricStrict x y)).
Qed.

(*
   * [SymmetricMonoidalFunctor] is a [Definition] alias in
   [Functor/Structure/Monoidal/Braided.v], so the instance is supplied
   explicitly rather than by class search. 

   --------
   * [SymmetricMonoidalFunctor] 是 [Functor/Structure/Monoidal/Braided.v] 中的 [Definition] 别名，因此实例是显式提供的，而不是通过类搜索获取的。
*)
Definition InterpF_Symmetric :
  @SymmetricMonoidalFunctor (FreeCat S) P (FreeCat_Symmetric S)
    (@prop_symmetric P) InterpF := InterpF_Braided.

(*
   * Competitors arriving with a [BraidedMonoidalFunctor]
   convert to [SymmetricStrict], given that their two tensor
   comparisons agree across the coherence transport. 

   --------
   * 对于携带 [BraidedMonoidalFunctor] 到达的竞争者，若其两个张量比较在相干传输中一致，则转换为 [SymmetricStrict]。
*)
Corollary SymmetricStrict_of_Braided
  (G : FreeCat S ⟶ P)
  (SG : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) G)
  (BG : @BraidedMonoidalFunctor (FreeCat S) P (FreeCat_Braided S)
          (@symmetric_is_braided P (@prop_symmetric P)) G)
  (Hap : ∀ x y : nat,
     to (@ap_iso _ _ _ _ G
           (MonoidalFunctor_transport (@prop_monoidal_coherence P)
              (@strict_functor_is_monoidal _ _ _ _ G SG)) x y)
       ≈ to (@ap_iso _ _ _ _ G (@braided_is_strong _ _ _ _ G BG) x y)) :
  SymmetricStrict G SG.
Proof.
  exact (SymmetricStrict_untransport (@prop_monoidal_coherence P) G
           (@strict_functor_is_monoidal _ _ _ _ G SG)
           (@braided_is_strong _ _ _ _ G BG)
           (fun a b : P =>
              @braid P (@symmetric_is_braided P (@prop_symmetric P)) a b)
           Hap
           (fun x y => @braid_compat _ _ _ _ G BG x y)).
Qed.

(*
   * ** 5. Uniqueness

   The cast toolbox is the transport kit of
   [Construction/Quotient.v] — sliding a cast across an equation
   ([comp_cast_shift]), fusing nested cast conjugations
   ([id_cast_conj_fuse]), identifying conjugations along different
   proofs of the same object equalities ([id_cast_conj_irr], UIP),
   and round-tripping [hom_cast]s ([hom_cast_roundtrip]) — plus its
   monoidal extension [bimap_hom_cast] from
   [Construction/PROP/Interp.v]. 

   --------
   * ** 5. 独特性

   铸造工具箱是 [Construction/Quotient.v] 的传输工具包——在方程上滑动一个类型转换 ([comp_cast_shift])，融合嵌套的类型转换共轭 ([id_cast_conj_fuse])，识别同一对象等式的不同证明中的共轭 ([id_cast_conj_irr]，UIP)，以及往返 [hom_cast] ([hom_cast_roundtrip]) ——加上它的单体扩展 [bimap_hom_cast] 来自 [Construction/PROP/Interp.v]。
*)

Section Uniqueness.

Context (G : FreeCat S ⟶ P).
Context (SG : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S)
                (MP P) G).
Context (HB : SymmetricStrict G SG).
Context (Hobj : ∀ n : nat, G n = ⟦n⟧).
Context (Hgen : ∀ m n (g : S m n),
  fmap[G] (T_gen g)
    ≈ hom_cast (eq_sym (Hobj m)) (eq_sym (Hobj n)) (v m n g)).

(*
   * The tensor comparison of [SG], spelled as an [id_cast]. 

   --------
   * 张量比较 [SG]，被拼写为 [id_cast]。
*)
Lemma G_ap_cast (x y : nat) :
  to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof. exact (@strict_ap_iso_id _ _ _ _ G SG x y). Qed.

(*
   * Naturality of [SG]'s tensor comparison at a pair of terms. 

   --------
   * [SG] 在一对项上的张量比较的自然性。
*)
Lemma G_ap_natural {m1 m2 n1 n2 : nat}
  (f : Term S m1 n1) (g : Term S m2 n2) :
  fmap[G] (T_tens f g)
      ∘ to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG)
              m1 m2)
    ≈ to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG)
            n1 n2)
        ∘ (fmap[G] f ⨂[MP P] fmap[G] g).
Proof.
  exact (naturality
           (to (@ap_functor_iso _ _ _ _ G
                  (@strict_functor_is_monoidal _ _ _ _ G SG)))
           (m1, m2) (n1, n2) (f, g)).
Qed.

(*
   * Main uniqueness: any strict symmetric competitor agreeing with [v]
   on generators agrees with [interp] on every term, up to the
   [hom_cast] conjugation along the object family [Hobj].  The proof
   is a structural induction on terms; thanks to UIP on [obj P], it
   works for an ARBITRARY family [Hobj], with no coherence hypothesis
   relating its members. 

   --------
   * 主要独特性：任何在生成元上与  [v] 一致的严格对称竞争者，都在每一项上与  [interp] 一致，最多相差沿对象族  [Hobj] 的  [hom_cast] 共轭。证明是基于项的结构归纳；得益于  [obj P] 上的 UIP，它适用于任意家族  [Hobj] ，无需关于其成员的任何一致性假设。
*)
Theorem interp_unique : ∀ m n (t : Term S m n),
  fmap[G] t ≈ hom_cast (eq_sym (Hobj m)) (eq_sym (Hobj n)) (interp P S v t).
Proof using G HB Hgen Hobj OD P S SG v.
  intros m n t.
  induction t as [k | bm bn | cm cn cp tg IHg tf IHf
                  | m1 n1 m2 n2 tf IHf tg IHg | gm gn gs].
  - (* T_id *)
    cbn [interp].
    rewrite hom_cast_id.
    exact (@fmap_id (FreeCat S) P G k).
  - (* T_braid *)
    cbn [interp].
    unfold prop_braid.
    assert (Hb : fmap[G] (T_braid bm bn)
              ≈ id_cast (@strict_ap_obj _ _ _ _ G SG bn bm)
                  ∘ strict_braid P (G bm) (G bn)
                  ∘ id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG bm bn))).
    { apply comp_cast_shift.
      rewrite <- !G_ap_cast.
      apply HB. }
    rewrite Hb.
    rewrite (strict_braid_cast P (eq_sym (Hobj bm)) (eq_sym (Hobj bn))).
    rewrite !hom_cast_decompose.
    rewrite !id_cast_conj_fuse.
    apply id_cast_conj_irr.
  - (* T_comp *)
    cbn [interp].
    rewrite <- (hom_cast_comp (eq_sym (Hobj cm)) (eq_sym (Hobj cn))
                  (eq_sym (Hobj cp))).
    rewrite <- IHg, <- IHf.
    exact (@fmap_comp (FreeCat S) P G cm cn cp tg tf).
  - (* T_tens *)
    cbn [interp].
    unfold prop_tensor_hom.
    assert (Ht : fmap[G] (T_tens tf tg)
              ≈ id_cast (@strict_ap_obj _ _ _ _ G SG n1 n2)
                  ∘ (fmap[G] tf ⨂[MP P] fmap[G] tg)
                  ∘ id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG m1 m2))).
    { apply comp_cast_shift.
      rewrite <- !G_ap_cast.
      apply G_ap_natural. }
    rewrite Ht.
    rewrite IHf, IHg.
    rewrite (bimap_hom_cast P).
    rewrite !hom_cast_decompose.
    rewrite !id_cast_conj_fuse.
    apply id_cast_conj_irr.
  - (* T_gen *)
    apply Hgen.
Qed.

End Uniqueness.

(*
   * *** Existence, machine-checked against the hypothesis pack

   [InterpF] itself — with its strict structure [InterpF_Strict], its
   braid square [InterpF_SymmetricStrict], and the object family
   [Hobj := eq_refl] (its object action is [prop_of_nat] on the nose)
   — satisfies the hypotheses of [interp_unique]: the generator
   agreement is [InterpF_extends_valuation] up to trivial casts, and
   instantiating the theorem at [InterpF] typechecks.  This is the
   named witness that the mediating functor of the existence half is
   itself pinned by the uniqueness half. 

   --------
   * *** 存在性，经机器检查以验证假设包

   [InterpF] 本身——带有它严格的结构 [InterpF_Strict]，
   它的辫方 [InterpF_SymmetricStrict]，以及对象家族 [Hobj := eq_refl]
   （它的对象作用正好是 [prop_of_nat]）
   ——满足 [interp_unique] 的假设：生成元一致性在平凡转换下为 [InterpF_extends_valuation]，
   并且在 [InterpF] 处实例化定理类型检查成功。这是存在性部分的调解函子
   本身由唯一性部分固定的命名证据。
*)

Example InterpF_generator_agreement (m n : nat) (g : S m n) :
  fmap[InterpF] (T_gen g)
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦m⟧)) (eq_sym (@eq_refl _ ⟦n⟧))
               (v m n g).
Proof. reflexivity. Qed.

Example InterpF_interp_unique_self (m n : nat) (t : Term S m n) :
  fmap[InterpF] t
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦m⟧)) (eq_sym (@eq_refl _ ⟦n⟧))
               (interp P S v t).
Proof.
  exact (interp_unique InterpF InterpF_Strict InterpF_SymmetricStrict
           (fun k : nat => eq_refl) InterpF_generator_agreement m n t).
Qed.

(*
   * *** Uniqueness from a single object datum

   The object family [Hobj] can be synthesised from the single
   equality [G 1 = ⟦1⟧]: zero-arity agreement is [strict_pure_obj]
   against [prop_unit_zero], and successor agreement peels one wire
   off with [strict_ap_obj] against [prop_tensor_plus], using the
   definitional facts [1 ⨂ k = 1 + k = S k] on the free side. 

   --------
   * *** 来自单个对象数据的唯一性

   对象族 [Hobj] 可以通过单个相等性 [G 1 = [G 1 = ⟦1⟧]] 综合生成：零元同意为 [strict_pure_obj] 对 [prop_unit_zero]，而后继同意则通过 [strict_ap_obj] 对 [prop_tensor_plus] 剥离一根线，使用自由侧的定义事实 [1 ⨂ k = 1 + k = S k]。
*)

Section UniquenessFromOne.

Context (G : FreeCat S ⟶ P).
Context (SG : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S)
                (MP P) G).
Context (HB : SymmetricStrict G SG).
Context (H1 : G 1 = ⟦1⟧).

Fixpoint G_obj (n : nat) : G n = ⟦n⟧ :=
  match n with
  | O => eq_trans (eq_sym (@strict_pure_obj _ _ _ _ G SG))
                  (@prop_unit_zero P)
  | Datatypes.S k =>
      eq_trans
        (eq_sym (@strict_ap_obj _ _ _ _ G SG 1 k))
        (eq_trans
           (f_equal2 (fun a b : P => (a ⨂[MP P] b)%object) H1 (G_obj k))
           (@prop_tensor_plus P 1 k))
  end.

Corollary interp_unique_from_one
  (Hgen : ∀ m n (g : S m n),
     fmap[G] (T_gen g)
       ≈ hom_cast (eq_sym (G_obj m)) (eq_sym (G_obj n)) (v m n g)) :
  ∀ m n (t : Term S m n),
    fmap[G] t ≈ hom_cast (eq_sym (G_obj m)) (eq_sym (G_obj n))
                         (interp P S v t).
Proof using G H1 HB OD P S SG v. exact (interp_unique G SG HB G_obj Hgen). Qed.

End UniquenessFromOne.

(*
   * *** Agreement of competitors

   Any two strict symmetric functors that agree with [v] on the
   generators agree with each other on every term, after re-indexing
   both to the canonical objects. 

   --------
   * *** 竞争者的一致性

   任何两个在生成元上与 [v] 一致的严格对称函子，在将两者重新索引到标准对象后，在每一个项上都彼此一致。
*)

Corollary interp_unique2
  (G1 : FreeCat S ⟶ P)
  (SG1 : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) G1)
  (HB1 : SymmetricStrict G1 SG1)
  (Hobj1 : ∀ n : nat, G1 n = ⟦n⟧)
  (Hgen1 : ∀ m n (g : S m n),
     fmap[G1] (T_gen g)
       ≈ hom_cast (eq_sym (Hobj1 m)) (eq_sym (Hobj1 n)) (v m n g))
  (G2 : FreeCat S ⟶ P)
  (SG2 : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) G2)
  (HB2 : SymmetricStrict G2 SG2)
  (Hobj2 : ∀ n : nat, G2 n = ⟦n⟧)
  (Hgen2 : ∀ m n (g : S m n),
     fmap[G2] (T_gen g)
       ≈ hom_cast (eq_sym (Hobj2 m)) (eq_sym (Hobj2 n)) (v m n g)) :
  ∀ m n (t : Term S m n),
    hom_cast (Hobj1 m) (Hobj1 n) (fmap[G1] t)
      ≈ hom_cast (Hobj2 m) (Hobj2 n) (fmap[G2] t).
Proof using OD P S v.
  intros m n t.
  rewrite (interp_unique G1 SG1 HB1 Hobj1 Hgen1 m n t).
  rewrite (interp_unique G2 SG2 HB2 Hobj2 Hgen2 m n t).
  now rewrite !hom_cast_roundtrip.
Qed.

End Universal.

Arguments InterpF S P {HP OD} v : assert.
Arguments SymmetricStrict S P G MG : assert.
