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
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.PROP.Presentation.

From Coq Require Import Arith.

Generalizable All Variables.

Open Scope nat_scope.

(* * * Tietze moves for presentations of PROPs / * * Tietze 移动以展示 PROPs *)

(*
 nLab: https://ncatlab.org/nlab/show/generators+and+relations
 nLab: https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/Tietze_transformations
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 Two FINITE presentations of the same group are related by a finite
 sequence of TIETZE TRANSFORMATIONS: adding/removing a derivable
 relation, and adding/removing a definable generator.  The same
 calculus applies to presentations of PROPs by symmetric monoidal
 theories ([SMT], from [Construction/PROP/Presentation.v]), and this
 file develops its two “adding” moves together with the theorems
 that make them presentation-preserving: for move 1 the congruences
 coincide at every arity; for move 2 the embedding is conservative
 AND a section up to derivable equality, which pins the presented
 homs on both sides (the packaging as an equivalence of presented
 PROPs is deferred; see the trailer):

 1.  SIGNATURE MORPHISMS ([T_map]): a [SubSig S T] acts on terms by
 structural recursion, giving a functor [RelabelFunctor : FreeCat S ⟶
 FreeCat T] that is strict symmetric monoidal — signature
 morphisms induce strict symmetric maps of free PROPs (no
 injectivity of [h] is assumed or used: arbitrary
 boundary-preserving relabellings, including generator
 collapses, are covered).  Unlike
 the tactic-built [T_inj] of [Term.v] (left untouched, related by
 the bridge [T_map_T_inj]), [T_map] is a computing [Fixpoint], so
 the functor laws hold by reflexivity.

 2.  SUMS OF SIGNATURES: the copairing of two valuations interprets a
 summand's image under [sig_inl]/[sig_inr] exactly as the summand
 itself ([interp_copair_inl]/[interp_copair_inr]).

 3.  TIETZE MOVE 1 ([AddEqn]): adding an equation DERIVABLE in a
 theory [E] yields a theory with the same congruence — the
 equivalence [AddEqn_derivable_conservative], both directions.

 4.  TIETZE MOVE 2 ([ext_smt]): adjoining a fresh generator [g] of
 arity [(m, n)] together with the defining equation [g ≈ w] for a
 word [w] of the base theory is CONSERVATIVE: base-signature
 terms are identified in the extension exactly when they were
 identified before ([ext_conservative]/[ext_reflects]).  The
 proof is by a syntactic retraction that substitutes [w] for the
 new generator; a semantic route through [interp] and a copaired
 valuation is possible but carries heavier dependencies, so the
 retraction is preferred here.  The retraction is moreover a
 SECTION of the embedding up to derivable equality
 ([ext_retract_section]): every extended-signature term is
 [TermEqW]-equal to an embedded base term, so the extension adds
 no new morphisms, only a new name.

 Everything is elementary syntax: the only quotients involved are the
 [Prop]-valued congruences [TermEq] and [TermEqW], and the only
 proof-irrelevance used is axiom-free UIP on [nat] (via [T_cast_id]
 from [Construction/PROP/Cast.v]). 

 --------
 nLab: https://ncatlab.org/nlab/show/generators+and+relations
 nLab: https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/Tietze_transformations
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 同一个群的两个有限表示由有限序列的TIETZE变换相关联：添加/删除可推导关系，以及添加/删除可定义生成元。相同的演算也适用于通过对称幺半理论（[SMT]，来自[Construction/PROP/Presentation.v]）表示的PROP，而此文件将其两个“添加”操作与使其保持表示的定理一起展开：对于移动1，每个元数上的合同一致；对于移动2，嵌入是保守的，并且在可推导等式下是一个截面，这固定了两边的表示同态（作为PROP表示等价的整体打包推迟讨论；见结尾）。1. 签名态射（[T_map]）：一个 [SubSig S T] 通过结构递归作用于项，给出一个函子 [RelabelFunctor : FreeCat S ⟶ FreeCat T]，该函子是严格对称单体的——签名态射会诱导自由 PROP 的严格对称映射（不假设或使用 [h] 的单射性：覆盖任意保持边界的重新标记，包括生成元的合并）。与战术构建的 [T_inj] 的 [Term.v]（保持不变，通过桥 [T_map_T_inj] 关联）不同，[T_map] 是一个计算 [Fixpoint]，因此函子律通过自反性成立。

 2. 签名的和：两个赋值的协对解释了求和项在 [sig_inl] / [sig_inr] 下的像，正好如同求和项本身（[interp_copair_inl] / [interp_copair_inr]）。3. TIETZE 移动 1（[AddEqn]）：在理论 [E] 中添加一个可导出的方程，得到一个具有相同同余的理论——等价 [AddEqn_derivable_conservative]，两个方向。4. TIETZE 移动 2（[ext_smt]）：在基理论中，向外延中添加一个新的算子 [g]，其元数为 [(m, n)]，并加上定义方程 [g ≈ w] 对于某个词 [w] 是保守的：基符号的项在扩展中恰好在它们之前被识别时才被识别（[ext_conservative] / [ext_reflects]）。证明方法是通过语法收缩，将 [w] 替换为新生成元；虽可通过 [interp] 和共配值的语义路线实现，但依赖性更重，因此这里优先采用收缩法。此外，收缩是嵌入的一部分，直到可推导相等 ([ext_retract_section])：每一个扩展签名项都与一个嵌入的基础项 [TermEqW] 相等，因此扩展不会增加新的态射，只是增加了一个新名称。

 一切都是基本语法：涉及的唯一商是 [Prop] 值的合同 [TermEq] 和 [TermEqW]，唯一使用的证明无关性是在 [nat] 上的无公理 UIP（通过 [T_cast_id] 从 [Construction/PROP/Cast.v] 得到）。
*)

(*
   * ** Signature morphisms acting on terms

   [T_map h] relabels every generator leaf through [h] and leaves the
   structural constructors untouched — the [T_subst] instance of
   [Construction/PROP/TermEq.v] whose generator action is [T_gen]
   after [h].  It COMPUTES on constructors — e.g. [T_map h (T_comp g
   f)] is definitionally [T_comp (T_map h g) (T_map h f)] — which the
   functor and monoidal-functor packaging below exploits:
   identity/composition preservation are [TE_refl]. 

   --------
   * ** 作用于项的签名态射

   [T_map h] 通过 [h] 重新标记每个生成器叶子，并保持结构构造器不变——[T_subst] 是 [Construction/PROP/TermEq.v] 的一个实例，其生成器作用在 [h] 之后为 [T_gen]。它在构造器上进行计算——例如 [T_map h (T_comp g f)] 定义上为 [T_comp (T_map h g) (T_map h f)]——下面的函子和单体函子封装利用了这一点：身份/复合保持性为 [TE_refl]。
*)

Definition T_map {S T : Signature} (h : SubSig S T) {m n : nat}
  (t : Term S m n) : Term T m n :=
  T_subst (fun a b (s : S a b) => T_gen (h a b s)) t.

(*
   * The instantiation is definitional, so every [T_subst]-level lemma
   specializes to [T_map] by conversion. 

   --------
   * 实例化是定义性的，因此每个 [T_subst] 级别的引理都通过转换特化为 [T_map]。
*)
Example T_map_is_T_subst {S T : Signature} (h : SubSig S T) {m n : nat} :
  @T_map S T h m n
  = @T_subst S T (fun a b (s : S a b) => T_gen (h a b s)) m n := eq_refl.

(*
   * [T_map] agrees with the tactic-built [T_inj] of [Term.v] on the
   nose; [T_inj] itself is left untouched. 

   --------
   * [T_map] 同意由 [Term.v] 构建战术的 [T_inj]；[T_inj] 本身保持不变。
*)
Lemma T_map_T_inj {S T : Signature} (h : SubSig S T) {m n : nat}
  (t : Term S m n) :
  T_map h t = T_inj h t.
Proof.
  induction t; cbn; try reflexivity; now f_equal.
Qed.

(*
   * Casts are fixed by every signature morphism (a Leibniz equality:
   both sides are the same [match] once [e] is destructed). 

   --------
   * 每个签名态射都会固定类型转换（一个莱布尼茨等式：一旦  [e] 被解构，两边都是相同的 [match]）。
*)
Lemma T_map_T_cast {S T : Signature} (h : SubSig S T) {a b : nat}
  (e : a = b) :
  T_map h (T_cast e) = T_cast e.
Proof. destruct e; reflexivity. Qed.

(*
   * *** Soundness of relabelling

   [T_map h] carries every free equation of [TermEq S] to the
   corresponding free equation of [TermEq T] — the nineteen-case
   preservation induction [T_subst_TermEq] of
   [Construction/PROP/TermEq.v], specialized (definitionally) to the
   relabelling substitution. 

   --------
   * *** 重标记的健全性

   [T_map h] 将 [TermEq S] 的每个自由方程映射到 [TermEq T] 的对应自由方程——十九种情况的保持归纳 [T_subst_TermEq] 的 [Construction/PROP/TermEq.v]，定义上专门针对重标记替换。
*)

Lemma T_map_TermEq {S T : Signature} (h : SubSig S T) {m n : nat}
  {s t : Term S m n} :
  TermEq S s t → TermEq T (T_map h s) (T_map h t).
Proof.
  exact (T_subst_TermEq (fun a b (g : S a b) => T_gen (h a b g))).
Qed.

(*
   * ** The induced functor of free PROPs

   A signature morphism [h : SubSig S T] induces [RelabelFunctor h :
   FreeCat S ⟶ FreeCat T] — identity on objects (arities), [T_map h]
   on morphisms — and the functor is STRICT SYMMETRIC monoidal: both
   comparison maps are identities on the nose, the object equalities
   are [eq_refl], and the braid square commutes because [T_map] fixes
   [T_braid].  This is the “signature morphisms induce strict
   symmetric maps of free PROPs” half of the Tietze calculus; the
   packaging mirrors the projection functor of [Presentation.v], and
   both discharge their coherence squares with the shared
   identity-bookkeeping lemmas [tm_id_swap] / [tm_comp_id_tens] /
   [tm_collapse_r] / [tm_collapse_l] of
   [Construction/PROP/TermEq.v]. 

   --------
   * ** 自由PROPs的诱导函子

   一个符号态射 [h : SubSig S T] 诱导了 [RelabelFunctor h :
   FreeCat S ⟶ FreeCat T] — 在对象（元数）上是恒等映射，[T_map h] 
   在态射上 — 并且该函子是严格对称单体的：两者的比较映射在本质上都是恒等，
   对象等式是 [eq_refl]，编织图正方形可交换，因为 [T_map] 固定了
   [T_braid]。这是“符号态射诱导自由PROPs的严格对称映射”的 Tietze 演算的一半；
   其封装方式反映了 [Presentation.v] 的投影函子，并且它们都通过共享的
   恒等记账引理 [tm_id_swap] / [tm_comp_id_tens] / [tm_collapse_r] / [tm_collapse_l] 减轻了其相干方形
   的复杂性，来自于 [Construction/PROP/TermEq.v]。
*)

Section SignatureMorphism.

Context {S T : Signature}.
Context (h : SubSig S T).

Definition RelabelFunctor : FreeCat S ⟶ FreeCat T :=
  Build_Functor (FreeCat S) (FreeCat T)
    (fun n : nat => n)
    (fun m n (t : Term S m n) => T_map h t)
    (fun m n s t Hst => T_map_TermEq h Hst)
    (fun x => TE_refl (T_id x))
    (fun x y z f g => TE_refl (T_comp (T_map h f) (T_map h g))).

(*
   * The tensor-then-map and map-then-tensor composites related by the
   tensor comparison of the monoidal structure. 

   --------
   * 与单体结构的张量比较相关的张量-然后映射和映射-然后张量复合。
*)
Definition Relabel_ap_dom : FreeCat S ∏ FreeCat S ⟶ FreeCat T :=
  FreeCat_Tensor T ◯ (RelabelFunctor ∏⟶ RelabelFunctor).

Definition Relabel_ap_cod : FreeCat S ∏ FreeCat S ⟶ FreeCat T :=
  RelabelFunctor ◯ FreeCat_Tensor S.

(*
   * Both directions of the tensor comparison are families of
   identities — [T_map] computes through [T_tens], so the two functors
   have definitionally equal actions — and naturality is
   [tm_id_swap]. 

   --------
   * 张量比较的两个方向都是恒等式的族 —— [T_map] 通过 [T_tens] 进行计算，所以两个函子在定义上具有相等的作用 —— 并且自然性是 [tm_id_swap] 。
*)
Definition Relabel_ap_to : Relabel_ap_dom ⟹ Relabel_ap_cod :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) (FreeCat T)
    Relabel_ap_dom Relabel_ap_cod
    (fun p => T_id (fst p + snd p))
    (fun p q f => tm_id_swap (T_tens (T_map h (fst f)) (T_map h (snd f)))).

Definition Relabel_ap_from : Relabel_ap_cod ⟹ Relabel_ap_dom :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) (FreeCat T)
    Relabel_ap_cod Relabel_ap_dom
    (fun p => T_id (fst p + snd p))
    (fun p q f => tm_id_swap (T_tens (T_map h (fst f)) (T_map h (snd f)))).

(*
   * The identity components are inverse up to [TermEq] (the identity
   natural transformation of a composite-with-tensor functor has
   components [T_tens (T_id _) (T_id _)]). 

   --------
   * 恒等分量是 ZZ W0WZZ 下的逆（复合张量函子 的恒等自然变换具有分量 ZZ W1WZZ）。
*)
Program Definition Relabel_ap_iso :
  Relabel_ap_dom ≅[[FreeCat S ∏ FreeCat S, FreeCat T]] Relabel_ap_cod := {|
  to   := Relabel_ap_to;
  from := Relabel_ap_from;
  iso_to_from := fun p => tm_comp_id_tens (fst p) (snd p);
  iso_from_to := fun p => tm_comp_id_tens (fst p) (snd p)
|}.

(*
   * *** The coherence squares

   Each structural map of [FreeCat_Monoidal] is a [T_cast], which
   [T_map] fixes ([T_map_T_cast]); after that rewrite the squares are
   pure identity bookkeeping. 

   --------
   * *** 一致性方块

   [FreeCat_Monoidal] 的每个结构图是一个 [T_cast]，它被 [T_map] 固定（[T_map_T_cast]）；之后重写的方块只是纯粹的身份簿记。
*)

Lemma Relabel_unit_left_square (x : nat) :
  TermEq T (T_cast (Nat.add_0_l x))
    (T_comp (T_comp (T_map h (T_cast (Nat.add_0_l x))) (T_id (0 + x)))
            (T_tens (T_id 0) (T_id x))).
Proof.
  rewrite (T_map_T_cast h (Nat.add_0_l x)).
  apply TE_sym, tm_collapse_r.
Qed.

Lemma Relabel_unit_right_square (x : nat) :
  TermEq T (T_cast (Nat.add_0_r x))
    (T_comp (T_comp (T_map h (T_cast (Nat.add_0_r x))) (T_id (x + 0)))
            (T_tens (T_id x) (T_id 0))).
Proof.
  rewrite (T_map_T_cast h (Nat.add_0_r x)).
  apply TE_sym, tm_collapse_r.
Qed.

Lemma Relabel_assoc_square (x y z : nat) :
  TermEq T
    (T_comp (T_comp (T_map h (T_cast (eq_sym (Nat.add_assoc x y z))))
                    (T_id ((x + y) + z)))
            (T_tens (T_id (x + y)) (T_id z)))
    (T_comp (T_comp (T_id (x + (y + z)))
                    (T_tens (T_id x) (T_id (y + z))))
            (T_cast (eq_sym (Nat.add_assoc x y z)))).
Proof.
  rewrite (T_map_T_cast h (eq_sym (Nat.add_assoc x y z))).
  apply TE_trans with (T_cast (eq_sym (Nat.add_assoc x y z))).
  - apply tm_collapse_r.
  - apply TE_sym, tm_collapse_l.
Qed.

Program Definition RelabelFunctor_Monoidal :
  @MonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Monoidal S) (FreeCat_Monoidal T) RelabelFunctor := {|
  pure_iso := iso_id;
  ap_functor_iso := Relabel_ap_iso;
  pure_iso_left  := fun x => iso_id;
  pure_iso_right := fun x => iso_id;
  ap_iso_assoc := fun x y z =>
    @tensor_assoc (FreeCat T) (FreeCat_Monoidal T) x y z;
  monoidal_unit_left  := fun x => Relabel_unit_left_square x;
  monoidal_unit_right := fun x => Relabel_unit_right_square x;
  monoidal_assoc := fun x y z => Relabel_assoc_square x y z
|}.

(*
   * Both comparison maps are identities on the nose, so the functor is
   STRICT monoidal with [eq_refl] object equalities.  As with
   [Presentation.v]'s projection, the two comparison fields are
   discharged in situ, keeping the record at a single universe
   instance. 

   --------
   * 两个比较映射在本质上都是恒等映射，因此这个函子是严格单的，其对象等式为 [eq_refl]。与 [Presentation.v] 的投影类似，这两个比较域在原位解决，使得记录保持在单一宇宙实例中。
*)
Program Definition RelabelFunctor_Strict :
  @StrictMonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Monoidal S) (FreeCat_Monoidal T) RelabelFunctor := {|
  strict_functor_is_monoidal := RelabelFunctor_Monoidal;
  strict_pure_obj := eq_refl;
  strict_ap_obj := fun x y => eq_refl
|}.
Next Obligation. exact (TE_refl _). Qed.
Next Obligation. exact (TE_refl _). Qed.

(*
   * The braid-compatibility square: [T_map] fixes [T_braid], and both
   tensor comparisons are identities, so the square is one slide of an
   identity past the braid. 

   --------
   * 辫子兼容方格：[T_map] 固定 [T_braid]，且两个张量比较都是恒等变换，因此该方格就是恒等变换绕过辫子的一次滑动。
*)
Lemma RelabelFunctor_braid (m n : nat) :
  fmap[RelabelFunctor] (@braid (FreeCat S) (FreeCat_Braided S) m n)
    ∘ to (@ap_iso _ _ _ _ RelabelFunctor RelabelFunctor_Monoidal m n)
  ≈[FreeCat T]
  to (@ap_iso _ _ _ _ RelabelFunctor RelabelFunctor_Monoidal n m)
    ∘ @braid (FreeCat T) (FreeCat_Braided T) m n.
Proof.
  exact (tm_id_swap (T_braid m n)).
Qed.

Program Definition RelabelFunctor_Braided :
  @BraidedMonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Braided S) (FreeCat_Braided T) RelabelFunctor := {|
  braided_is_strong := RelabelFunctor_Monoidal
|}.
Next Obligation.
  exact (tm_id_swap (T_braid x y)).
Qed.

(*
   * A braided monoidal functor between symmetric monoidal categories IS
   a symmetric monoidal functor ([SymmetricMonoidalFunctor] is a
   definition, not a class); supplied explicitly, as the alias does
   not participate in instance resolution. 

   --------
   * 对称幺半范畴之间的编织幺半函子就是一个对称幺半函子（[SymmetricMonoidalFunctor] 是一个定义，不是一个类）；需显式提供，因为该别名不参与实例解析。
*)
Definition RelabelFunctor_Symmetric :
  @SymmetricMonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Symmetric S) (FreeCat_Symmetric T) RelabelFunctor :=
  RelabelFunctor_Braided.

End SignatureMorphism.

Arguments RelabelFunctor {S T} h : assert.
Arguments RelabelFunctor_Monoidal {S T} h : assert.
Arguments RelabelFunctor_Strict {S T} h : assert.
Arguments RelabelFunctor_Braided {S T} h : assert.
Arguments RelabelFunctor_Symmetric {S T} h : assert.

(*
   * ** Sums of signatures and copaired valuations

   The coproduct injections of [Sum_Sig], and the copairing of two
   valuations, satisfying the expected computation rules under
   [interp]: interpreting the [T_map]-image of a summand's term
   through the copaired valuation is interpreting the term through the
   summand's own valuation. 

   --------
   * ** 签名和共成对值的和

   [Sum_Sig] 的余积注入，以及两个值的共成对，
   满足在 [interp] 下的预期计算规则：通过共成对值解释一个子项的 [T_map] 映像，就是通过该子项自身的值来解释该项。
*)

Definition sig_inl {S T : Signature} : SubSig S (Sum_Sig S T) :=
  fun _ _ s => Datatypes.inl s.

Definition sig_inr {S T : Signature} : SubSig T (Sum_Sig S T) :=
  fun _ _ t => Datatypes.inr t.

Definition copair_val {S T : Signature} {P : PROP}
  (v : Valuation P S) (w : Valuation P T) : Valuation P (Sum_Sig S T) :=
  fun m n g =>
    match g with
    | Datatypes.inl s => v m n s
    | Datatypes.inr t => w m n t
    end.

(*
   * No decidability or reflection hypotheses are needed here: the
   induction never leaves the [Type]-valued hom equivalence. 

   --------
   * 这里不需要可判定性或反射假设：归纳从未离开 [Type] 值的同态等价。
*)
Lemma interp_copair_inl {S T : Signature} {P : PROP}
  (v : Valuation P S) (w : Valuation P T) {m n : nat} (t : Term S m n) :
  interp P (Sum_Sig S T) (copair_val v w) (T_map sig_inl t)
    ≈ interp P S v t.
Proof.
  induction t; cbn [T_map T_subst interp].
  - reflexivity.
  - reflexivity.
  - rewrite <- IHt1, <- IHt2; reflexivity.
  - rewrite <- IHt1, <- IHt2; reflexivity.
  - reflexivity.
Qed.

Lemma interp_copair_inr {S T : Signature} {P : PROP}
  (v : Valuation P S) (w : Valuation P T) {m n : nat} (t : Term T m n) :
  interp P (Sum_Sig S T) (copair_val v w) (T_map sig_inr t)
    ≈ interp P T w t.
Proof.
  induction t; cbn [T_map T_subst interp].
  - reflexivity.
  - reflexivity.
  - rewrite <- IHt1, <- IHt2; reflexivity.
  - rewrite <- IHt1, <- IHt2; reflexivity.
  - reflexivity.
Qed.

(*
   * ** Tietze move 1: adding a derivable equation

   Extending a theory [E] by ONE new equation [s ≈ t] between terms of
   a fixed arity.  The extended equation system is the two-constructor
   inductive below — an axiom of [E], or the new equation — which
   keeps the arity indices pinned by the constructor itself, so no
   transports (and no UIP) are needed anywhere in the conservativity
   proof. 

   --------
   * ** Tietze 移动 1：添加可导出方程

   通过在固定元数的项之间增加一个新方程 [s ≈ t] 来扩展理论 [E]。
   扩展的方程系统如下双构造子归纳 —— [E] 的公理，或新方程 —— 它保持由构造子本身固定的元数索引，因此在保守性证明中不需要任何传递（也不需要 UIP）。
*)

Section AddEquation.

Context (E : SMT).
Context {m n : nat}.
Context (s t : Term (smt_sig E) m n).

Inductive add_eqn : ∀ a b : nat,
  Term (smt_sig E) a b → Term (smt_sig E) a b → Prop :=
  | ae_base {a b} (u u' : Term (smt_sig E) a b) :
      smt_eqs E a b u u' → add_eqn a b u u'
  | ae_new : add_eqn m n s t.

Definition AddEqn : SMT := {|
  smt_sig := smt_sig E;
  smt_eqs := add_eqn
|}.

(*
   * Adding a DERIVABLE equation changes nothing: the congruence of the
   extended theory coincides with the congruence of [E].  Forward
   direction by induction — the new axiom's case is exactly the
   derivation [Hd] — and backward direction by axiom-inclusion
   monotonicity. 

   --------
   * 添加一个可导出的方程不会改变任何内容：扩展理论的合同与  [E]  的合同一致。正向通过归纳——新公理的情况正好是推导  [Hd] ——反向通过公理包含单调性。
*)
Theorem AddEqn_derivable_conservative (Hd : TermEqW E s t) :
  ∀ (a b : nat) (u u' : Term (smt_sig E) a b),
    TermEqW AddEqn u u' <-> TermEqW E u u'.
Proof.
  intros a b u u'.
  split; intros H.
  - induction H as [a1 b1 u1 u2 Hfree
                   |a1 b1 u1 u2 Hax
                   |a1 b1 u1 u2 Hw IHw
                   |a1 b1 u1 u2 u3 Hw1 IHw1 Hw2 IHw2
                   |a1 b1 c1 f1 f2 g1 g2 Hf IHf Hg IHg
                   |a1 b1 c1 d1 f1 f2 g1 g2 Hf IHf Hg IHg].
    + apply TEW_termeq; exact Hfree.
    + destruct Hax as [a2 b2 u3 u4 Hax'|].
      * apply TEW_ax; exact Hax'.
      * exact Hd.
    + apply TEW_sym; exact IHw.
    + exact (TEW_trans _ _ _ _ IHw1 IHw2).
    + exact (TEW_comp E _ _ _ _ IHf IHg).
    + exact (TEW_tens E _ _ _ _ IHf IHg).
  - induction H as [a1 b1 u1 u2 Hfree
                   |a1 b1 u1 u2 Hax
                   |a1 b1 u1 u2 Hw IHw
                   |a1 b1 u1 u2 u3 Hw1 IHw1 Hw2 IHw2
                   |a1 b1 c1 f1 f2 g1 g2 Hf IHf Hg IHg
                   |a1 b1 c1 d1 f1 f2 g1 g2 Hf IHf Hg IHg].
    + apply TEW_termeq; exact Hfree.
    + apply TEW_ax, ae_base; exact Hax.
    + apply TEW_sym; exact IHw.
    + exact (TEW_trans _ _ _ _ IHw1 IHw2).
    + exact (TEW_comp AddEqn _ _ _ _ IHf IHg).
    + exact (TEW_tens AddEqn _ _ _ _ IHf IHg).
Qed.

End AddEquation.

Arguments AddEqn E {m n} s t : assert.

(*
   * ** Tietze move 2: definitional extension

   Adjoining to a theory [B] a FRESH generator of arity [(m, n)]
   together with the single defining equation identifying it with a
   word [w] of the base signature.  The extension is conservative:
   the retraction substituting [w] back for the new generator carries
   every derivation of the extended theory to a derivation of [B]. 

   --------
   * ** Tietze 移动 2：定义性扩展

   向理论 [B] 添加一个新的生成元，其元数为 [(m, n)]，同时附加唯一的定义方程，将其与基础符号的一个词 [w] 识别。此扩展是保守的：通过将 [w] 重新替换回新生成元的折回操作，可将扩展理论的每一个演绎转换为 [B] 的演绎。
*)

Section Extension.

Context (B : SMT).
Context (m n : nat).
Context (w : Term (smt_sig B) m n).

(** The extended signature: the base plus one generator. / 扩展签名：基数加一个生成元。 *)
Definition ext_sig : Signature := Sum_Sig (smt_sig B) (Single_Sig m n).

(*
   * Computing witnesses for the [Nat.eqb] equations of the singleton
   signature.  The standard library's [Nat.eqb_refl] and [Nat.eqb_eq]
   are Qed-opaque, so anything built on them is stuck at closed
   arities; these transparent fixpoints restore reduction. 

   --------
   * 为单元素签名的  [Nat.eqb]  方程计算证人。标准库的  [Nat.eqb_refl]  和  [Nat.eqb_eq]  是 Qed-opaque 的，因此基于它们构建的任何东西都被限制在封闭的元数上；这些透明的不动点恢复了规约。
*)

Fixpoint nat_eqb_refl (x : nat) : Nat.eqb x x = true :=
  match x return Nat.eqb x x = true with
  | O => eq_refl
  | Datatypes.S k => nat_eqb_refl k
  end.

Fixpoint nat_eqb_eq (a b : nat) {struct a} : Nat.eqb a b = true → a = b :=
  match a, b return Nat.eqb a b = true → a = b with
  | O, O => fun _ => eq_refl
  | O, Datatypes.S b' => fun H =>
      match H in _ = c return if c then O = Datatypes.S b' else True with
      | eq_refl => Logic.I
      end
  | Datatypes.S a', O => fun H =>
      match H in _ = c return if c then Datatypes.S a' = O else True with
      | eq_refl => Logic.I
      end
  | Datatypes.S a', Datatypes.S b' => fun H =>
      f_equal Datatypes.S (nat_eqb_eq a' b' H)
  end.

(*
   * The unique generator of [Single_Sig m n], with its arity
   equations.  All three definitions are TRANSPARENT and built on the
   computing witnesses above, so they reduce at closed arities
   ([single_gen] to [tt], the arity equations to [eq_refl]) and
   [ext_retract] computes on concrete definitional extensions — see
   [ext_retract_computes_on_new_gen] at the end of the file.  The
   conservativity proofs below remain transparency-indifferent: they
   consume the arity equations only through UIP on [nat]
   ([T_cast_id]). 

   --------
   * [Single_Sig m n] 的唯一生成器及其元数方程。三个定义都是透明的，并且都是建立在上述计算见证之上的，因此它们在封闭元数下会简化（[single_gen] 到 [tt]，元数方程到 [eq_refl]），并且 [ext_retract] 会在具体定义扩展上进行计算 —— 见文件末尾的 [ext_retract_computes_on_new_gen]。下面的保守性证明对透明性不敏感：它们仅通过 [nat] ([T_cast_id]) 上的 UIP 来使用元数方程。
*)
Definition single_gen : Single_Sig m n m n :=
  match eq_sym (nat_eqb_refl m) in _ = c
    return (if c then if Nat.eqb n n then unit else Empty_set
            else Empty_set)
  with
  | eq_refl =>
      match eq_sym (nat_eqb_refl n) in _ = d
        return (if d then unit else Empty_set)
      with
      | eq_refl => tt
      end
  end.

Definition single_dom {a b : nat} : Single_Sig m n a b → a = m :=
  match Nat.eqb a m as c
    return (Nat.eqb a m = c →
            (if c then if Nat.eqb b n then unit else Empty_set
             else Empty_set) → a = m)
  with
  | true  => fun Ha _ => nat_eqb_eq a m Ha
  | false => fun _ s => match s return a = m with end
  end eq_refl.

Definition single_cod {a b : nat} : Single_Sig m n a b → b = n :=
  match Nat.eqb a m as c
    return ((if c then if Nat.eqb b n then unit else Empty_set
             else Empty_set) → b = n)
  with
  | true =>
      match Nat.eqb b n as d
        return (Nat.eqb b n = d → (if d then unit else Empty_set) → b = n)
      with
      | true  => fun Hb _ => nat_eqb_eq b n Hb
      | false => fun _ s => match s return b = n with end
      end eq_refl
  | false => fun s => match s return b = n with end
  end.

(*
   * [Single_Sig m n] is a SINGLETON: any two generators of any one
   arity are equal.  This identifies a generator of the extended
   signature with [single_gen] in the section lemma below. 

   --------
   * [Single_Sig m n] 是一个单例：任意一个元的任意两个生成元都是相等的。这将在下面的引理部分将扩展签名的生成元与 [single_gen] 识别。
*)
Lemma single_sig_singleton {a b : nat} (s s' : Single_Sig m n a b) :
  s = s'.
Proof.
  revert s s'.
  unfold Single_Sig.
  destruct (Nat.eqb a m), (Nat.eqb b n); intros s s'; now destruct s, s'.
Qed.

(*
   * The fresh generator, as a generator of the extended signature. 

   --------
   * 新生成器，作为扩展签名的生成器。
*)
Definition new_gen : ext_sig m n := Datatypes.inr single_gen.

(*
   * The equations of the extended theory: the base axioms (embedded
   along [sig_inl]) plus the single defining equation. 

   --------
   * 扩展理论的方程：基元公理（沿 [sig_inl] 嵌入）加上单一的定义方程。
*)
Inductive ext_eqs : ∀ a b : nat,
  Term ext_sig a b → Term ext_sig a b → Prop :=
  | ee_base {a b} (s t : Term (smt_sig B) a b) :
      smt_eqs B a b s t →
      ext_eqs a b (T_map sig_inl s) (T_map sig_inl t)
  | ee_def : ext_eqs m n (T_gen new_gen) (T_map sig_inl w).

Definition ext_smt : SMT := {|
  smt_sig := ext_sig;
  smt_eqs := ext_eqs
|}.

(*
   * *** The syntactic retraction

   Substitute [w] for the new generator, conjugated by the arity
   casts that reconcile the generator's typed arity [(a, b)] with the
   pinned [(m, n)]; base generators go back to themselves. 

   --------
   * *** 句法收缩

   用[w]替代新的生成器，并通过调和生成器的类型元数[(a, b)]与固定[(m, n)]的元数的元数转换进行结合；基础生成器回到它们自身。
*)

Definition ext_retract_gen {a b : nat} (g : ext_sig a b) :
  Term (smt_sig B) a b :=
  match g with
  | Datatypes.inl s => T_gen s
  | Datatypes.inr s => T_comp (T_cast (eq_sym (single_cod s)))
                              (T_comp w (T_cast (single_dom s)))
  end.

Definition ext_retract {a b : nat} (t : Term ext_sig a b) :
  Term (smt_sig B) a b :=
  T_subst (@ext_retract_gen) t.

(*
   * The instantiation is definitional, so every [T_subst]-level lemma
   specializes to [ext_retract] by conversion. 

   --------
   * 实例化是定义性的，因此每个 [T_subst] 级别的引理都通过转换特化为 [ext_retract]。
*)
Example ext_retract_is_T_subst {a b : nat} :
  @ext_retract a b
  = @T_subst ext_sig (smt_sig B) (@ext_retract_gen) a b := eq_refl.

(*
   * [ext_retract] fixes casts, just as [T_map] does. 

   --------
   * [ext_retract] 修复了投掷，就像 [T_map] 一样。
*)
Lemma retract_T_cast {a b : nat} (e : a = b) :
  ext_retract (T_cast e) = T_cast e.
Proof. destruct e; reflexivity. Qed.

(*
   * The retraction is a left inverse of the embedding — a Leibniz
   equality, by term induction. 

   --------
   * 收回是嵌入的左逆——通过项归纳，它是莱布尼茨等式。
*)
Lemma retract_map_inl {a b : nat} (t : Term (smt_sig B) a b) :
  ext_retract (T_map sig_inl t) = t.
Proof.
  induction t;
  cbn [T_map ext_retract T_subst ext_retract_gen sig_inl];
  try reflexivity.
  - now f_equal.
  - now f_equal.
Qed.

(*
   * The retraction carries free equations to free equations — the
   nineteen-case preservation induction [T_subst_TermEq] of
   [Construction/PROP/TermEq.v], specialized (definitionally) to the
   retraction substitution. 

   --------
   * 这一回退将自由方程映射到自由方程——
   十九种情况的保留归纳 [T_subst_TermEq] 
   对 [Construction/PROP/TermEq.v] 的回退代换进行了特化（按定义）。
*)
Lemma retract_TermEq {a b : nat} {s t : Term ext_sig a b} :
  TermEq ext_sig s t → TermEq (smt_sig B) (ext_retract s) (ext_retract t).
Proof.
  exact (T_subst_TermEq (@ext_retract_gen)).
Qed.

(*
   * The retraction is sound for the whole extended theory: base axioms
   retract to themselves ([retract_map_inl]), and the defining
   equation retracts to the identity bookkeeping [cast ⊙ (w ⊙ cast) ≈
   w], where both casts are along loop equations on [nat] and vanish
   by [T_cast_id] (axiom-free UIP). 

   --------
   * 对整个扩展理论来说，收缩是合理的：基础公理收缩到自身（[retract_map_inl]），定义方程收缩到恒等账簿记录 [cast ⊙ (w ⊙ cast) ≈ w]，其中两个 cast 都沿着 [nat] 上的循环方程进行，并且根据 [T_cast_id]（无公理的 UIP）消失。
*)
Lemma retract_sound {a b : nat} {s t : Term ext_sig a b} :
  TermEqW ext_smt s t → TermEqW B (ext_retract s) (ext_retract t).
Proof.
  intros H.
  induction H as [a1 b1 u1 u2 Hfree
                 |a1 b1 u1 u2 Hax
                 |a1 b1 u1 u2 Hw IHw
                 |a1 b1 u1 u2 u3 Hw1 IHw1 Hw2 IHw2
                 |a1 b1 c1 f1 f2 g1 g2 Hf IHf Hg IHg
                 |a1 b1 c1 d1 f1 f2 g1 g2 Hf IHf Hg IHg].
  - apply TEW_termeq, retract_TermEq; exact Hfree.
  - destruct Hax as [a2 b2 u3 u4 Hax'|].
    + rewrite !retract_map_inl.
      apply TEW_ax; exact Hax'.
    + rewrite retract_map_inl.
      cbn [ext_retract T_subst ext_retract_gen new_gen].
      rewrite (T_cast_id (single_dom single_gen)).
      rewrite (T_cast_id (eq_sym (single_cod single_gen))).
      apply TEW_termeq.
      apply TE_trans with (T_comp w (T_id m)).
      * apply TE_id_left.
      * apply TE_id_right.
  - apply TEW_sym; exact IHw.
  - exact (TEW_trans _ _ _ _ IHw1 IHw2).
  - cbn [ext_retract T_subst]; apply TEW_comp; assumption.
  - cbn [ext_retract T_subst]; apply TEW_tens; assumption.
Qed.

(* * *** Conservativity, both directions / * *** 保守性，双向 *)

(*
   * Base-signature terms identified in the extension were already
   identified in the base theory. 

   --------
   * 扩展中识别的基本符号术语已在基础理论中识别。
*)
Theorem ext_conservative {a b : nat} (s t : Term (smt_sig B) a b) :
  TermEqW ext_smt (T_map sig_inl s) (T_map sig_inl t) →
  TermEqW B s t.
Proof.
  intros H.
  pose proof (retract_sound H) as Hr.
  rewrite !retract_map_inl in Hr.
  exact Hr.
Qed.

(*
   * Conversely, every base identification survives the extension. 

   --------
   * 相反，每个基识别都会在扩展中保留。
*)
Theorem ext_reflects {a b : nat} {s t : Term (smt_sig B) a b} :
  TermEqW B s t →
  TermEqW ext_smt (T_map sig_inl s) (T_map sig_inl t).
Proof.
  intros H.
  induction H as [a1 b1 u1 u2 Hfree
                 |a1 b1 u1 u2 Hax
                 |a1 b1 u1 u2 Hw IHw
                 |a1 b1 u1 u2 u3 Hw1 IHw1 Hw2 IHw2
                 |a1 b1 c1 f1 f2 g1 g2 Hf IHf Hg IHg
                 |a1 b1 c1 d1 f1 f2 g1 g2 Hf IHf Hg IHg].
  - apply TEW_termeq, T_map_TermEq; exact Hfree.
  - apply TEW_ax, ee_base; exact Hax.
  - apply TEW_sym; exact IHw.
  - exact (TEW_trans _ _ _ _ IHw1 IHw2).
  - cbn [T_map T_subst]; apply TEW_comp; assumption.
  - cbn [T_map T_subst]; apply TEW_tens; assumption.
Qed.

(*
   * The fullness (“section”) leg: EVERY term of the extended
   signature is [TermEqW ext_smt]-equal to the embedding of its own
   retraction — the embedded base theory is not merely conservative
   but exhaustive.  Together with [ext_conservative]/[ext_reflects]
   this is the hom-level content of an equivalence between the base
   and extended presentations; the [PresEquiv] packaging is deferred
   (see the trailer).  By term induction: structural constructors are
   congruences, base generators are fixed, and the fresh generator is
   exactly the defining equation [ee_def] once [single_sig_singleton]
   pins it to [single_gen] and UIP on [nat] ([T_cast_id]) clears the
   arity casts. 

   --------
   * 完整性（“部分”）部分：扩展签名的每一个项都是 [TermEqW ext_smt]——等于其自身收缩的嵌入——嵌入的基础理论不仅是保守的，而且是详尽的。结合 [ext_conservative] / [ext_reflects]，这构成了基础表示与扩展表示之间等价的同类水平内容；[PresEquiv] 的封装被推迟（见尾声）。通过项归纳：结构构造器是合同的，基础生成元是固定的，而新的生成元正是定义方程 [ee_def]，一旦 [single_sig_singleton] 将其固定到 [single_gen] 上，并且 [nat] 上的 UIP（[T_cast_id]）清除了元数的类型转换。
*)
Lemma ext_retract_section {a b : nat} (t : Term ext_sig a b) :
  TermEqW ext_smt t (T_map sig_inl (ext_retract t)).
Proof.
  induction t.
  - (* T_id *)
    apply TEW_termeq, TE_refl.
  - (* T_braid *)
    apply TEW_termeq, TE_refl.
  - (* T_comp *)
    cbn [ext_retract T_subst T_map].
    apply TEW_comp; assumption.
  - (* T_tens *)
    cbn [ext_retract T_subst T_map].
    apply TEW_tens; assumption.
  - (* T_gen *)
    destruct s as [s|s].
    + (* a base generator retracts to itself / 一个基础发电机收回到自身 *)
      apply TEW_termeq, TE_refl.
    + (* the fresh generator: pin the arity, then [ee_def] / 新生成器：先钉住A值，然后再打[ee_def] *)
      pose proof (single_dom s) as ea.
      pose proof (single_cod s) as eb.
      subst.
      cbn [ext_retract T_subst ext_retract_gen].
      rewrite (T_cast_id (single_dom s)).
      rewrite (T_cast_id (eq_sym (single_cod s))).
      rewrite (single_sig_singleton s single_gen).
      apply TEW_trans with (t := T_map sig_inl w).
      * exact (TEW_ax ext_smt _ _ ee_def).
      * apply TEW_termeq, T_map_TermEq.
        apply TE_sym.
        apply TE_trans with (T_comp w (T_id m)).
        -- apply TE_id_left.
        -- apply TE_id_right.
Qed.

(** The defining equation itself holds in the extended theory. / 定义方程本身在扩展理论中成立。 *)
Example ext_definition_holds :
  TermEqW ext_smt (T_gen new_gen) (T_map sig_inl w) :=
  TEW_ax ext_smt _ _ ee_def.

(*
   * The retraction computes on embedded generators, by [eq_refl]. 

   --------
   * 该收缩由 [eq_refl] 在嵌入生成元上计算。
*)
Example retract_fixes_base_gen {a b : nat} (s : smt_sig B a b) :
  ext_retract (T_map sig_inl (T_gen s)) = T_gen s := eq_refl.

End Extension.

Arguments ext_smt B m n w : assert.
Arguments new_gen B m n : assert.

(*
   * ** Machine-checked sanity

   [T_map] computes on the structural constructors, so the functor
   action of [RelabelFunctor] is definitional. 

   --------
   * ** 机器检查的合理性

   [T_map] 在结构构造子上进行计算，因此 [RelabelFunctor] 的函子作用是定义的。
*)

Example T_map_fixes_id {S T : Signature} (h : SubSig S T) (k : nat) :
  T_map h (T_id k) = T_id k := eq_refl.

Example T_map_fixes_braid {S T : Signature} (h : SubSig S T) (a b : nat) :
  T_map h (T_braid a b) = T_braid a b := eq_refl.

Example T_map_computes_comp {S T : Signature} (h : SubSig S T)
  {a b c : nat} (g : Term S b c) (f : Term S a b) :
  T_map h (T_comp g f) = T_comp (T_map h g) (T_map h f) := eq_refl.

Example T_map_computes_tens {S T : Signature} (h : SubSig S T)
  {a b c d : nat} (f : Term S a b) (g : Term S c d) :
  T_map h (T_tens f g) = T_tens (T_map h f) (T_map h g) := eq_refl.

Example RelabelFunctor_obj_id {S T : Signature} (h : SubSig S T) (k : nat) :
  fobj[RelabelFunctor h] k = k := eq_refl.

(*
   * A scratch definitional extension over the empty signature,
   witnessing that [ext_retract] REDUCES at closed arities — the
   transparent [single_gen]/[single_dom]/[single_cod] compute, so
   retracting the fresh generator yields its defining word framed by
   identity casts, by [eq_refl]. 

   --------
   * 在空符号上的一个擦写定义扩展，证明 [ext_retract] 在封闭元数下可以约减 — 透明的 [single_gen] / [single_dom] / [single_cod] 进行计算，因此撤回新的生成器会生成其定义词，并通过恒等类型转换框架，由 [eq_refl] 完成。
*)
Local Definition scratch_smt : SMT :=
  {| smt_sig := Empty_Sig; smt_eqs := fun _ _ _ _ => False |}.

Example ext_retract_computes_on_new_gen :
  ext_retract scratch_smt 1 1 (T_id 1) (T_gen (new_gen scratch_smt 1 1))
  = T_comp (T_id 1) (T_comp (T_id 1) (T_id 1)) := eq_refl.

(*
   * ** Follow-up material (deliberately not started here)

   Two natural continuations of this file are left for a successor:

   - a [TheoryMorphism] record — a [SubSig] between theory signatures
   whose action carries each axiom of the source theory to a
   derivable equation of the target, inducing a functor of
   PRESENTED categories through the quotient's universal property;

   - a [PresEquiv] record packaging a presentation equivalence as a
   pair of theory morphisms whose composites are pointwise
   derivably equal to the identities, with the Tietze moves above
   as its generating instances.

   Both ride only on machinery already present in this file and in
   [Construction/PROP/Presentation.v]. 

   --------
   * ** 后续材料（故意未在此处开始）

   留给继任者的两个自然延续：

   - 一个 [TheoryMorphism] 记录——一个 [SubSig] 记录在理论签名之间，其作用将源理论的每个公理带到目标理论的一个可导出方程，通过商的泛性质诱导 PRESENTED 范畴的函子；

   - 一个 [PresEquiv] 记录，将展示等价打包为一对理论态射，其复合在每一点上可导出地等于恒等映射，上述的 Tietze 变换作为其生成实例。

   两者仅依赖于此文件和 [Construction/PROP/Presentation.v] 中已存在的机制。
*)
