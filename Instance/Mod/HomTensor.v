(* * * Mac Lane V.8 Exercise 2(a): the hom-tensor adjunctions over any ring / * * Mac Lane 第八版 练习 2(a)：任意环上的同构-张量伴随 *)

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd
 ed., §V.8 Exercise 2(a), printed p. 131, PDF p. 140
 (ledger item `maclane:V.8:ex2`, issue #454), read from the
 printed page: “For A a left R-module, B a right R-module
 and G an abelian group, establish adjunctions

 (a) hom_R(A, hom_Z(B, G)) ≅ hom_Z(B ⊗_R A, G)
 ≅ hom_R(B, hom_Z(A, G)),

 where hom_Z(B, G) has a suitable (left or right) R-module
 structure, and where hom_R denotes the hom-set in R-Mod,
 hom_Z that in Ab.”  Here hom_Z(B, G) carries the left
 R-action induced by B's right one and hom_Z(A, G) the right
 R-action induced by A's left one.  Part (b), in
 Instance/Mod/Cogenerator.v, takes B := R.
 Book:      Mac Lane, ibid., §IV.1, printed pp. 79–80 — adjunctions in
 hom-set form, the presentation of Theory/Adjunction.v's
 record, built here through [Build_Adjunction'].
 nLab:      https://ncatlab.org/nlab/show/tensor+product+of+modules
 nLab:      https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem — the
 theorem these exercises serve.

 WHAT IS DELIVERED, strict first.

 - First isomorphism (section [HomTensor], B a right module fixed).
 [HomZL B G : RModObject R] is hom_Z(B, G) with (r · f)(b) :=
 f (b ⊲ r); its group is Adjunction/Additive.v's [hom_ab] at
 [Ab_AbEnriched], nothing rebuilt.  [HomZLF B : Ab ⟶ RMod R] and
 [TensorBF B : RMod R ⟶ Ab] (A ↦ [BalTensor B A]), and
 **[tensor_homZ_adjunction B : TensorBF B ⊣ HomZLF B]**, natural in
 A and G because it is an inhabitant of the [Adjunction] record.
 The transpose computes: [ht_to_at] says ((⌊ψ⌋ a) b) = ψ (b ⊗ a) at
 [eq_refl].
 - Second isomorphism (section [TensorHomRight], A a left module
 fixed): [HomZR A G : RModObject (Ring_op R)] with (f ⊲ r)(a) :=
 f (r · a), [HomZRF A : Ab ⟶ ModR R], [TensorAF A : ModR R ⟶ Ab],
 and **[homZ_tensor_adjunction A : TensorAF A ⊣ HomZRF A]**.
 - The composite, Mac Lane's outer terms: [hom_hom_swap] and the
 [Sets]-isomorphism [hom_hom_swap_iso].  At [eq_refl]
 ([hom_hom_swap_at], [hom_hom_swap_iso_to],
 [hom_hom_swap_iso_from_at]) the swap is literally the exchange of
 the two arguments.  [hom_hom_swap_natural] states its naturality
 in G, up to ≈.
 - Over #449's tensor: the object of [TensorBF_AFT B] at A is the
 [repr_obj] of Instance/Mod/TensorAFT.v's [bal_tensor_via_AFT B A],
 [TensorBF_AFT_iso : TensorBF_AFT ≈ TensorBF B] is assembled from
 that file's [bal_AFT_iso], and **[hom_tensor_adjunction :
 TensorBF_AFT ⊣ HomZLF B]** — the name the issue's Verification
 block prints — is [tensor_homZ_adjunction] carried along it by
 Theory/Adjunction.v's [adjunction_along_left_iso].  Likewise
 [hom_tensor_adjunction_right] for the second leg.  Both transposes
 read back at [eq_refl] through [from (bal_AFT_iso _ _)].
 - B := R (sections [RingUnit] and [RingCoext]): [ring_unit_iso A :
 BalTensor R_R A ≅ rm_ab A] in Ab (R ⊗_R A ≅ A; both components at
 [eq_refl]), [ring_unit_nat : RMod_Forget_Ab R ≈ TensorBF R_R],
 [homzl_ring_adjunction : RMod_Forget_Ab R ⊣ HomZLF R_R], and the
 comparison with Instance/Mod/Coextension.v's [coex_adjunction]:
 the groups agree at [eq_refl] ([homzl_ring_group]), the actions
 pointwise at [eq_refl] ([homzl_ring_act]), the two adjunctions'
 transposes pointwise at [eq_refl]
 ([homzl_ring_adjunction_is_coex_at]), and [homzl_coext_iso] is an
 isomorphism in [RMod R] whose two maps are the identity.

 THE TWO RECORDS ARE NOT IDENTIFIED — a stated fact, measured, not
 pinned here.  [HomZL (Ring_RMod (Ring_op R)) G = CoextObj R G] at
 [eq_refl] is refused, ending “(cannot unify ”HomZL (Ring_RMod (Ring_op
 R)) G“ and ”CoextObj R G“)”.  It is STILL refused in a scratch copy in
 which every [Qed] of this file and of Instance/Mod/Coextension.v (up
 to that file's probe section) was turned into [Defined] under
 [Set Transparent Obligations], so the refusal is not caused by
 opacity in these two files; the [Qed]s of the files they build on
 (Instance/Mod.v, Instance/Ab.v, Instance/Mod/Bimodule.v and others)
 were left opaque, so whether the law fields differ as proofs, rather
 than only through opacity further down, is not measured, and nothing
 here says that they are different proofs.  [homzl_coext_iso]
 with the [eq_refl] components above is the strongest identification
 made at that level of flipping.

 NO COMMUTATIVITY.  Section [HomTensor]'s only [Context] is R and B.
 The module laws of [HomZL] consume B's own laws and nothing of R's
 commutativity: [hzl_act_assoc] is [rm_smul_assoc] of B read through
 [Ring_op].  The R-linearity of the forward transpose is the balance
 relation itself ([be_balance], in [ht_to]); the balance of the
 backward one is [rm_map_smul] of the given map ([ht_bal]).  Neither
 in-tree neighbour hosts G as a bare abelian group:
 Instance/Mod/Closed.v's [HomMod] needs commutativity, and
 Instance/Mod/Bimodule.v's [HomAbBimod] is bimodule-valued.

 UNIVERSES, measured by [About] under [Set Printing Universes].  Each
 section declares [Universes ra rc rp] for [R : RingObject@{ra rc rp}].
 Every universe EQUATION in the constraint blocks of this file's
 constants is one of three kinds, none introduced here: (i) the object
 instance of [RMod R], whose objects are
 [RModObject@{rc ra rc rc rc ra rc rp} R] (for instance A in
 [hom_hom_swap]); (ii) the object instance of [Ab] at hom universe rc,
 [AbObject@{rc rc rc}], which is Instance/Ab.v's hand pin
 ([obj := AbObject@{p p p}]) and is where G lives; (iii) the fixed
 module's group (B in [HomZL], A in [HomZR]) at rc, forced because
 [hom_ab@{u u0}] returns [AbObject@{u u u}] and takes its source in
 [Ab].  So [tensor_homZ_adjunction] reads
 [Adjunction@{u4 rc rc u5 rc rc rc rc u6 rc u7}] with no equation
 among the three ring universes.  [ring_unit_iso] and [ring_unit_nat] stay at
 [RingObject@{ra rc rp}] with no equation.  [homzl_ring_adjunction]
 carries [ra = rc] and [ra = rp]: its right adjoint is [hom_ab] out of
 R's own additive group [ring_ab R : AbObject@{ra rc rp}], which (iii)
 puts at Ab's object instance — the identification [CoextObj] carries
 for the same reason.  Section [RingCoext] therefore fixes
 [R : RingObject@{r r r}].

 NOT DELIVERED.  No naturality in the FIXED module (B for the first
 leg, A for the second): the tensor is not assembled into a bifunctor
 [ModR R ∏ RMod R ⟶ Ab], so Adjunction/Parameter.v's
 [ParametrizedAdjunction] is not instantiated.  The isomorphisms are
 bijections of hom-setoids, not of hom-GROUPS; Adjunction/Additive.v's
 [adj_hom_ab_iso] is not applied to them.  [hom_hom_swap] is stated
 natural in G only ([hom_hom_swap_natural]); naturality in A or B would
 need hom_Z(−, G) as a functor in the module variable, which is not
 built.  No record-level
 identification of [HomZL R_R G] with [CoextObj R G] (above).  No
 comparison with Instance/Mod/Closed.v's [HomMod] over a commutative
 ring. 

 --------
 书籍：      Mac Lane，《为工作中的数学家准备的范畴》，第2版，§V.8 练习 2(a)，印刷页 131，PDF 页 140（账目编号 `maclane:V.8:ex2`，第 454 期），从印刷页阅读：“对于左 R-模 A，右 R-模 B 和阿贝尔群 G，建立下列伴随关系

 (a) hom_R(A, hom_Z(B, G)) ≅ hom_Z(B ⊗_R A, G)
 ≅ hom_R(B, hom_Z(A, G))”其中 hom_Z(B, G) 具有适当的（左或右）R-模结构，且 hom_R 表示 R-Mod 中的同态集合，hom_Z 表示 Ab 中的同态集合。这里 hom_Z(B, G) 携带由 B 的右作用诱导的左 R-作用，而 hom_Z(A, G) 携带由 A 的左作用诱导的右 R-作用。部分 (b)，在 Instance/Mod/Cogenerator.v 中，取 B := R。
 书籍：Mac Lane，同上，第 IV.1 节，印刷页 79–80 — 同态集合形式下的对偶关系，Theory/Adjunction.v 的记录呈现，这里通过 [Build_Adjunction'] 构建。
 nLab: https://ncatlab.org/nlab/show/tensor+product+of+modules
 nLab: https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem — 这些练习所服从的定理。

 首先严格交付。- 第一个同构（章节 [HomTensor]，固定右模 B）。[HomZL B G : RModObject R] 是 hom_Z(B, G)，其定义为 (r · f)(b) := f(b ⊲ r)；其群是 Adjunction/Additive.v 中的 [hom_ab] 在 [Ab_AbEnriched]，未重建任何内容。[HomZLF B : Ab ⟶ RMod R] 和 [TensorBF B : RMod R ⟶ Ab]（A ↦ [BalTensor B A]），以及 **[tensor_homZ_adjunction B : TensorBF B ⊣ HomZLF B]**，在 A 和 G 中是自然的，因为它是 [Adjunction] 记录的一个成员。转置计算为：[ht_to_at] 表示 ((⌊ψ⌋ a) b) = ψ(b ⊗ a) 在 [eq_refl]。- 第二个同构（章节 [TensorHomRight]，固定左模 A）：[HomZR A G : RModObject (Ring_op R)]，(f ⊲ r)(a) := f(r · a)，[HomZRF A : Ab ⟶ ModR R]，[TensorAF A : ModR R ⟶ Ab]，以及 **[homZ_tensor_adjunction A : TensorAF A ⊣ HomZRF A]**。- 复合，同伦链外部项：[hom_hom_swap] 和 [Sets]-isomorphism [hom_hom_swap_iso]。在 [eq_refl]（[hom_hom_swap_at], [hom_hom_swap_iso_to], [hom_hom_swap_iso_from_at]）处，交换实际上是两个参数的交换。[hom_hom_swap_natural] 说明了它在 G 中的自然性，直到 ≈。- 关于 #449 的张量：[TensorBF_AFT B] 在 A 上的对象是 Instance/Mod/TensorAFT.v 的 [bal_tensor_via_AFT B A] 的 [repr_obj]，[TensorBF_AFT_iso : TensorBF_AFT ≈ TensorBF B] 是从该文件的 [bal_AFT_iso] 组装而成的，**[hom_tensor_adjunction : TensorBF_AFT ⊣ HomZLF B]** — 这是问题的 Verification 块打印的名称 — 是由 Theory/Adjunction.v 的 [adjunction_along_left_iso] 沿传递的 [tensor_homZ_adjunction]。同样的 [hom_tensor_adjunction_right] 适用于第二条支路。两个转置通过 [from (bal_AFT_iso _ _)] 在 [eq_refl] 处被读取回来。- B := R（章节 [RingUnit] 和 [RingCoext]）：[环单位同构 A :  
 BalTensor R_R A ≅ rm_ab A] 在 Ab 中（R ⊗_R A ≅ A；两个分量在
 [eq_refl] ），[ring_unit_nat : RMod_Forget_Ab R ≈ TensorBF R_R]，
 [homzl_ring_adjunction : RMod_Forget_Ab R ⊣ HomZLF R_R]，以及与 Instance/Mod/Coextension.v 中 [coex_adjunction] 的
 比较：
 群在 [eq_refl]（[homzl_ring_group]）一致，作用在 [eq_refl]（[homzl_ring_act]）逐点一致，
 两个伴随的转置在 [eq_refl]（[homzl_ring_adjunction_is_coex_at]）逐点一致，
 并且 [homzl_coext_iso] 是 [RMod R] 中的一个同构，其两个映射都是恒等映射。这两个记录未被识别——这是一个陈述的事实，已测量，并未在此处固定。[HomZL (Ring_RMod (Ring_op R)) G = CoextObj R G] 在 [eq_refl] 被拒绝，结束于“（无法统一 'HomZL (Ring_RMod (Ring_op R)) G' 和 'CoextObj R G'）”。在一个草稿副本中它仍然被拒绝，在该副本中，本文件及 Instance/Mod/Coextension.v 的每个 [Qed]（直到该文件的探测部分）都被转换为 [Defined] 在 [Set Transparent Obligations] 下，因此拒绝并不是由这两个文件的不透明性引起的；它们所依赖的文件（Instance/Mod.v，Instance/Ab.v，Instance/Mod/Bimodule.v 及其他）的 [Qed] 保持不透明，因此是否法律字段在证明上不同，而不只是通过更深层的不透明性不同，还未被测量，这里没有说明它们是不同的证明。[homzl_coext_iso]
 与上面的 [eq_refl] 组件一起，在该翻转级别上是最强的识别。

 无交换性。[HomTensor] 节只有 [Context] 是 R 和 B。
 [HomZL] 的模律消耗 B 自身的律而不消耗 R 的交换性：[hzl_act_assoc] 是通过 [Ring_op] 读取 B 的 [rm_smul_assoc]。前向转置的 R 线性是平衡关系本身（[be_balance]，在 [ht_to] 中）；后向转置的平衡是给定映射的 [rm_map_smul]（[ht_bal]）。
 树内邻居都没有以裸阿贝尔群形式承载 G：Instance/Mod/Closed.v 的 [HomMod] 需要交换性，而 Instance/Mod/Bimodule.v 的 [HomAbBimod] 是双模值。宇宙，由 [About] 在 [Set Printing Universes] 下测量。每个部分为 [R : RingObject@{ra rc rp}] 声明 [Universes ra rc rp]。本文件常量的约束块中的每个宇宙方程属于三种类型之一，这里没有引入： (i) [RMod R] 的对象实例，其对象是 [RModObject@{rc ra rc rc rc ra rc rp} R]（例如 [hom_hom_swap] 中的实例 A）；(ii) 在本元宇宙 rc 中的 [Ab] 的对象实例 [AbObject@{rc rc rc}]，它是 Instance/Ab.v 的手动引脚（[obj := AbObject@{p p p}]）且是 G 所在位置；(iii) 在 rc 上固定模块的组（[HomZL] 中的 B，[HomZR] 中的 A），因 [hom_ab@{u u0}] 返回 [AbObject@{u u u}] 并以 [Ab] 作为其来源而被强制。因此 [tensor_homZ_adjunction] 读取 [Adjunction@{u4 rc rc u5 rc rc rc rc u6 rc u7}]，在三个环宇宙之间没有方程。[ring_unit_iso] 和 [ring_unit_nat] 保持在 [RingObject@{ra rc rp}]，没有方程。[homzl_ring_adjunction] 携带 [ra = rc] 和 [ra = rp]：它的右伴随是 [hom_ab]，来自 R 自身的加法群 [ring_ab R : AbObject@{ra rc rp}]，这（iii）放在 Ab 的对象实例上——同样的原因 [CoextObj] 也携带了识别。因此，章节 [RingCoext] 固定了 [R : RingObject@{r r r}]。未交付。在 FIXED 模块中没有自然性（第一段为 B，第二段为 A）：张量没有组装成双函子 [ModR R ∏ RMod R ⟶ Ab]，因此 Adjunction/Parameter.v 的 [ParametrizedAdjunction] 没有被实例化。该同构是同态集合的双射，而不是同态群的双射；Adjunction/Additive.v 的 [adj_hom_ab_iso] 没有被应用于它们。[hom_hom_swap] 仅在 G 中声明为自然（[hom_hom_swap_natural]）；在 A 或 B 中的自然性需要将 hom_Z(−, G) 作为模块变量的函子，这没有构建。没有在记录层面将 [HomZL R_R G] 与 [CoextObj R G]（如上）识别。也没有与 Instance/Mod/Closed.v 的 [HomMod] 在交换环上的比较。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Coextension.
Require Import Category.Instance.Mod.TensorAFT.
Require Import Category.Structure.AbCategory.
Require Import Category.Adjunction.Additive.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.
#[local] Obligation Tactic := idtac.

(*
   * Mac Lane V.8 Ex 2a, first isomorphism, as an adjunction
   (B ⊗_R −) ⊣ hom_Z(B, −) : Ab → R-Mod,
   for a RIGHT R-module B (an [RModObject (Ring_op R)]). 

   --------
   * Mac Lane V.8 练习 2a，第一个同构定理，作为一个伴随对  
   (B ⊗_R −) ⊣ hom_Z(B, −) : Ab → R-Mod，  
   对于一个右 R-模 B（一个 [RModObject (Ring_op R)] ）。
*)
Section HomTensor.

Universes ra rc rp.

Context {R : RingObject@{ra rc rp}}.
Context (B : RModObject (Ring_op R)).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation BC := (carrier (cmon_setoid (rm_ab B))).
Local Notation BG := (rm_ab B).

Definition hzl_group (G : AbObject) : AbObject := hom_ab Ab_AbEnriched BG G.

(* (r · f)(b) := f (b ⊲ r) *)
Program Definition hzl_act (G : AbObject) (r : RC) (f : AbHom BG G) :
  AbHom BG G := {|
  cmon_map := {| morphism := fun b => cmon_map f (rm_smul B r b) |}
|}.
Next Obligation.
  intros G r f b b' Hb.
  exact (proper_morphism (cmon_map f) _ _
           (rm_smul_respects B r r (reflexivity r) b b' Hb)).
Qed.
Next Obligation.
  intros G r f; simpl.
  transitivity (cmon_map f (cmon_zero BG)).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_zero_r B r)).
  - exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros G r f b b'; simpl.
  transitivity (cmon_map f (cmon_plus BG (rm_smul B r b) (rm_smul B r b'))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_distr_l B r b b')).
  - exact (cmon_map_plus f _ _).
Qed.

Lemma hzl_act_respects (G : AbObject) :
  Proper (equiv ==> equiv ==> equiv) (hzl_act G).
Proof.
  intros r r' Hr f g Hfg b; simpl.
  transitivity (cmon_map f (rm_smul B r' b)).
  - exact (proper_morphism (cmon_map f) _ _
             (rm_smul_respects B r r' Hr b b (reflexivity b))).
  - exact (Hfg _).
Qed.

Lemma hzl_act_distr_l (G : AbObject) (r : RC) (f g : AbHom BG G) :
  hzl_act G r (cmon_plus (hzl_group G) f g)
    ≈ cmon_plus (hzl_group G) (hzl_act G r f) (hzl_act G r g).
Proof. intro b; reflexivity. Qed.

Lemma hzl_act_distr_r (G : AbObject) (r r' : RC) (f : AbHom BG G) :
  hzl_act G (rig_add (ring_rig R) r r') f
    ≈ cmon_plus (hzl_group G) (hzl_act G r f) (hzl_act G r' f).
Proof.
  intro b; simpl.
  transitivity (cmon_map f (cmon_plus BG (rm_smul B r b) (rm_smul B r' b))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_distr_r B r r' b)).
  - exact (cmon_map_plus f _ _).
Qed.

(*
 ((r s)·f)(b) = f (b ⊲ (r s)) = f ((b ⊲ r) ⊲ s) = (r·(s·f))(b):
 B's right associativity, read through [Ring_op], and nothing else. 

 --------
 ((r s)·f)(b) = f (b ⊲ (r s)) = f ((b ⊲ r) ⊲ s) = (r·(s·f))(b)：
 B 的右结合性，通过 [Ring_op] 阅读，除此之外没有其他。
*)
Lemma hzl_act_assoc (G : AbObject) (r s : RC) (f : AbHom BG G) :
  hzl_act G (rig_mul (ring_rig R) r s) f ≈ hzl_act G r (hzl_act G s f).
Proof.
  intro b; simpl.
  exact (proper_morphism (cmon_map f) _ _ (rm_smul_assoc B s r b)).
Qed.

Lemma hzl_act_one (G : AbObject) (f : AbHom BG G) :
  hzl_act G (rig_one (ring_rig R)) f ≈ f.
Proof.
  intro b; simpl.
  exact (proper_morphism (cmon_map f) _ _ (rm_smul_one B b)).
Qed.

Definition HomZL (G : AbObject) : RModObject R := {|
  rm_ab            := hzl_group G;
  rm_smul          := hzl_act G;
  rm_smul_respects := hzl_act_respects G;
  rm_smul_distr_l  := hzl_act_distr_l G;
  rm_smul_distr_r  := hzl_act_distr_r G;
  rm_smul_assoc    := hzl_act_assoc G;
  rm_smul_one      := hzl_act_one G
|}.

Program Definition hzl_map_ab {G H : AbObject} (f : AbHom G H) :
  AbHom (hzl_group G) (hzl_group H) := {|
  cmon_map := {| morphism := fun phi => (cmon_hom_compose f phi : AbHom BG H) |}
|}.
Next Obligation.
  intros G H f phi phi' Hphi b; simpl.
  exact (proper_morphism (cmon_map f) _ _ (Hphi b)).
Qed.
Next Obligation. intros G H f b; simpl. exact (cmon_map_zero f). Qed.
Next Obligation. intros G H f phi psi b; simpl. exact (cmon_map_plus f _ _). Qed.

Program Definition HomZLMap {G H : AbObject} (f : AbHom G H) :
  HomZL G ~{RMod R}~> HomZL H := {| rm_hom := hzl_map_ab f |}.
Next Obligation. intros G H f r phi b; reflexivity. Qed.

Program Definition HomZLF : Ab ⟶ RMod R := {|
  fobj := HomZL;
  fmap := @HomZLMap
|}.
Next Obligation. intros G H f g Hfg phi b; simpl. exact (Hfg _). Qed.
Next Obligation. intros G phi b; reflexivity. Qed.
Next Obligation. intros G H K f g phi b; reflexivity. Qed.

(** The tensor side, B ⊗_R − : R-Mod → Ab. / 张量侧，B ⊗_R − : R-模 → 阿贝尔群。 *)
Program Definition tb_bal {A A' : RModObject R} (f : A ~{RMod R}~> A') :
  BalBiadditive B A (BalTensor B A') := {|
  bal_map := fun b a => bs_gen b (cmon_map (rm_hom f) a)
|}.
Next Obligation.
  intros A A' f b b' Hb a a' Ha.
  exact (be_gen Hb (proper_morphism (cmon_map (rm_hom f)) _ _ Ha)).
Qed.
Next Obligation. intros A A' f b b' a; exact (be_add_l b b' _). Qed.
Next Obligation.
  intros A A' f b a a'.
  exact (be_trans
           (be_gen (reflexivity b) (cmon_map_plus (rm_hom f) a a'))
           (be_add_r b _ _)).
Qed.
Next Obligation.
  intros A A' f r b a.
  exact (be_trans (be_balance r b _)
           (be_gen (reflexivity b)
              (symmetry (rm_map_smul f r a)))).
Qed.

Program Definition TensorBF : RMod R ⟶ Ab := {|
  fobj := fun A => BalTensor B A;
  fmap := fun A A' f => @bal_med _ B A _ (tb_bal f)
|}.
Next Obligation.
  intros A A' f g Hfg s.
  revert s; apply bal_hom_ext; intros b a; simpl.
  exact (be_gen (reflexivity b) (Hfg a)).
Qed.
Next Obligation.
  intros A s; revert s; apply bal_hom_ext; intros b a; simpl.
  exact (bs_refl _).
Qed.
Next Obligation.
  intros A A' A'' f g s; revert s; apply bal_hom_ext; intros b a; simpl.
  exact (bs_refl _).
Qed.

(** The two transposes. / 两个转置。 *)
Program Definition ht_to_inner {A : RModObject R} {G : AbObject}
  (psi : BalTensor B A ~{Ab}~> G) (a : carrier (cmon_setoid (rm_ab A))) :
  AbHom BG G := {|
  cmon_map := {| morphism := fun b => cmon_map psi (bs_gen b a) |}
|}.
Next Obligation.
  intros A G psi a b b' Hb.
  exact (proper_morphism (cmon_map psi) _ _ (be_gen Hb (reflexivity a))).
Qed.
Next Obligation.
  intros A G psi a; simpl.
  transitivity (cmon_map psi (cmon_zero (BalTensor B A))).
  - exact (proper_morphism (cmon_map psi) _ _ (bal_gen_zero_l B A a)).
  - exact (cmon_map_zero psi).
Qed.
Next Obligation.
  intros A G psi a b b'; simpl.
  transitivity (cmon_map psi (cmon_plus (BalTensor B A) (bs_gen b a) (bs_gen b' a))).
  - exact (proper_morphism (cmon_map psi) _ _ (be_add_l b b' a)).
  - exact (cmon_map_plus psi _ _).
Qed.

Program Definition ht_to_ab {A : RModObject R} {G : AbObject}
  (psi : BalTensor B A ~{Ab}~> G) : AbHom (rm_ab A) (hzl_group G) := {|
  cmon_map := {| morphism := fun a => ht_to_inner psi a |}
|}.
Next Obligation.
  intros A G psi a a' Ha b; simpl.
  exact (proper_morphism (cmon_map psi) _ _ (be_gen (reflexivity b) Ha)).
Qed.
Next Obligation.
  intros A G psi b; simpl.
  transitivity (cmon_map psi (cmon_zero (BalTensor B A))).
  - exact (proper_morphism (cmon_map psi) _ _ (bal_gen_zero_r B A b)).
  - exact (cmon_map_zero psi).
Qed.
Next Obligation.
  intros A G psi a a' b; simpl.
  transitivity (cmon_map psi (cmon_plus (BalTensor B A) (bs_gen b a) (bs_gen b a'))).
  - exact (proper_morphism (cmon_map psi) _ _ (be_add_r b a a')).
  - exact (cmon_map_plus psi _ _).
Qed.

(* R-linearity of the transpose IS the balance relation. / 转置的R线性就是平衡关系。 *)
Program Definition ht_to {A : RModObject R} {G : AbObject}
  (psi : BalTensor B A ~{Ab}~> G) : A ~{RMod R}~> HomZL G := {|
  rm_hom := ht_to_ab psi
|}.
Next Obligation.
  intros A G psi r a b; simpl.
  exact (proper_morphism (cmon_map psi) _ _ (be_sym (be_balance r b a))).
Qed.

Program Definition ht_bal {A : RModObject R} {G : AbObject}
  (phi : A ~{RMod R}~> HomZL G) : BalBiadditive B A G := {|
  bal_map := fun b a => cmon_map (cmon_map (rm_hom phi) a) b
|}.
Next Obligation.
  intros A G phi b b' Hb a a' Ha; simpl.
  transitivity (cmon_map (cmon_map (rm_hom phi) a) b').
  - exact (proper_morphism (cmon_map (cmon_map (rm_hom phi) a)) _ _ Hb).
  - exact (proper_morphism (cmon_map (rm_hom phi)) _ _ Ha b').
Qed.
Next Obligation.
  intros A G phi b b' a; exact (cmon_map_plus (cmon_map (rm_hom phi) a) b b').
Qed.
Next Obligation.
  intros A G phi b a a'; exact (cmon_map_plus (rm_hom phi) a a' b).
Qed.
Next Obligation.
  intros A G phi r b a; simpl.
  exact (symmetry (rm_map_smul phi r a b)).
Qed.

Definition ht_from {A : RModObject R} {G : AbObject}
  (phi : A ~{RMod R}~> HomZL G) : BalTensor B A ~{Ab}~> G :=
  bal_med (ht_bal phi).

Program Definition ht_adj (A : RModObject R) (G : AbObject) :
  @Isomorphism Sets
    {| carrier := BalTensor B A ~{Ab}~> G;
       is_setoid := @homset Ab (BalTensor B A) G |}
    {| carrier := A ~{RMod R}~> HomZL G;
       is_setoid := @homset (RMod R) A (HomZL G) |} := {|
  to   := {| morphism := fun psi => ht_to psi |};
  from := {| morphism := fun phi => ht_from phi |}
|}.
Next Obligation. intros A G psi psi' H a b; exact (H _). Qed.
Next Obligation.
  intros A G phi phi' H s; revert s; apply bal_hom_ext; intros b a; simpl.
  exact (H a b).
Qed.
Next Obligation. intros A G phi a b; simpl; reflexivity. Qed.
Next Obligation.
  intros A G psi s; revert s; apply bal_hom_ext; intros b a; simpl.
  reflexivity.
Qed.

(*
   * Mac Lane V.8 Ex 2a, first leg: hom_R(A, hom_Z(B, G)) ≅ hom_Z(B ⊗_R A, G),
   natural in A and G. 

   --------
   * Mac Lane V.8 练习 2a，第一部分：hom_R(A, hom_Z(B, G)) ≅ hom_Z(B ⊗_R A, G)，在 A 和 G 中是自然的。
*)
Definition tensor_homZ_adjunction : TensorBF ⊣ HomZLF.
Proof.
  unshelve eapply (@Build_Adjunction' Ab (RMod R) TensorBF HomZLF ht_adj).
  - intros A A' G psi g a b; simpl; reflexivity.
  - intros A G H h psi a b; simpl; reflexivity.
Defined.

Example ht_to_at {A : RModObject R} {G : AbObject}
  (psi : BalTensor B A ~{Ab}~> G) a b :
  cmon_map (cmon_map (rm_hom (to (@adj _ _ _ _ tensor_homZ_adjunction A G) psi)) a) b
    = cmon_map psi (bs_gen b a) := eq_refl.

End HomTensor.

(*
   * Mac Lane V.8 Ex 2a, second leg:
   hom_Z(B ⊗_R A, G) ≅ hom_R(B, hom_Z(A, G))   (right modules),
   i.e. (− ⊗_R A) ⊣ hom_Z(A, −) : Ab → Mod-R, for a LEFT R-module A. 

   --------
   * Mac Lane V.8 练习 2a，第二步：
   hom_Z(B ⊗_R A, G) ≅ hom_R(B, hom_Z(A, G))（右模），
   即 (− ⊗_R A) ⊣ hom_Z(A, −) : Ab → Mod-R，对于一个左 R-模 A。
*)
Section TensorHomRight.

Universes ra rc rp.

Context {R : RingObject@{ra rc rp}}.
Context (A : RModObject R).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation AG := (rm_ab A).

Definition hzr_group (G : AbObject) : AbObject := hom_ab Ab_AbEnriched AG G.

(* (f ⊲ r)(a) := f (r · a) *)
Program Definition hzr_act (G : AbObject) (r : RC) (f : AbHom AG G) :
  AbHom AG G := {|
  cmon_map := {| morphism := fun a => cmon_map f (rm_smul A r a) |}
|}.
Next Obligation.
  intros G r f a a' Ha.
  exact (proper_morphism (cmon_map f) _ _
           (rm_smul_respects A r r (reflexivity r) a a' Ha)).
Qed.
Next Obligation.
  intros G r f; simpl.
  transitivity (cmon_map f (cmon_zero AG)).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_zero_r A r)).
  - exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros G r f a a'; simpl.
  transitivity (cmon_map f (cmon_plus AG (rm_smul A r a) (rm_smul A r a'))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_distr_l A r a a')).
  - exact (cmon_map_plus f _ _).
Qed.

Lemma hzr_act_respects (G : AbObject) :
  Proper (equiv ==> equiv ==> equiv) (hzr_act G).
Proof.
  intros r r' Hr f g Hfg a; simpl.
  transitivity (cmon_map f (rm_smul A r' a)).
  - exact (proper_morphism (cmon_map f) _ _
             (rm_smul_respects A r r' Hr a a (reflexivity a))).
  - exact (Hfg _).
Qed.

Lemma hzr_act_distr_l (G : AbObject) (r : RC) (f g : AbHom AG G) :
  hzr_act G r (cmon_plus (hzr_group G) f g)
    ≈ cmon_plus (hzr_group G) (hzr_act G r f) (hzr_act G r g).
Proof. intro a; reflexivity. Qed.

Lemma hzr_act_distr_r (G : AbObject) (r r' : RC) (f : AbHom AG G) :
  hzr_act G (rig_add (ring_rig (Ring_op R)) r r') f
    ≈ cmon_plus (hzr_group G) (hzr_act G r f) (hzr_act G r' f).
Proof.
  intro a; simpl.
  transitivity (cmon_map f (cmon_plus AG (rm_smul A r a) (rm_smul A r' a))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_distr_r A r r' a)).
  - exact (cmon_map_plus f _ _).
Qed.

Lemma hzr_act_assoc (G : AbObject) (r s : RC) (f : AbHom AG G) :
  hzr_act G (rig_mul (ring_rig (Ring_op R)) r s) f ≈ hzr_act G r (hzr_act G s f).
Proof.
  intro a; simpl.
  exact (proper_morphism (cmon_map f) _ _ (rm_smul_assoc A s r a)).
Qed.

Lemma hzr_act_one (G : AbObject) (f : AbHom AG G) :
  hzr_act G (rig_one (ring_rig (Ring_op R))) f ≈ f.
Proof.
  intro a; simpl.
  exact (proper_morphism (cmon_map f) _ _ (rm_smul_one A a)).
Qed.

Definition HomZR (G : AbObject) : RModObject (Ring_op R) :=
  @Build_RModObject (Ring_op R) (hzr_group G) (hzr_act G)
    (hzr_act_respects G) (hzr_act_distr_l G) (hzr_act_distr_r G)
    (hzr_act_assoc G) (hzr_act_one G).

Program Definition hzr_map_ab {G H : AbObject} (f : AbHom G H) :
  AbHom (hzr_group G) (hzr_group H) := {|
  cmon_map := {| morphism := fun phi => (cmon_hom_compose f phi : AbHom AG H) |}
|}.
Next Obligation.
  intros G H f phi phi' Hphi a; simpl.
  exact (proper_morphism (cmon_map f) _ _ (Hphi a)).
Qed.
Next Obligation. intros G H f a; simpl. exact (cmon_map_zero f). Qed.
Next Obligation. intros G H f phi psi a; simpl. exact (cmon_map_plus f _ _). Qed.

Program Definition HomZRMap {G H : AbObject} (f : AbHom G H) :
  HomZR G ~{ModR R}~> HomZR H := {| rm_hom := hzr_map_ab f |}.
Next Obligation. intros G H f r phi a; reflexivity. Qed.

Program Definition HomZRF : Ab ⟶ ModR R := {|
  fobj := HomZR;
  fmap := @HomZRMap
|}.
Next Obligation. intros G H f g Hfg phi a; simpl. exact (Hfg _). Qed.
Next Obligation. intros G phi a; reflexivity. Qed.
Next Obligation. intros G H K f g phi a; reflexivity. Qed.

Program Definition ta_bal {B B' : RModObject (Ring_op R)} (f : B ~{ModR R}~> B') :
  BalBiadditive B A (BalTensor B' A) := {|
  bal_map := fun b a => bs_gen (cmon_map (rm_hom f) b) a
|}.
Next Obligation.
  intros B B' f b b' Hb a a' Ha.
  exact (be_gen (proper_morphism (cmon_map (rm_hom f)) _ _ Hb) Ha).
Qed.
Next Obligation.
  intros B B' f b b' a.
  exact (be_trans (be_gen (cmon_map_plus (rm_hom f) b b') (reflexivity a))
                  (be_add_l _ _ a)).
Qed.
Next Obligation. intros B B' f b a a'; exact (be_add_r _ a a'). Qed.
Next Obligation.
  intros B B' f r b a.
  exact (be_trans (be_gen (rm_map_smul f r b) (reflexivity a))
                  (be_balance r _ a)).
Qed.

Program Definition TensorAF : ModR R ⟶ Ab := {|
  fobj := fun B => BalTensor B A;
  fmap := fun B B' f => @bal_med _ B A _ (ta_bal f)
|}.
Next Obligation.
  intros B B' f g Hfg s; revert s; apply bal_hom_ext; intros b a; simpl.
  exact (be_gen (Hfg b) (reflexivity a)).
Qed.
Next Obligation.
  intros B s; revert s; apply bal_hom_ext; intros b a; simpl.
  exact (bs_refl _).
Qed.
Next Obligation.
  intros B B' B'' f g s; revert s; apply bal_hom_ext; intros b a; simpl.
  exact (bs_refl _).
Qed.

Program Definition th_to_inner {B : RModObject (Ring_op R)} {G : AbObject}
  (psi : BalTensor B A ~{Ab}~> G) (b : carrier (cmon_setoid (rm_ab B))) :
  AbHom AG G := {|
  cmon_map := {| morphism := fun a => cmon_map psi (bs_gen b a) |}
|}.
Next Obligation.
  intros B G psi b a a' Ha.
  exact (proper_morphism (cmon_map psi) _ _ (be_gen (reflexivity b) Ha)).
Qed.
Next Obligation.
  intros B G psi b; simpl.
  transitivity (cmon_map psi (cmon_zero (BalTensor B A))).
  - exact (proper_morphism (cmon_map psi) _ _ (bal_gen_zero_r B A b)).
  - exact (cmon_map_zero psi).
Qed.
Next Obligation.
  intros B G psi b a a'; simpl.
  transitivity (cmon_map psi (cmon_plus (BalTensor B A) (bs_gen b a) (bs_gen b a'))).
  - exact (proper_morphism (cmon_map psi) _ _ (be_add_r b a a')).
  - exact (cmon_map_plus psi _ _).
Qed.

Program Definition th_to_ab {B : RModObject (Ring_op R)} {G : AbObject}
  (psi : BalTensor B A ~{Ab}~> G) : AbHom (rm_ab B) (hzr_group G) := {|
  cmon_map := {| morphism := fun b => th_to_inner psi b |}
|}.
Next Obligation.
  intros B G psi b b' Hb a; simpl.
  exact (proper_morphism (cmon_map psi) _ _ (be_gen Hb (reflexivity a))).
Qed.
Next Obligation.
  intros B G psi a; simpl.
  transitivity (cmon_map psi (cmon_zero (BalTensor B A))).
  - exact (proper_morphism (cmon_map psi) _ _ (bal_gen_zero_l B A a)).
  - exact (cmon_map_zero psi).
Qed.
Next Obligation.
  intros B G psi b b' a; simpl.
  transitivity (cmon_map psi (cmon_plus (BalTensor B A) (bs_gen b a) (bs_gen b' a))).
  - exact (proper_morphism (cmon_map psi) _ _ (be_add_l b b' a)).
  - exact (cmon_map_plus psi _ _).
Qed.

Program Definition th_to {B : RModObject (Ring_op R)} {G : AbObject}
  (psi : BalTensor B A ~{Ab}~> G) : B ~{ModR R}~> HomZR G := {|
  rm_hom := th_to_ab psi
|}.
Next Obligation.
  intros B G psi r b a; simpl.
  exact (proper_morphism (cmon_map psi) _ _ (@be_balance R B A r b a)).
Qed.

Program Definition th_bal {B : RModObject (Ring_op R)} {G : AbObject}
  (phi : B ~{ModR R}~> HomZR G) : BalBiadditive B A G := {|
  bal_map := fun b a => cmon_map (cmon_map (rm_hom phi) b) a
|}.
Next Obligation.
  intros B G phi b b' Hb a a' Ha; simpl.
  transitivity (cmon_map (cmon_map (rm_hom phi) b) a').
  - exact (proper_morphism (cmon_map (cmon_map (rm_hom phi) b)) _ _ Ha).
  - exact (proper_morphism (cmon_map (rm_hom phi)) _ _ Hb a').
Qed.
Next Obligation.
  intros B G phi b b' a; exact (cmon_map_plus (rm_hom phi) b b' a).
Qed.
Next Obligation.
  intros B G phi b a a'; exact (cmon_map_plus (cmon_map (rm_hom phi) b) a a').
Qed.
Next Obligation.
  intros B G phi r b a; simpl.
  exact (rm_map_smul phi r b a).
Qed.

Program Definition th_adj (B : RModObject (Ring_op R)) (G : AbObject) :
  @Isomorphism Sets
    {| carrier := BalTensor B A ~{Ab}~> G;
       is_setoid := @homset Ab (BalTensor B A) G |}
    {| carrier := B ~{ModR R}~> HomZR G;
       is_setoid := @homset (ModR R) B (HomZR G) |} := {|
  to   := {| morphism := fun psi => th_to psi |};
  from := {| morphism := fun phi => bal_med (th_bal phi) |}
|}.
Next Obligation. intros B G psi psi' H b a; exact (H _). Qed.
Next Obligation.
  intros B G phi phi' H s; revert s; apply bal_hom_ext; intros b a; simpl.
  exact (H b a).
Qed.
Next Obligation. intros B G phi b a; simpl; reflexivity. Qed.
Next Obligation.
  intros B G psi s; revert s; apply bal_hom_ext; intros b a; simpl.
  reflexivity.
Qed.

Definition homZ_tensor_adjunction : TensorAF ⊣ HomZRF.
Proof.
  unshelve eapply (@Build_Adjunction' Ab (ModR R) TensorAF HomZRF th_adj).
  - intros B B' G psi g b a; simpl; reflexivity.
  - intros B G H h psi b a; simpl; reflexivity.
Defined.

End TensorHomRight.

(** The composite natural bijection hom_R(A, hom_Z(B,G)) ≅ hom_R(B, hom_Z(A,G)). / 复合自然双射 hom_R(A, hom_Z(B,G)) ≅ hom_R(B, hom_Z(A,G))。 *)
Section HomHomSwap.

Universes ra rc rp.

Context {R : RingObject@{ra rc rp}}.
Context (A : RModObject R).
Context (B : RModObject (Ring_op R)).
Context (G : AbObject).

Definition hom_hom_swap (phi : A ~{RMod R}~> HomZL B G) :
  B ~{ModR R}~> HomZR A G :=
  to (@adj _ _ _ _ (homZ_tensor_adjunction A) B G)
     (from (@adj _ _ _ _ (tensor_homZ_adjunction B) A G) phi).

Example hom_hom_swap_at (phi : A ~{RMod R}~> HomZL B G) b a :
  cmon_map (cmon_map (rm_hom (hom_hom_swap phi)) b) a
    = cmon_map (cmon_map (rm_hom phi) a) b := eq_refl.

(** The composite as a bijection of hom-setoids. / 作为同值宿集的双射的复合。 *)
Definition hom_hom_swap_iso :
  @Isomorphism Sets
    {| carrier := A ~{RMod R}~> HomZL B G;
       is_setoid := @homset (RMod R) A (HomZL B G) |}
    {| carrier := B ~{ModR R}~> HomZR A G;
       is_setoid := @homset (ModR R) B (HomZR A G) |} :=
  iso_compose (@adj _ _ _ _ (homZ_tensor_adjunction A) B G)
    (iso_sym (@adj _ _ _ _ (tensor_homZ_adjunction B) A G)).

Example hom_hom_swap_iso_to (phi : A ~{RMod R}~> HomZL B G) :
  to hom_hom_swap_iso phi = hom_hom_swap phi := eq_refl.

Example hom_hom_swap_iso_from_at (chi : B ~{ModR R}~> HomZR A G) a b :
  cmon_map (cmon_map (rm_hom (from hom_hom_swap_iso chi)) a) b
    = cmon_map (cmon_map (rm_hom chi) b) a := eq_refl.

End HomHomSwap.

(* The swap is natural in the abelian group: post-composing with k : G → G' before or after swapping gives the same map, pointwise at the level of elements. / 在阿贝尔群中，交换是自然的：在交换之前或之后与 k : G → G' 后合成，得到的映射在元素层面是逐点相同的。 *)
Lemma hom_hom_swap_natural@{ra rc rp +} {R : RingObject@{ra rc rp}}
  (A : RModObject R) (B : RModObject (Ring_op R)) {G G' : AbObject}
  (k : G ~{Ab}~> G') (phi : A ~{RMod R}~> HomZL B G) :
  hom_hom_swap A B G' (HomZLMap B k ∘ phi)
    ≈ HomZRMap A k ∘ hom_hom_swap A B G phi.
Proof. intros b a; reflexivity. Qed.

(** ** Over #449's tensor / ** 在 #449 的张量上 *)

Section HomTensorAFT.

Universes ra rc rp.

Context {R : RingObject@{ra rc rp}}.
Context (B : RModObject (Ring_op R)).

Definition TensorBF_AFT_obj (A : RModObject R) : AbObject :=
  @repr_obj Ab (BalBiadd B A) (bal_tensor_via_AFT B A).

Definition TensorBF_AFT_fmap {A A' : RModObject R}
  (f : A ~{RMod R}~> A') :
  TensorBF_AFT_obj A ~{Ab}~> TensorBF_AFT_obj A' :=
  from (bal_AFT_iso B A') ∘ fmap[TensorBF B] f ∘ to (bal_AFT_iso B A).

Program Definition TensorBF_AFT : RMod R ⟶ Ab := {|
  fobj := TensorBF_AFT_obj;
  fmap := @TensorBF_AFT_fmap
|}.
Next Obligation.
  intros A A' f g Hfg; unfold TensorBF_AFT_fmap.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros A; unfold TensorBF_AFT_fmap.
  rewrite fmap_id, id_right.
  apply iso_from_to.
Qed.
Next Obligation.
  intros A A' A'' f g; unfold TensorBF_AFT_fmap.
  rewrite fmap_comp.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (to (bal_AFT_iso B A'))).
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

Definition TensorBF_AFT_iso : TensorBF_AFT ≈ TensorBF B.
Proof.
  exists (fun A => bal_AFT_iso B A).
  intros A A' f; simpl; unfold TensorBF_AFT_fmap; reflexivity.
Defined.

(** Mac Lane V.8 Exercise 2(a), first isomorphism, over #449's tensor. / Mac Lane V.8 练习 2(a)，第一次同构，基于 #449 的张量。 *)
Definition hom_tensor_adjunction : TensorBF_AFT ⊣ HomZLF B :=
  adjunction_along_left_iso TensorBF_AFT_iso (tensor_homZ_adjunction B).

Example hom_tensor_adjunction_to_at {A : RModObject R} {G : AbObject}
  (psi : TensorBF_AFT_obj A ~{Ab}~> G) a b :
  cmon_map (cmon_map (rm_hom (to (@adj _ _ _ _ hom_tensor_adjunction A G) psi)) a) b
    = cmon_map psi (cmon_map (from (bal_AFT_iso B A)) (bs_gen b a)) :=
  eq_refl.

End HomTensorAFT.

Section TensorHomRightAFT.

Universes ra rc rp.

Context {R : RingObject@{ra rc rp}}.
Context (A : RModObject R).

Definition TensorAF_AFT_obj (B : RModObject (Ring_op R)) : AbObject :=
  @repr_obj Ab (BalBiadd B A) (bal_tensor_via_AFT B A).

Definition TensorAF_AFT_fmap {B B' : RModObject (Ring_op R)}
  (f : B ~{ModR R}~> B') :
  TensorAF_AFT_obj B ~{Ab}~> TensorAF_AFT_obj B' :=
  from (bal_AFT_iso B' A) ∘ fmap[TensorAF A] f ∘ to (bal_AFT_iso B A).

Program Definition TensorAF_AFT : ModR R ⟶ Ab := {|
  fobj := TensorAF_AFT_obj;
  fmap := @TensorAF_AFT_fmap
|}.
Next Obligation.
  intros B B' f g Hfg; unfold TensorAF_AFT_fmap.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros B; unfold TensorAF_AFT_fmap.
  rewrite fmap_id, id_right.
  apply iso_from_to.
Qed.
Next Obligation.
  intros B B' B'' f g; unfold TensorAF_AFT_fmap.
  rewrite fmap_comp.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (to (bal_AFT_iso B' A))).
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

Definition TensorAF_AFT_iso : TensorAF_AFT ≈ TensorAF A.
Proof.
  exists (fun B => bal_AFT_iso B A).
  intros B B' f; simpl; unfold TensorAF_AFT_fmap; reflexivity.
Defined.

(** Mac Lane V.8 Exercise 2(a), second isomorphism, over #449's tensor. / Mac Lane V.8 练习 2(a)，第二同构，基于 #449 的张量。 *)
Definition hom_tensor_adjunction_right : TensorAF_AFT ⊣ HomZRF A :=
  adjunction_along_left_iso TensorAF_AFT_iso (homZ_tensor_adjunction A).

Example hom_tensor_adjunction_right_to_at {B : RModObject (Ring_op R)}
  {G : AbObject} (psi : TensorAF_AFT_obj B ~{Ab}~> G) b a :
  cmon_map (cmon_map (rm_hom
    (to (@adj _ _ _ _ hom_tensor_adjunction_right B G) psi)) b) a
    = cmon_map psi (cmon_map (from (bal_AFT_iso B A)) (bs_gen b a)) :=
  eq_refl.

End TensorHomRightAFT.

(* * ** Mac Lane's B := R: the coextension module / * ** Mac Lane 的 B := R：共扩展模 *)

Example homzl_ring_group@{ra +} (R : RingObject@{ra ra ra}) (G : AbObject) :
  rm_ab (HomZL (Ring_RMod (Ring_op R)) G) = rm_ab (CoextObj R G) := eq_refl.

Example homzl_ring_act@{ra +} (R : RingObject@{ra ra ra}) (G : AbObject) r f s :
  cmon_map (rm_smul (HomZL (Ring_RMod (Ring_op R)) G) r f) s
    = cmon_map (rm_smul (CoextObj R G) r f) s := eq_refl.

(* * ** Mac Lane's route to Exercise 2(b): B := R and R ⊗_R A ≅ A / * ** 麦克·莱恩到练习 2(b) 的路径：B := R 并且 R ⊗_R A ≅ A *)

Section RingUnit.

Universes ra rc rp.

Context {R : RingObject@{ra rc rp}}.

Local Notation RR := (Ring_RMod (Ring_op R)).

Program Definition runit_bal (A : RModObject R) :
  BalBiadditive RR A (rm_ab A) := {|
  bal_map := fun b a => rm_smul A b a
|}.
Next Obligation. intros A; exact (rm_smul_respects A). Qed.
Next Obligation. intros A b b' a; exact (rm_smul_distr_r A b b' a). Qed.
Next Obligation. intros A b a a'; exact (rm_smul_distr_l A b a a'). Qed.
Next Obligation. intros A x b a; exact (rm_smul_assoc A b x a). Qed.

Definition runit_to (A : RModObject R) : BalTensor RR A ~{Ab}~> rm_ab A :=
  bal_med (runit_bal A).

Program Definition runit_from (A : RModObject R) :
  rm_ab A ~{Ab}~> BalTensor RR A := {|
  cmon_map := {| morphism := fun a => bs_gen (rig_one (ring_rig R)) a |}
|}.
Next Obligation.
  intros A a a' Ha. exact (be_gen (reflexivity _) Ha).
Qed.
Next Obligation. intros A. exact (bal_gen_zero_r RR A _). Qed.
Next Obligation. intros A a a'. exact (be_add_r _ a a'). Qed.

Lemma runit_gen (A : RModObject R) (b : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (rm_ab A))) :
  @bs_eq R RR A (@bs_gen R RR A (rig_one (ring_rig R)) (rm_smul A b a))
    (@bs_gen R RR A b a).
Proof.
  refine (be_trans (be_sym (@be_balance R RR A b (rig_one (ring_rig R)) a)) _).
  exact (@be_gen R RR A _ _ _ _ (rig_mul_one_l (ring_rig R) b) (reflexivity a)).
Qed.

(** R ⊗_R A ≅ A in Ab. / R ⊗_R A 在 Ab 中同构于 A。 *)
Definition ring_unit_iso (A : RModObject R) :
  @Isomorphism Ab (BalTensor RR A) (rm_ab A).
Proof.
  unshelve econstructor.
  - exact (runit_to A).
  - exact (runit_from A).
  - intro a; simpl. exact (rm_smul_one A a).
  - intro s; revert s. apply bal_hom_ext; intros b a; simpl.
    exact (runit_gen A b a).
Defined.

Example ring_unit_iso_to_at (A : RModObject R) b a :
  cmon_map (to (ring_unit_iso A)) (bs_gen b a) = rm_smul A b a := eq_refl.

Example ring_unit_iso_from_at (A : RModObject R) a :
  cmon_map (from (ring_unit_iso A)) a
    = @bs_gen R RR A (rig_one (ring_rig R)) a := eq_refl.

(** The forgetful functor IS the tensor with R, up to natural isomorphism. / 忘记函子是与 R 的张量，至自然同构为止。 *)
Definition ring_unit_nat : RMod_Forget_Ab R ≈ TensorBF RR.
Proof.
  exists (fun A => iso_sym (ring_unit_iso A)).
  intros A A' f a; simpl.
  symmetry. exact (rm_smul_one A' (cmon_map (rm_hom f) a)).
Defined.

(*
   * Exercise 2(a) at B := R, read along R ⊗_R A ≅ A:
   hom_Z(A, G) ≅ hom_R(A, hom_Z(R, G)). 

   --------
   * 在 B := R 上做练习 2(a)，沿着 R ⊗_R A ≅ A 阅读：
   hom_Z(A, G) ≅ hom_R(A, hom_Z(R, G))。
*)
Definition homzl_ring_adjunction : RMod_Forget_Ab R ⊣ HomZLF RR :=
  adjunction_along_left_iso ring_unit_nat (tensor_homZ_adjunction RR).

Example homzl_ring_adjunction_to_at {A : RModObject R} {G : AbObject}
  (psi : rm_ab A ~{Ab}~> G) a s :
  cmon_map (cmon_map (rm_hom
    (to (@adj _ _ _ _ homzl_ring_adjunction A G) psi)) a) s
    = cmon_map psi (rm_smul A s a) := eq_refl.

End RingUnit.

(*
 From here on the coextension module [CoextObj] enters, and with it the
 three ring universes are identified: [CoextObj]'s own signature
 (Instance/Mod/Coextension.v) is over [RingObject@{u u0 u1}] with
 [u = u0] and [u = u1] among its constraints.  The section above is not
 narrowed by it. 

 --------
 从这里起，余延模块 [CoextObj] 开始作用，并且由此确定了三个环宇宙：[CoextObj] 自己的签名（Instance/Mod/Coextension.v）位于 [RingObject@{u u0 u1}] 之上，同时 [u = u0] 和 [u = u1] 在其约束之中。上述部分不受其限制。
*)
Section RingCoext.

Universes r.

Context {R : RingObject@{r r r}}.

Local Notation RR := (Ring_RMod (Ring_op R)).

(* The same transpose as the coextension adjunction's, pointwise. / 与余拓张的伴随变换相同，逐点地。 *)
Example homzl_ring_adjunction_is_coex_at {A : RModObject R} {G : AbObject}
  (psi : rm_ab A ~{Ab}~> G) a s :
  cmon_map (cmon_map (rm_hom
    (to (@adj _ _ _ _ homzl_ring_adjunction A G) psi)) a) s
    = cmon_map (cmon_map (rm_hom
        (to (@adj _ _ _ _ (coex_adjunction R) A G) psi)) a) s := eq_refl.

(*
   * hom_Z(R, G) read through Exercise 2(a) and through the coextension
   are isomorphic modules, the identity map both ways. 

   --------
   * hom_Z(R, G) 通读练习 2(a) 并通过余扩展是同构模，两边的恒等映射。
*)
Program Definition homzl_coext_to (G : AbObject) :
  HomZL RR G ~{RMod R}~> CoextObj R G := {|
  rm_hom := {| cmon_map := {| morphism := fun f => f |} |}
|}.
Next Obligation. intros G f g H; exact H. Qed.
Next Obligation. intros G s; reflexivity. Qed.
Next Obligation. intros G f g s; reflexivity. Qed.
Next Obligation. intros G x f s; reflexivity. Qed.

Program Definition homzl_coext_from (G : AbObject) :
  CoextObj R G ~{RMod R}~> HomZL RR G := {|
  rm_hom := {| cmon_map := {| morphism := fun f => f |} |}
|}.
Next Obligation. intros G f g H; exact H. Qed.
Next Obligation. intros G s; reflexivity. Qed.
Next Obligation. intros G f g s; reflexivity. Qed.
Next Obligation. intros G x f s; reflexivity. Qed.

Definition homzl_coext_iso (G : AbObject) :
  @Isomorphism (RMod R) (HomZL RR G) (CoextObj R G).
Proof.
  unshelve econstructor.
  - exact (homzl_coext_to G).
  - exact (homzl_coext_from G).
  - intros f s; reflexivity.
  - intros f s; reflexivity.
Defined.

End RingCoext.
