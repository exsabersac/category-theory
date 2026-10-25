Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Comonoid.Hom.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.Presentation.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Supply.

From Coq Require Import Lists.List.
From Coq Require Import PeanoNat.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

Generalizable All Variables.

(* * * The linear discipline over coloured PROPs / * * 彩色 PROP 上的线性学科 *)

(*
 nLab:      https://ncatlab.org/nlab/show/PROP
 nLab:      https://ncatlab.org/nlab/show/linear+logic
 Wikipedia: https://en.wikipedia.org/wiki/Linear_type_system

 A wire type in a typed string-diagram language is LINEAR when values
 of that type may be neither duplicated nor deleted: every linear
 wire entering a diagram must leave it exactly once.  This file
 formalises that discipline over the coloured-PROP spine, in both
 directions:

 - NEGATIVE HALF (the fan-out/discard restriction).  Copyability is
 a boolean predicate [copyable : Colour -> bool]; a colour is
 linear when [copyable c = false].  A signature is CONSERVATIVE at
 a colour [c] when every generator has as many [c]-wires entering
 as leaving ([c_conservative], counted by [count_occ]); the free
 structural operations (identities, braids, composition, tensor)
 are conservative at EVERY colour, so per-colour wire counts are
 an invariant of all free terms ([cterm_count_occ]).  It follows
 that at a conservative colour the hom-types [CTerm S [c] [c; c]]
 (fan-out) and [CTerm S [c] []] (discard) are EMPTY
 ([no_linear_fanout] / [no_linear_discard]).  This is emptiness of
 the raw TYPE of terms, not merely emptiness up to the [CTermEq]
 equivalence — no diagram of that boundary can even be written
 down — and since a presented coloured PROP has literally the same
 morphisms as the free one (only the equivalence coarsens, see
 [Construction/ColouredPROP/Presentation.v]), the emptiness
 descends to EVERY presented quotient
 ([no_linear_fanout_presented] / [no_linear_discard_presented]).
 This is the categorical content of the type-level fan-out check
 of linear dataflow languages: an ill-linear plugging is not
 rewritten away — it is unrepresentable.

 - PERMUTATION INVARIANT.  Over a generator-free signature the
 counting invariant sharpens: every term's output boundary is a
 permutation of its input boundary ([structural_permutation]).
 This is a one-directional, Prop-level necessary condition on
 boundaries — it assigns no permutation to a term and proves no
 converse realizability — a necessary-condition shadow of "the
 free coloured PROP on no generators is the coloured permutation
 groupoid" (cf. [Empty_CSig] in
 [Construction/ColouredPROP/Signature.v]), which is not itself
 formalized here.

 - POSITIVE HALF (fan-out at copyable colours).  Conversely, a
 copyable colour is one whose wire object CARRIES a commutative
 comonoid: the selective supply of
 [Construction/ColouredPROP/Supply.v], whose single per-colour
 primitive [supply_wire] equips [wire c] with its comonoid
 whenever [copyable c = true].  Its comultiplication IS a fan-out
 morphism [wire c ~> wire c ⨂ wire c] ([copyable_fanout]) and its
 counit a discard [wire c ~> I] ([copyable_discard]) — the
 converse of the emptiness theorems, and the reason [copyable] is
 the correct boundary of the linear discipline.  Relative to the
 boundary supplies [supply_list] that [Supply.v] DERIVES from that
 primitive (by tensoring wire comonoids through
 [Theory/Algebra/Comonoid/Tensor.v]; nothing boundary-level is
 postulated), a morphism between all-copyable boundaries is
 DETERMINISTIC when it is a comonoid homomorphism between them
 ([sel_deterministic]) — the two Cho–Jacobs copy/discard
 preservation squares

 scopy ds Hd ∘ f    ≈ (f ⨂ f) ∘ scopy cs Hc
 sdiscard ds Hd ∘ f ≈ sdiscard cs Hc

 ([sel_deterministic_scopy] / [sel_deterministic_sdiscard]),
 packaged by the [ComonoidHom] class of
 [Theory/Algebra/Comonoid/Hom.v], whose kit supplies the
 identity/composition/respectfulness laws
 ([sel_deterministic_id] / [sel_deterministic_comp] /
 [sel_deterministic_equiv]).  The determinism predicate is stated
 on the braided/symmetric monoidal path [MBc P], where the supply
 comonoids live (see the MP/MB mediation note in [Supply.v]).
 The linear/non-linear bridge built on this predicate lives in
 [Construction/ColouredPROP/LNL.v].

 References:
 - Cho & Jacobs, "Disintegration and Bayesian inversion via string
 diagrams", MSCS 29(7):938-971, 2019 (arXiv:1709.00322) —
 determinism as comonoid homomorphy.
 - Fong & Spivak, "Supplying bells and whistles in symmetric
 monoidal categories" (arXiv:1908.02633) — supplies of commutative
 comonoids.
 - Bonchi, Sobocinski & Zanasi, "A categorical semantics of signal
 flow graphs" — coloured PROPs as typed diagram languages. 

 --------
 nLab:       https://ncatlab.org/nlab/show/PROP 
 nLab:       https://ncatlab.org/nlab/show/linear+logic 
 Wikipedia:  https://en.wikipedia.org/wiki/Linear_type_system 

 在类型化字符串图语言中，当某个类型的值既不能被复制也不能被删除时，该类型的线被称为线性（LINEAR）：每条进入图表的线性线都必须恰好离开图表一次。该文件在彩色PROP主干上以双向形式正式化了这一规律：- 负半 (扇出/丢弃限制)。可复制性是布尔谓词 [copyable : Colour -> bool]；当 [copyable c = false] 时，一种颜色是线性的。当每个生成器进入和离开的 [c] 线一样多时，签名在颜色 [c] 下是保守的 ([c_conservative]，由 [count_occ] 计数)；自由结构操作（恒等、编织、组合、张量）在每种颜色下都是保守的，所以每种颜色的线计数是所有自由项的不变量 ([cterm_count_occ])。因此，在保守颜色下，类型同态 [CTerm S [c]   [c; c] ]（扇出）和 [CTerm S [c]  []]（丢弃）是空的 ([no_linear_fanout] / [no_linear_discard])。这是术语的原始类型的空性，而不仅仅是达到 [CTermEq] 等价的空性——即使是那个边界的图也无法被写下——并且由于一个呈现的彩色 PROP 与自由 PROP 具有完全相同的态射（只是等价关系更粗糙，见 [Construction/ColouredPROP/Presentation.v]），这种空性会降到每一个呈现的商（[no_linear_fanout_presented] / [no_linear_discard_presented]）。这是线性数据流语言的类型级展开检查的范畴内容：一个不符合线性的插入不会被重写掉——它是无法表示的。- 置换不变。在无生成元的签名上，计数不变量被加强：每个项的输出边界都是其输入边界的一个置换（[structural_permutation]）。这是一个关于边界的单向、命题层次的必要条件——它不为项分配任何置换，也不证明任何逆向可实现性——是“无生成元的自由彩色 PROP 是彩色置换群体”（参见 [Empty_CSig] 在 [Construction/ColouredPROP/Signature.v] 中）的必要条件影子，本身未在此处形式化。- 正半部分（在可复制颜色上的分叉）。相反，一个可复制颜色是其线对象携带交换余单元的颜色：选择性提供 [Construction/ColouredPROP/Supply.v]，其每颜色的单个原语 [supply_wire] 在 [copyable c = true] 条件下为 [wire c] 装备其余单元。其余积是一个分叉态射 [wire c ~> wire c ⨂ wire c]（[copyable_fanout]），其余单位是丢弃 [wire c ~> I]（[copyable_discard]）——这是空性定理的逆，也是 [copyable] 是线性纪律正确界限的原因。相对于从原始对象导出的边界供给 [supply_list] 到 [Supply.v]（通过 [Theory/Algebra/Comonoid/Tensor.v] 张量化线性余单元；没有假定边界级别的内容），所有可复制边界之间的态射在它们之间是余单元同态（[sel_deterministic]）时是确定性的——两个 Cho–Jacobs 复制/丢弃保持方形图

 scopy ds Hd ∘ f    ≈ (f ⨂ f) ∘ scopy cs Hc
 sdiscard ds Hd ∘ f ≈ sdiscard cs Hc( [sel_deterministic_scopy] / [sel_deterministic_sdiscard] ), 由 [ComonoidHom] 类的 [Theory/Algebra/Comonoid/Hom.v] 打包，其套件提供身份/构成/尊重法则 ( [sel_deterministic_id] / [sel_deterministic_comp] / [sel_deterministic_equiv] )。确定性谓词在编织/对称单体路径 [MBc P] 上陈述，供应的余单对象存在其中（参见 [Supply.v] 中的 MP/MB 调解说明）。建立在此谓词上的线性/非线性桥存在于 [Construction/ColouredPROP/LNL.v]。参考文献：
 - Cho & Jacobs，《通过弦图的解体与贝叶斯反演》，MSCS 29(7):938-971, 2019 (arXiv:1709.00322) — 决定论作为余单体同态。
 - Fong & Spivak，《在对称幺半范畴中提供铃铛和口哨》(arXiv:1908.02633) — 交换余单体的提供。
 - Bonchi, Sobocinski & Zanasi，《信号流图的范畴语义》— 彩色 PROP 作为带类型的图语言。
*)

(* * ** The negative half: conservativity and hom-emptiness / * ** 消极的一面：保守性与同质空虚 *)

Section LinearDiscipline.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (S : CSignature Colour).
Context (copyable : Colour -> bool).

(** A colour is linear when it is not copyable. / 当一种颜色不可复制时，它是线性的。 *)
Definition LinearColour (c : Colour) : Prop := copyable c = false.

(*
   * A signature is conservative at [c] when every generator carries as
   many [c]-coloured wires in as out.  [Type]-valued: downstream
   positive-half files may need to eliminate it into data. 

   --------
   * 当每个发生器传出和传入的 [c] 颜色的电线数量相同时，[c] 上的签名是保守的。[Type] 数值：下游的正半文件可能需要将其消除到数据中。
*)
Definition c_conservative (c : Colour) : Type :=
  forall (cs ds : list Colour) (g : S cs ds),
    count_occ Cdec cs c = count_occ Cdec ds c.

(*
   * The linear discipline for a whole signature: conservativity at
   every linear colour.  Copyable colours are unconstrained — their
   generators (e.g. explicit duplicators) may change wire counts. 

   --------
   * 整个签名的线性约束：在每种线性颜色下保持保守性。可复制的颜色没有限制——它们的生成器（例如显式复制器）可以改变导线数量。
*)
Definition LinearRespecting : Type :=
  forall c : Colour, LinearColour c -> c_conservative c.

(*
   * *** The occurrence invariant

   Per-colour wire counts are invariant under all five term formers:
   identities and composites trivially, the block braid and the
   tensor because [count_occ] distributes over [++]
   ([count_occ_app]), and generators by conservativity.  This is the
   whole-diagram consequence of the local counting discipline. 

   --------
   * *** 出现不变式

   在所有五种项形成器下，每种颜色的线数量都是不变的：
   对恒等和复合而言显然如此，对块编织和张量而言，
   因为  [count_occ] 分配在  [++]（[count_occ_app]）上，
   对生成元则通过保守性成立。这是局部计数规
   律的整个图的结果。
*)

Lemma cterm_count_occ (c : Colour) (Hgen : c_conservative c)
  {cs ds : list Colour} (t : CTerm S cs ds) :
  count_occ Cdec cs c = count_occ Cdec ds c.
Proof.
  induction t as [xs | xs ys | xs ys zs g IHg f IHf
                 | xs1 ys1 xs2 ys2 f IHf g IHg | xs ys g];
  simpl.
  - (* CT_id *) reflexivity.
  - (* CT_braid: both boundaries are the same two blocks, swapped / CT_braid：两个边界是相同的两个区块，互换了 *)
    rewrite !count_occ_app; apply Nat.add_comm.
  - (* CT_comp: paste the two invariants / CT_comp：粘贴这两个不变量 *)
    etransitivity; eauto.
  - (* CT_tens: counts add across [++] / CT_tens：计数在 [++] 上相加 *)
    rewrite !count_occ_app; congruence.
  - (* CT_gen: conservativity of the signature / CT_gen：签名的保守性 *)
    exact (Hgen _ _ g).
Qed.

(*
   * *** Hom-emptiness at conservative colours

   No term can fan a conservative wire out ([1 <> 2]) or discard it
   ([1 <> 0]).  These are statements about the TYPE of raw terms:
   the free hom-setoid at these boundaries is empty outright, which
   is strictly stronger than emptiness up to [CTermEq]. 

   --------
   * *** 保守颜色下的同-空性

   没有术语可以扇出一个保守的线圈 ([1 <> 2]) 或将其丢弃 ([1 <> 0])。这些是关于原始术语类型的声明：在这些边界处的自由同集合是完全空的，这比直到 [CTermEq] 的空性严格更强。
*)

Theorem no_linear_fanout (c : Colour) (Hgen : c_conservative c) :
  CTerm S [c] [c; c] -> False.
Proof.
  intro t.
  pose proof (cterm_count_occ c Hgen t) as H.
  simpl in H.
  destruct (Cdec c c) as [_ | n] in H.
  - discriminate H.
  - exact (n eq_refl).
Qed.

Theorem no_linear_discard (c : Colour) (Hgen : c_conservative c) :
  CTerm S [c] [] -> False.
Proof.
  intro t.
  pose proof (cterm_count_occ c Hgen t) as H.
  simpl in H.
  destruct (Cdec c c) as [_ | n] in H.
  - discriminate H.
  - exact (n eq_refl).
Qed.

(*
   * The bundled forms: under the linear discipline, every LINEAR
   colour has empty fan-out and discard homs. 

   --------
   * 捆绑形式：在线性范畴下，每个线性颜色都有空分叉并丢弃同态。
*)

Corollary linear_no_fanout (HL : LinearRespecting)
  (c : Colour) (Hc : LinearColour c) :
  CTerm S [c] [c; c] -> False.
Proof. exact (no_linear_fanout c (HL c Hc)). Qed.

Corollary linear_no_discard (HL : LinearRespecting)
  (c : Colour) (Hc : LinearColour c) :
  CTerm S [c] [] -> False.
Proof. exact (no_linear_discard c (HL c Hc)). Qed.

(*
   * *** The permutation invariant of the structural fragment

   Over a generator-free signature the invariant sharpens from
   per-colour counting to boundary relatedness: every term's output
   boundary is a permutation of its input boundary.  Identities are
   reflexivity, the block braid is [Permutation_app_comm], and
   composition/tensor are transitivity/congruence of
   [Permutation]. 

   --------
   * *** 结构片段的排列不变性

   在无生成子符号的签名上，该不变性从按颜色计数细化为边界相关性：每个项的输出边界是其输入边界的一个排列。恒等式是自反性的，块编织为 [Permutation_app_comm]，组合/张量是 [Permutation] 的传递性/相容性。
*)

Theorem structural_permutation
  (Hempty : forall cs ds : list Colour, S cs ds -> False)
  {cs ds : list Colour} (t : CTerm S cs ds) :
  Permutation cs ds.
Proof.
  induction t as [xs | xs ys | xs ys zs g IHg f IHf
                 | xs1 ys1 xs2 ys2 f IHf g IHg | xs ys g].
  - apply Permutation_refl.
  - apply Permutation_app_comm.
  - eapply Permutation_trans; eauto.
  - apply Permutation_app; auto.
  - destruct (Hempty _ _ g).
Qed.

End LinearDiscipline.

Arguments LinearColour {Colour} copyable c : assert.
Arguments c_conservative {Colour} Cdec S c : assert.
Arguments LinearRespecting {Colour} Cdec S copyable : assert.
Arguments cterm_count_occ {Colour} Cdec S c Hgen {cs ds} t : assert.
Arguments no_linear_fanout {Colour} Cdec S c Hgen _ : assert.
Arguments no_linear_discard {Colour} Cdec S c Hgen _ : assert.
Arguments linear_no_fanout {Colour} Cdec S copyable HL c Hc _ : assert.
Arguments linear_no_discard {Colour} Cdec S copyable HL c Hc _ : assert.
Arguments structural_permutation {Colour} S Hempty {cs ds} t : assert.

(*
   * ** Presented transfer

   A presented coloured PROP ([Construction/ColouredPROP/
   Presentation.v]) has THE SAME morphisms as the free category —
   [CPresentedCat E] is a [Quotient], which keeps [hom] on the nose
   and only coarsens the equivalence — so hom-emptiness transfers
   verbatim: both corollaries are [exact] applications of the free
   theorems at [CTerm (csmt_sig E)].  No quotient can create a
   fan-out at a conservative colour, whatever its axioms. 

   --------
   * ** 已呈现的迁移

   已呈现的彩色 PROP ([Construction/ColouredPROP/Presentation.v]) 具有与自由范畴相同的态射——[CPresentedCat E] 是一个 [Quotient]，它精确保持 [hom]，只是粗化了等价关系——因此同态空性逐字迁移：两个推论都是 [exact] 对自由定理在 [CTerm (csmt_sig E)] 的应用。没有任何商可以在保守颜色上创建分叉，无论其公理为何。
*)

Section LinearPresented.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (E : CSMT Colour).

Corollary no_linear_fanout_presented (c : Colour)
  (Hgen : c_conservative Cdec (csmt_sig E) c) :
  ([c] ~{CPresentedCat E}~> [c; c]) -> False.
Proof. exact (no_linear_fanout Cdec (csmt_sig E) c Hgen). Qed.

Corollary no_linear_discard_presented (c : Colour)
  (Hgen : c_conservative Cdec (csmt_sig E) c) :
  ([c] ~{CPresentedCat E}~> []) -> False.
Proof. exact (no_linear_discard Cdec (csmt_sig E) c Hgen). Qed.

End LinearPresented.

Arguments no_linear_fanout_presented {Colour} Cdec E c Hgen _ : assert.
Arguments no_linear_discard_presented {Colour} Cdec E c Hgen _ : assert.

(*
   * ** Machine-checked sanity: the empty signature

   [Empty_CSig] is conservative at every colour (its generator type
   is [Empty_set]), so with all colours declared linear it respects
   the linear discipline, its fan-out homs are empty, and every one
   of its terms has output boundary a permutation of its input
   boundary. 

   --------
   * ** 机器检查的合理性：空签名

   [Empty_CSig] 在每种颜色下都是保守的（其生成器类型为 [Empty_set]），因此当所有颜色声明为线性时，它遵循线性规则，其扇出同态为空，并且其每个项的输出边界都是其输入边界的一个排列。
*)

Example Empty_CSig_conservative {Colour : Type}
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) (c : Colour) :
  c_conservative Cdec Empty_CSig c :=
  fun _ _ g => match g with end.

Example Empty_CSig_linear_respecting {Colour : Type}
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) :
  LinearRespecting Cdec Empty_CSig (fun _ : Colour => false) :=
  fun c _ => Empty_CSig_conservative Cdec c.

Example Empty_CSig_no_fanout {Colour : Type}
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) (c : Colour) :
  CTerm Empty_CSig [c] [c; c] -> False :=
  no_linear_fanout Cdec Empty_CSig c (Empty_CSig_conservative Cdec c).

Example Empty_CSig_structural_permutation {Colour : Type}
  {cs ds : list Colour} (t : CTerm (@Empty_CSig Colour) cs ds) :
  Permutation cs ds :=
  structural_permutation Empty_CSig (fun _ _ g => match g with end) t.

(*
   * ** The positive half: fan-out at copyable colours

   At an arbitrary coloured PROP [P] with a selective supply
   ([Construction/ColouredPROP/Supply.v]), every copyable wire
   carries honest fan-out and discard morphisms, and determinism at
   all-copyable boundaries is comonoid homomorphy for the derived
   supplies.  Everything is stated on the braided/symmetric monoidal
   path [MBc P], where the supply comonoids live. 

   --------
   * ** 正半部分：可复制颜色的分叉

   在具有选择性供应（[Construction/ColouredPROP/Supply.v]）的任意彩色 PROP [P] 上，每条可复制的线路都携带真实的分叉和丢弃态射，并且在所有可复制边界处的确定性是派生供应的余模同态。在扎伊姆/对称单体路径 [MBc P] 上陈述了一切，其中供应余模存在。
*)

Section SelectiveFanOut.

Context {Colour : Type}.
Context {P : ColouredPROP Colour}.
Context {copyable : Colour -> bool}.
Context `{SS : @SelectiveSupply Colour P copyable}.

Notation "⟦ cs ⟧c" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧c").

(*
   * *** Fan-out and discard at a copyable wire

   The comultiplication and counit of the wire supply, read as
   morphisms of [P]: the positive converses of [no_linear_fanout]
   and [no_linear_discard]. 

   --------
   * *** 在可复制的线上的分支和丢弃

   线的余乘和余单位被读取为 [P] 的态射：[no_linear_fanout] 和 [no_linear_discard] 的正反映。
*)

Definition copyable_fanout {c : Colour} (H : copyable c = true) :
  wire (P := P) c ~{P}~>
    ((wire (P := P) c ⨂[MBc P] wire (P := P) c)%object) :=
  @ccomon_delta P (@cprop_symmetric Colour P) (wire (P := P) c)
    (@supply_wire Colour P copyable SS c H).

Definition copyable_discard {c : Colour} (H : copyable c = true) :
  wire (P := P) c ~{P}~> @I P (MBc P) :=
  @ccomon_epsilon P (@cprop_symmetric Colour P) (wire (P := P) c)
    (@supply_wire Colour P copyable SS c H).

(*
   * *** Determinism at all-copyable boundaries

   Relative to the derived boundary supplies [supply_list], a
   morphism is DETERMINISTIC when it is a comonoid homomorphism
   between them — the two Cho–Jacobs preservation squares, packaged
   by [ComonoidHom].  The [ComonoidHom] kit of
   [Theory/Algebra/Comonoid/Hom.v] instantiates to the expected laws:
   identities are deterministic, deterministic morphisms compose, and
   determinism respects [≈]. 

   --------
   * *** 在所有可复制边界上的确定性

   相对于派生边界供应  [supply_list]，当一个态射在它们之间是一个余单元同态时——由  [ComonoidHom] 封装的两个 Cho–Jacobs 保持平方——它就是确定性的。  [ComonoidHom] 工具包中的  [Theory/Algebra/Comonoid/Hom.v]  实例化为预期定律：恒等式是确定性的，确定性态射可以组合，并且确定性遵循  [≈] 。
*)

Definition sel_deterministic {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) : Type :=
  @ComonoidHom P (MBc P) ⟦cs⟧c ⟦ds⟧c
    (@ccomon_comonoid P (@cprop_symmetric Colour P) ⟦cs⟧c
       (@supply_list Colour P copyable SS cs Hc))
    (@ccomon_comonoid P (@cprop_symmetric Colour P) ⟦ds⟧c
       (@supply_list Colour P copyable SS ds Hd))
    f.

Lemma sel_deterministic_id {cs : list Colour}
  (Hc : all_copyable copyable cs) :
  sel_deterministic Hc Hc (@id P ⟦cs⟧c).
Proof.
  exact (@ComonoidHom_id P (MBc P) ⟦cs⟧c
           (@ccomon_comonoid P (@cprop_symmetric Colour P) ⟦cs⟧c
              (@supply_list Colour P copyable SS cs Hc))).
Qed.

Lemma sel_deterministic_comp {cs ds es : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (He : all_copyable copyable es)
  (f : ⟦ds⟧c ~{P}~> ⟦es⟧c) (g : ⟦cs⟧c ~{P}~> ⟦ds⟧c) :
  sel_deterministic Hd He f ->
  sel_deterministic Hc Hd g ->
  sel_deterministic Hc He (f ∘ g).
Proof.
  exact (@ComonoidHom_comp P (MBc P) ⟦cs⟧c ⟦ds⟧c ⟦es⟧c _ _ _ f g).
Qed.

Lemma sel_deterministic_equiv {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f g : ⟦cs⟧c ~{P}~> ⟦ds⟧c) :
  f ≈ g -> sel_deterministic Hc Hd f -> sel_deterministic Hc Hd g.
Proof.
  exact (@ComonoidHom_equiv P (MBc P) ⟦cs⟧c ⟦ds⟧c _ _ f g).
Qed.

(*
   * The two Cho–Jacobs squares, projected out in the copy/discard
   vocabulary of [Supply.v]: copying after [f] is running [f] twice
   on a copy, and discarding after [f] is discarding. 

   --------
   * 两个 Cho–Jacobs 正方形，在 [Supply.v] 的复制/丢弃词汇中投影：在复制后 [f] 正在对一个副本运行 [f] 两次，而在 [f] 之后丢弃就是丢弃。
*)

Lemma sel_deterministic_scopy {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) :
  sel_deterministic Hc Hd f ->
  @scopy Colour P copyable SS ds Hd ∘ f
    ≈ (f ⨂[MBc P] f) ∘ @scopy Colour P copyable SS cs Hc.
Proof.
  intro D.
  exact (@hom_delta P (MBc P) ⟦cs⟧c ⟦ds⟧c _ _ f D).
Qed.

Lemma sel_deterministic_sdiscard {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) :
  sel_deterministic Hc Hd f ->
  @sdiscard Colour P copyable SS ds Hd ∘ f
    ≈ @sdiscard Colour P copyable SS cs Hc.
Proof.
  intro D.
  exact (@hom_epsilon P (MBc P) ⟦cs⟧c ⟦ds⟧c _ _ f D).
Qed.

End SelectiveFanOut.

Arguments copyable_fanout {Colour P copyable SS c} H : assert.
Arguments copyable_discard {Colour P copyable SS c} H : assert.
Arguments sel_deterministic {Colour P copyable SS cs ds} Hc Hd f : assert.
Arguments sel_deterministic_id {Colour P copyable SS cs} Hc : assert.
