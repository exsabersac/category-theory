Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Two.

Generalizable All Variables.

Open Scope category_scope.

(** * Probe: the measured boundaries of Structure/Limit/FromProducts.v / * 探测器：Structure/Limit/FromProducts.v 的测量边界 *)

(*
Companion to Structure/Limit/FromProducts.v (Mac Lane, Categories for
   the Working Mathematician, 2nd ed., §V.2 Theorems 1 and 2, Corollary 2,
   §V.4 Exercise 2; Riehl, Category Theory in Context, 2nd ed., Theorems
   3.2.11 and 3.5.11, Exercise 3.2.ii).  Everything that file claims at
   [eq_refl] is shipped there as an [Example]; what it cannot guard from
   inside are the REFUSALS its header records and the universe boundaries
   a consumer meets.  Those are pinned here, from OUTSIDE the target,
   because an in-file [Fail] renames in lockstep with the constant it
   guards and so cannot detect a rename.  The [Sets] instantiation and the
   walking-arrow generating family live here too, because they cost
   modules the target should not carry.

   The negatives are of THREE kinds, told apart by the error TEXT — the
   kinds were read off the messages produced by stripping each [Fail] in
   turn, in a copy of this WHOLE file — plus one scope-free instrument
   check.

     N1  CONVERSION  The refinement at the FULL arrow index is the
                   construction in apex and in every leg (three controls
                   at [eq_refl]) but NOT as a cone RECORD: the coherence
                   field of [pe_cone] mentions the two component lemmas
                   [Hs] and [Ht], and the [Refinement] section's
                   [pe_gen_s_proj]/[pe_gen_t_proj] are different [Qed]
                   constants from [pe_s_proj]/[pe_t_proj].
     N2  CONVERSION  A leg of [pe_image_cone] is [fmap[G] proj ∘ fmap[G] e]
                   while the leg of [FCone G (pe_limit_cone …)] is
                   [fmap[G] (proj ∘ e)] — one [fmap_comp] apart, which
                   [fmap_comp] being a law FIELD does not convert; the
                   apex is the control.  This is why the target transports
                   along [pe_image_ConeIso] rather than ascribing.
     N3  CONVERSION  The two cones of N2 as whole records.
     N4  TYPING    [Complete_from_products_equalizers] fed a
                   [HasCoequalizers] where it asks for [HasEqualizers]: a
                   plain has-type mismatch with no [cannot unify] clause
                   and no universe clause.
     N5  TYPING    [Cocomplete_from_coproducts_coequalizers] fed the
                   products-and-equalizers pair: [HasIndexedProducts C] is
                   not [HasIndexedCoproducts C] — the latter is that class
                   at [C^op], and [C] is not [C^op] on the nose.
     N6  UNIVERSE  At a category whose hom level is declared strictly BELOW
                   its proof level, the hom-set, the identity and an
                   endofunctor are ACCEPTED while [HasIndexedProducts],
                   [HasEqualizers], [IsIndexedProduct], [IsEqualizer],
                   [Limit] and [Complete] are each refused ALONE — six
                   donors of the hom = proof identification every binder
                   in the target carries, none introduced there.
     N7  UNIVERSE  At a shape whose homs are declared strictly BELOW the
                   ambient category's, the diagram, a [Cone] over it and
                   the arrow index [ArrowIx] are ACCEPTED while [Limit]
                   and [IsLimitCone] are refused — the shape-hom =
                   ambient-hom identification is the limit vocabulary's.
                   [pe_cone] is refused there too, at its AMBIENT
                   argument [Cu] with the same [Cannot enforce ch = jh]
                   (no argument of it is already refused: [Fu], [Cone Ju
                   Cu Fu] and [ArrowIx Ju] all pass): the identification
                   sits in [pe_cone]'s OWN binder, [{J : Category@{u u0
                   u0}} {C : Category@{u1 u0 u0}}], whose donor is not
                   isolated here, and since [Cone] is accepted at those
                   levels this refusal corroborates nothing about the
                   attribution to [Limit]/[IsLimitCone].  (An earlier
                   draft said it fired at the diagram argument; an audit
                   stripped the command and read the message.)
     N8  REPAIRED, and recorded as a correction.  An earlier revision read:
                   "UNIVERSE  At a category whose hom level is declared
                   strictly above [Set], the class [HasIndexedProducts],
                   its [indexed_product] and
                   [Complete_from_products_equalizers] are ACCEPTED while
                   [iprod] — the discrete-diagram presentation the issue's
                   work item 4 asks the construction to route through — is
                   refused with [Cannot enforce Set = ch]: [iprod]'s binder
                   is [C : Category@{_ Set Set}] through
                   [DiscreteCat_Functor] and [Limit].  This is the measured
                   reason the target is stated over the CLASS and never
                   over [iprod]."

                   The attribution was correct and the defect is fixed.
                   [iprod] was never [Set]-pinned in itself; it inherited
                   the pin from [DiscreteCat_Functor], declared with bare
                   binders and minimized to [DiscreteCat@{u Set Set}].
                   Annotated in place in the PR "algebraic carriers are
                   sets" (2026-09-17) — Instance/Discrete.v — [iprod] is
                   ACCEPTED at those levels, and the line below is kept as
                   a positive control there.  So the count of UNIVERSE
                   negatives in this file is now two (N6 and N7), not
                   three.  The target is still stated over the CLASS, but
                   that is now a presentational choice rather than a
                   universe obligation.

   Every constant a negative names also appears in a [Check] outside every
   [Fail], so a rename breaks this file loudly instead of turning a [Fail]
   vacuously green.

--------
Structure/Limit/FromProducts.v 的伴随说明（Mac Lane，《为在职数学家而写的范畴论》，第2版，§V.2 定理1和2，推论2，§V.4 练习2；Riehl，《语境中的范畴论》，第2版，定理3.2.11和3.5.11，练习3.2.ii）。 文件在 [eq_refl] 所声明的所有内容都作为 [Example] 发布；它无法在文件内部防护的是其头部记录的拒绝（REFUSALS）以及使用者遭遇的宇宙边界。 这些内容从目标之外固定在这里，因为文件内的 [Fail] 会随着它所保护的常量同步重命名，因此无法检测重命名。 [Sets] 的实例化和生成步进箭头的族也在这里，因为它们会消耗目标模块不应承载的成本。

消极因素有三种，通过错误文本加以区分——这些种类是通过在整个文件的副本中依次剥离每个 [Fail] 所产生的消息中读取的——外加一次无范围仪器检查。

N1 转换 在 FULL 箭头索引处的精炼是在顶点和每条腿（[eq_refl] 的三个控制）中的构造，但不是作为圆锥记录：[pe_cone] 的相干场提到了两个组成引理 [Hs] 和 [Ht]，而 [Refinement] 部分的 [pe_gen_s_proj]/[pe_gen_t_proj] 与 [pe_s_proj]/[pe_t_proj] 是不同的 [Qed] 常量。 N2 转换 [pe_image_cone] 的一条腿是 [fmap[G] proj ∘ fmap[G] e]，而 [FCone G (pe_limit_cone …)] 的腿是 [fmap[G] (proj ∘ e)] — 相隔一个 [fmap_comp]，[fmap_comp] 作为一个律场不会转换；顶点是控制。这就是为什么目标沿 [pe_image_ConeIso] 传输而不是被归属的原因。
N3  转换  N2 的两个圆锥作为整体记录。 N4  类型检查  [Complete_from_products_equalizers] 输入了 [HasCoequalizers]，在它要求 [HasEqualizers] 的地方：一个普通的 has-type 不匹配，没有 [cannot unify] 子句，也没有 universe 子句。 N5  类型检查  [Cocomplete_from_coproducts_coequalizers] 输入了积和余等对：[HasIndexedProducts C] 不是 [HasIndexedCoproducts C] ——后者是在 [C^op] 的那个类，而 [C] 并不是正好是 [C^op]。
N6 宇宙 在一个其同态层严格低于其证明层的范畴中，同态集合、恒等映射和一个函子被接受，而 [HasIndexedProducts]、[HasEqualizers]、[IsIndexedProduct]、[IsEqualizer]、[Limit] 和 [Complete] 都会单独被拒绝——每个目标携带的绑定器都有六个同态=证明识别的捐赠者，但它们没有在那里引入。 
N7 宇宙 在一个其同态严格低于环境范畴的形状中，图、其上的 [Cone] 和箭头索引 [ArrowIx] 被接受，而 [Limit] 和 [IsLimitCone] 被拒绝——形状同态=环境同态的识别是极限词汇。
[pe_cone]在那里也被拒绝，在其AMBIENT参数[Cu]上，具有相同的[Cannot enforce ch = jh]（没有任何参数已经被拒绝：[Fu]，[Cone Ju Cu Fu] 和[ArrowIx Ju]都通过）：该识别位于[pe_cone]自己的绑定器中，[{J : Category@{u u0 u0}} {C : Category@{u1 u0 u0}}]，其捐赠者此处未被孤立，并且因为[Cone]在这些层级上被接受，这种拒绝并未证明对[Limit]/[IsLimitCone]的归属。(早期的草稿说它在图表参数上触发；审核去掉了该命令并读取了消息。) N8 已修复，并记录为纠正。
早期的修订版本写道：
                   “宇宙  在类别中，其同源层级被声明为
                   严格高于 [Set]，类 [HasIndexedProducts]、
                   其 [indexed_product] 和
                   [Complete_from_products_equalizers] 被接受，而
                   [iprod] —— 离散图展示该问题的
                   工作项 4 要求构造经过 —— 被拒绝，原因是 [Cannot enforce Set = ch]：[iprod] 的绑定器
                   通过 [DiscreteCat_Functor] 和 [Limit] 是 [C : Category@{_ Set Set}]。 这是目标声明在 CLASS 上而不是
                   [iprod] 上的衡量理由。”

归属是正确的，缺陷已修复。[iprod] 本身从未被 [Set] 固定；它继承了来自 [DiscreteCat_Functor] 的固定，后者用裸绑定器声明并最小化到 [DiscreteCat@{u Set Set}]。在 PR “代数载体是集合”（2026-09-17）中已就地注释 — Instance/Discrete.v — [iprod] 在这些层级上被接受，并且下面的行被保留作为正控制。因此，该文件中的 UNIVERSE 负例计数现在为两个（N6 和 N7），而不是三个。目标仍然是针对 CLASS 陈述，但现在这是一个展示上的选择，而不是宇宙义务。

每个常量负名称也出现在每个 [Fail] 之外的 [Check] 中，因此重命名会明显破坏此文件，而不是使 [Fail] 空洞地变为绿色。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Check probe416_no_such_constant.

(** ** Guards *)

Check @limit_of_products_equalizer.
Check @Complete_from_products_equalizers.
Check @Cocomplete_from_coproducts_coequalizers.
Check @continuous_from_products_equalizers.
Check @pe_cone.
Check @pe_limiting.
Check @pe_limit_cone.
Check @pe_gen_cone.
Check @pe_gen_apex.
Check @pe_apex.
Check @pe_image_cone.
Check @pe_image_ConeIso.
Check @ArrowIx.
Check @ArrowIx_Generates.
Check @Generates.
Check @Gen.
Check @gen_id.
Check @gen_idx.
Check @IsIdArrow.
Check @is_id_arrow.
Check @nonid_Generates.
Check @pe_gen_restrict_iso.
Check @HasIndexedProducts.
Check @HasIndexedCoproducts.
Check @HasEqualizers.
Check @HasCoequalizers.
Check @IsIndexedProduct.
Check @IsEqualizer.
Check @indexed_product.
Check @iprod.
Check @Limit.
Check @IsLimitCone.
Check @Cone.
Check @Complete.
Check @FCone.
Check @cone_leg.
Check @vertex_obj.

(** ** N1: the refinement at the full index / ** N1：全索引的精炼 *)

Section FullIndex.

Context {C : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context {J : Category} (F : J ⟶ C).

(* Controls: apex, apex object and every leg agree on the nose. / 控制：顶点、顶点对象和每条腿都在鼻子上对齐。 *)
Example probe416_ctrl_full_apex :
  vertex_obj[pe_gen_cone HP HE F ArrowIx_Generates]
    = vertex_obj[pe_limit_cone HP F HE] := eq_refl.

Example probe416_ctrl_full_apex_obj :
  pe_gen_apex HP HE F (idx_arr := @aix_arr J) = pe_apex HP F HE := eq_refl.

Example probe416_ctrl_full_leg (x : J) :
  cone_leg (pe_gen_cone HP HE F ArrowIx_Generates) x
    = cone_leg (pe_limit_cone HP F HE) x := eq_refl.

(* N1: CONVERSION — not as records. / N1：转换——不是作为记录。 *)
Fail Example probe416_n1 :
  pe_gen_cone HP HE F ArrowIx_Generates = pe_limit_cone HP F HE := eq_refl.

(* The delivered limit's cone IS the constructed cone. / 所给极限的圆锥就是所构造的圆锥。 *)
Example probe416_ctrl_limit_cone :
  @limit_cone _ _ _ (limit_of_products_equalizer HP F HE)
    = pe_limit_cone HP F HE := eq_refl.

Example probe416_ctrl_complete_cone :
  @limit_cone _ _ _ (Complete_from_products_equalizers HP HE J F)
    = pe_limit_cone HP F HE := eq_refl.

End FullIndex.

(** ** N2, N3: the image cone against the image of the cone / ** N2，N3：圆锥的像与圆锥的像相对 *)

Section Image.

Context {C D : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context (G : C ⟶ D) (GP : PreservesIndexedProducts G)
  (GE : PreservesEqualizers G).
Context {J : Category} (K : J ⟶ C).

(* Control: the apexes agree. / 控制：顶点一致。 *)
Example probe416_ctrl_image_apex :
  vertex_obj[pe_image_cone HP HE G GP GE K]
    = vertex_obj[FCone G (pe_limit_cone HP K HE)] := eq_refl.

(* N2: CONVERSION — a leg is one [fmap_comp] away. / N2：转换——一条腿只需一个 [fmap_comp]。 *)
Fail Example probe416_n2 (x : J) :
  cone_leg (pe_image_cone HP HE G GP GE K) x
    = cone_leg (FCone G (pe_limit_cone HP K HE)) x := eq_refl.

(* N3: CONVERSION — the whole records. / N3：转换——完整记录。 *)
Fail Example probe416_n3 :
  pe_image_cone HP HE G GP GE K = FCone G (pe_limit_cone HP K HE) := eq_refl.

(* Control: the transport the target ships. / 控制：运输目标船只。 *)
Check (pe_image_ConeIso HP HE G GP GE K).

End Image.

(** ** N4, N5: the hypotheses are the ones named / ** N4，N5：假设就是那些被命名的假设 *)

Section Handedness.

Context {C : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context (HC : HasIndexedCoproducts C) (HQ : HasCoequalizers C).

(* Controls. / 控制。 *)
Check (Complete_from_products_equalizers HP HE).
Check (Cocomplete_from_coproducts_coequalizers HC HQ).

(* N4: TYPING. *)
Fail Check (Complete_from_products_equalizers HP HQ).

(* N5: TYPING. *)
Fail Check (Cocomplete_from_coproducts_coequalizers HP HE).

End Handedness.

(** ** N6: hom = proof, six donors / ** N6：hom = 证明，六位捐赠者 *)

Section HomProof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}) (x y : Cu) (f : x ~> y).

(* Controls. / 控制。 *)
Check (x ~> y).
Check (id[x]).
Check (@Functor Cu Cu).

Fail Check (@HasIndexedProducts Cu).
Fail Check (@HasEqualizers Cu).
Fail Check (@IsIndexedProduct Cu).
Fail Check (@IsEqualizer Cu x y f f).
Fail Check (@Limit Cu).
Fail Check (@Complete Cu).

End HomProof.

(** ** N7: shape hom = ambient hom, the limit vocabulary's / ** N7：形状同构 = 环境同构，极限词汇的 *)

Section ShapeHom.

Universes jo jh co ch.
Constraint jh < ch.

Context (Ju : Category@{jo jh jh}) (Cu : Category@{co ch ch}).
Context (Fu : Ju ⟶ Cu).

(* Controls. / 控制。 *)
Check Fu.
Check (@Cone Ju Cu Fu).
Check (@ArrowIx Ju).

Fail Check (@Limit Ju Cu Fu).
Fail Check (@IsLimitCone Ju Cu Fu).

(* Inherited: fires at the diagram argument [Fu]. / 继承：在图表参数 [Fu] 上触发。 *)
Fail Check (@pe_cone Ju Cu Fu).

End ShapeHom.

(**
** Former N8: the [iprod] route is no longer pinned to [Set]

    RECORDED CORRECTION: this section held the file's third UNIVERSE
    negative, refused because [DiscreteCat_Functor] was unannotated
    ([DiscreteCat@{u Set Set}]).  Annotated in the PR "algebraic carriers
    are sets" (2026-09-17) it is accepted; the line is kept as a positive
    control at the same levels, so dropping the annotation breaks this
    file.

--------
** 前N8：[iprod]路线不再固定到[Set]

记录的更正：该部分包含文件的第三个UNIVERSE
负数，由于[DiscreteCat_Functor]未注释而被拒绝
（[DiscreteCat@{u Set Set}]）。在PR“代数载体是集合”（2026-09-17）中已注释，因此被接受；该行保持为相同级别的正控制，因此删除注释会破坏此文件。
*)

Section AboveSet.

Universes co ch.
Constraint Set < ch.

Context (Cu : Category@{co ch ch}).
Context (HP : HasIndexedProducts Cu) (HE : HasEqualizers Cu).

(* Controls. / 控制。 *)
Check HP.
Check (@indexed_product Cu HP).
Check (@Complete_from_products_equalizers Cu HP HE).

(* Former N8, now a positive control. / 前N8，现在是阳性对照。 *)
Check (@iprod Cu).

End AboveSet.

(** ** The [Sets] instantiation / ** [Sets] 实例化 *)

(*
Riehl's Theorem 3.2.11 is the general theorem at [Sets]: a SECOND
   inhabitant of [@Complete Sets] beside Instance/Sets/Complete.v's
   [Sets_Complete], NOT compared with it — and built WITHOUT it.  The
   products are Instance/Sets/Products.v's [Sets_HasIndexedProducts] and
   the equalizers are [HasEqualizers_of_HasPullbacks_Terminal] at
   Instance/Sets/Pullback.v's [Sets_HasPullbacks] (the route
   Adjunction/CokernelPair.v takes), so Instance/Sets/Complete.v is
   absent from this file's closure (coqdep: 47 modules).  The obvious
   supply, Adjunction/GAFT/Sets.v's [Sets_HasEqualizers], would NOT do:
   it is [Complete_HasEqualizers Sets_Complete], equalizers read off the
   very inhabitant this one stands beside — an audit caught a first
   draft that used it while calling the two "independent".

--------
Riehl 定理 3.2.11 是 [Sets] 的一般定理：[@Complete Sets] 的第二个元素，位于 Instance/Sets/Complete.v 的 [Sets_Complete] 旁边，而不是与其比较 — 并且是在没有它的情况下构建的。积是 Instance/Sets/Products.v 的 [Sets_HasIndexedProducts]，等化器是 Instance/Sets/Pullback.v 的 [HasEqualizers_of_HasPullbacks_Terminal]（Adjunction/CokernelPair.v 所走的路径），所以 Instance/Sets/Complete.v 在此文件的闭包中缺失（coqdep：47 个模块）。显而易见的补充，Adjunction/GAFT/Sets.v 的 [Sets_HasEqualizers]，是行不通的：它是 [Complete_HasEqualizers Sets_Complete]，等化器从这个元素旁边的那个元素读出 — 审核发现了一个草稿，它在使用它的同时将两者称为“独立”。
*)

Definition sets_pe_complete : @Complete Sets :=
  Complete_from_products_equalizers Sets_HasIndexedProducts
    (HasEqualizers_of_HasPullbacks_Terminal Sets_HasPullbacks).

Check sets_pe_complete.

(** ** A generating family on the walking arrow / ** 步行箭上的生成族 *)

(*
Riehl's Exercise 3.2.ii, non-vacuously: [_2] has three arrows, and the
   family with ONE index — the non-identity arrow — generates.  So the
   refined arrow product is indexed by [unit] where the full one is
   indexed by [ArrowIx _2].

--------
Riehl 的练习 3.2.ii，非空地：[_2] 有三条箭头，并且具有一个索引的族 —— 非恒等箭头 —— 可以生成。因此，精炼的箭头积由 [unit] 索引，而完整的箭头积由 [ArrowIx _2] 索引。
*)

Definition two_gen_fam (_ : unit) : TwoX ~{_2}~> TwoY := TwoXY.

Definition two_Generates : Generates two_gen_fam.
Proof.
  intros x y f.
  destruct f.
  - exact (@gen_id _2 unit _ _ two_gen_fam TwoX).
  - exact (@gen_id _2 unit _ _ two_gen_fam TwoY).
  - exact (@gen_idx _2 unit _ _ two_gen_fam tt).
Defined.

(*
The full index has (at least) two distinct elements the refined one
   does not: the two identities.

--------
完整索引至少有两个精炼索引没有的不同元素：两个身份。
*)

Example two_arrowix_apart :
  @mk_arrow _2 _ _ TwoXY = @mk_arrow _2 _ _ TwoIdX → False.
Proof. intro H; apply (f_equal (fun a => snd (`1 a))) in H; discriminate. Qed.

(*
Being an identity is decidable on [_2], so the non-identity family of
   the target's [nonid_Generates] generates there too.

--------
在 [_2] 上可以决定是否是一个身份，所以目标的 [nonid_Generates] 的非身份族也在那里生成。
*)

Definition two_isid_dec (x y : _2) (f : x ~{_2}~> y) :
  IsIdArrow x y f + (IsIdArrow x y f → False).
Proof.
  destruct f.
  - left; exact (@is_id_arrow _2 TwoX TwoIdX (reflexivity _)).
  - left; exact (@is_id_arrow _2 TwoY TwoIdY (reflexivity _)).
  - right; intro H; inversion H.
Defined.

Check (nonid_Generates two_isid_dec).

(*
The restriction does not change the limit: the one-index equalizer is
   canonically isomorphic, as a cone, to the full construction.

--------
该限制并不改变上限：一指标均衡器作为一个圆锥，与完整构造在典范意义下是同构的。
*)

Check (fun F : _2 ⟶ Sets =>
  pe_gen_restrict_iso Sets_HasIndexedProducts
    (HasEqualizers_of_HasPullbacks_Terminal Sets_HasPullbacks) F
    two_Generates).
