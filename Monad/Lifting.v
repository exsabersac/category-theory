Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Compose.
Require Import Category.Monad.Adjunction.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Limit.Preservation.

Generalizable All Variables.

(**
* Adjoint lifting along monadic functors, crude case

    nLab:      https://ncatlab.org/nlab/show/adjoint+lifting+theorem
    nLab:      https://ncatlab.org/nlab/show/adjoint+triangle+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

    This file delivers the adjoint lifting theorem in its adjoint-triangle
    form (Dubuc, “Adjoint triangles”, 1968), scoped to the crude
    monadicity hypotheses of Monad/Monadicity/Crude.v.

    Fix an adjunction F ⊣ U with F : D ⟶ C, and write T = U ◯ F for the
    induced monad on D and K = [EM_Comparison A] : C ⟶ D^T for the
    Eilenberg–Moore comparison (Monad/Comparison.v).  The core statement
    ([adjoint_triangle]) assumes only that K is fully faithful — that U is
    “of descent type” — supplied as [Full K] and [Faithful K] hypotheses:

      given R : B ⟶ C together with a left adjoint L0 ⊣ U ◯ R of the
      composite, if B has coequalizers of reflexive pairs, then R itself
      has a left adjoint ([Lifted_Left_Adjoint], adjoint to R by
      [adjoint_triangle]).

    The construction is the classical one.  For c : C, the parallel pair

        L0 (U ε_c),  ⌈U ε ∘ U F η0⌉  :  L0 (U (F (U c))) ⇉ L0 (U c)

    — the L0-transport of the canonical presentation of the comparison
    algebra K c, with the second leg the A0-inverse-transpose of the free
    algebra action on the A0-unit η0 — is reflexive with common section
    L0 η_{U c} ([lift_reflexive]; the retraction laws are the two zig-zag
    identities).  The value of the left adjoint at c is its chosen
    reflexive coequalizer e : L0 (U c) ~> q ([lift_obj]/[lift_e]).  The
    A0-transpose of e is an algebra homomorphism K c ~> K (R q) — its
    commuting square is the transposed cofork law ([lift_w_commutes]) —
    and pulling it back through the full comparison K produces the unit
    c ~> R q ([lift_unit]).  Every f : c ~> R b factors through the unit:
    the A0-inverse-transpose of U f coforks the pair ([lift_desc_cofork])
    and so descends through e, faithfulness of K (hence of U,
    [lift_faithful]) yields the factorization ([lift_factor_property]),
    and descent uniqueness read back through the transposition gives its
    uniqueness ([lift_factor_unique]).  The universal arrows so obtained
    assemble into a left adjoint via Theory/Universal/Arrow.v
    ([LeftAdjointFunctorFromUniversalArrows]).

    The principal theorem [adjoint_lifting] is the crude case: when the
    adjunction satisfies the crude hypotheses — C has reflexive
    coequalizers, U preserves them and reflects isomorphisms — the
    comparison is an equivalence ([crude_monadicity]), hence full and
    faithful (Theory/Equivalence/FullFaithful.v), and the triangle
    theorem applies: every R : B ⟶ C whose composite U ◯ R has a left
    adjoint has a left adjoint, provided B has reflexive coequalizers.
    [adjoint_lifting_monadic] states the same with the monadicity data
    packaged as [Monadic U] (Monad/Comparison.v).

    The classical square form of the adjoint lifting theorem — monads S
    on B' and T on D, a functor Q̄ between the algebra categories lifting
    Q : B' ⟶ D through the forgetful functors, and a left adjoint of Q —
    is the instance R := Q̄ of the triangle form: the composite of Q̄ with
    the (monadic) forgetful functor is Q ◯ U^S, whose left adjoint is
    F^S composed with the left adjoint of Q ([Adjunction_Compose]).

    Alongside, [EM_Adjunction_Transport] records the transport piece: an
    adjunction L ⊣ J whose right adjoint lands in the Eilenberg–Moore
    category composes with the adjoint equivalence K ⊣ K⁻¹ carried by the
    comparison (Theory/Equivalence/Adjoint.v) to the adjunction
    L ◯ K ⊣ K⁻¹ ◯ J, whose right adjoint lands in C. 

--------
* 沿着单子函子的伴随提升，粗略的情况

nLab：https://ncatlab.org/nlab/show/adjoint+lifting+theorem
 nLab：https://ncatlab.org/nlab/show/adjoint+triangle+theorem
 维基百科：https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

该文件在其伴随三角形中提供了伴随提升定理
 形式（Dubuc，“伴随三角形”，1968），范围为粗略
 Monad/Monadicity/Crude.v. 的单一性假设

将附加词 F ⊣ U 与 F : D ⟶ C 固定，并将 T = U ◯ F 写为
 D 和 K 上的诱导单子 = [EM_Comparison A] : C ⟶ D^T
 艾伦伯格-摩尔比较 (Monad/Comparison.v)。 核心说法
 ([adjoint_triangle]) 仅假设 K 完全忠实 — U 是
 “血统类型”——作为 [Full K] 和 [Faithful K] 假设提供：

给定 R : B ⟶ C 以及左伴随 L0 ⊣ U ◯ R
 复合，如果 B 具有自反对的共均衡器，则 R 本身
 有一个左伴随（[Lifted_Left_Adjoint]，与 R 的伴随为
 [adjoint_triangle]）。

建筑是古典的。 对于 c : C，平行对

L0 (U ε_c), ⌈U ε ∘ U F η0⌉ : L0 (U (F (U c))) ⇉ L0 (U c)

— 比较的规范表示的 L0 传输
 代数 K c，第二条腿是自由方程的 A0 转置
 A0 单元 η0 上的代数作用 — 与公共部分自反
 L0 η_{U c} ([lift_reflexive]；回缩定律是两个锯齿形
 身份）。 c 处左伴随的值是其选择的
 自反辅助均衡器 e : L0 (U c) ~> q ([lift_obj]/[lift_e])。 的
 e 的 A0 转置是代数同态 K c ~> K (R q) — 其
 通勤平方是转置 cofork 定律 ([lift_w_commutes]) —
 并通过完整比较 K 将其拉回产生单位
 c ~> R q ([lift_unit])。 每个 f : c ~> R b 通过单位因子：
 U f 的 A0 逆转置将这对 ([lift_desc_cofork]) 分叉
 因此通过 e 下降，K 的忠诚（因此是 U，
 [lift_faithful]) 产生因式分解 ([lift_factor_property])，
 通过转置读回的血统唯一性给出了它的
 唯一性（[lift_factor_unique]）。 如此获得的通用箭头
 通过 Theory/Universal/Arrow.v 组装成左伴随
 ([LeftAdjointFunctorFromUniversalArrows])。

主要定理 [adjoint_lifting] 是粗略的情况：当
 附加满足粗略假设——C 具有自反性
 共均衡器，U 保留它们并反映同构 —
 比较是等价的（[crude_monadicity]），因此完整且
 忠实 (Theory/Equivalence/FullFaithful.v)，以及三角形
 定理适用：每个 R : B ⟶ C 其复合 U ◯ R 有一个左
 伴随有一个左伴随，前提是 B 有自反余均衡器。 
[adjoint_lifting_monadic] 与单性数据的情况相同
 打包为 [Monadic U] (Monad/Comparison.v)。

伴随提升定理的经典平方形式 — monads S
 在 B' 和 T 在 D 上，代数类别提升之间的函子 Q̄
 Q : B' ⟶ D 通过健忘函子，以及 Q 的左伴随 —
 是三角形形式的实例 R := Q̄：Q̄ 与
 （单子）健忘函子是 Q ◯ U^S，其左伴随是
 F^S 由 Q 的左伴随组成 ([Adjunction_Compose])。

除此之外，[EM_Adjunction_Transport] 记录传输件：
 伴随 L ⊣ J 其右伴随落在 Eilenberg–Moore 上
 范畴由伴随等价 K ⊣ K⁻¹ 组成
 与附加的比较（Theory/Equivalence/Adjoint.v）
 L ◯ K ⊣ K⁻1 ◯ J，其右伴随落在 C 中。 
*)

(** ** The adjoint triangle theorem, for U of descent type  / ** 伴随三角形定理，对于下降型 U*)

Section AdjointTriangle.

Context {C : Category}.
Context {D : Category}.
Context {B : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (fullK : Full (EM_Comparison A)).
Context (faithK : Faithful (EM_Comparison A)).
Context {R : B ⟶ C}.
Context {L0 : D ⟶ B}.
Context (A0 : L0 ⊣ U ◯ R).
Context (RCB : HasReflexiveCoequalizers B).

Local Notation HM := (Adjunction_Induced_Monad A).
Local Notation EM := (@EilenbergMoore D (U ◯ F) HM).
Local Notation K := (EM_Comparison A).

(**
The A0-transposition laws, restated with the composite right
    adjoint's action split into fmap[U] (fmap[R] -), so that later
    rewrites are syntactic. 

--------
A0 换位法则，用复合权利重述
 adjoint 的操作拆分为 fmap[U] (fmap[R] -)，以便稍后
 重写是语法上的。 
*)

Lemma lift_transpose_unit {x : D} {b : B} (f : L0 x ~{B}~> b) :
  to (@adj _ _ _ _ A0 x b) f
    ≈ fmap[U] (fmap[R] f) ∘ @unit _ _ _ _ A0 x.
Proof. exact (@to_adj_unit _ _ _ _ A0 x b f). Qed.

Lemma lift_transpose_nat_r {x : D} {b b' : B}
  (f : b ~{B}~> b') (g : L0 x ~{B}~> b) :
  to (@adj _ _ _ _ A0 x b') (f ∘ g)
    ≈ fmap[U] (fmap[R] f) ∘ to (@adj _ _ _ _ A0 x b) g.
Proof. exact (@to_adj_nat_r _ _ _ _ A0 x b b' f g). Qed.

Lemma lift_untranspose_nat_r {x : D} {b b' : B}
  (f : b ~{B}~> b') (g : x ~{D}~> U (R b)) :
  from (@adj _ _ _ _ A0 x b') (fmap[U] (fmap[R] f) ∘ g)
    ≈ f ∘ from (@adj _ _ _ _ A0 x b) g.
Proof. exact (@from_adj_nat_r _ _ _ _ A0 x b b' f g). Qed.

(*
Transposition is injective: both transposes are the two legs of the
   hom-setoid isomorphism of A0. 

--------
转置是单射的：两个转置都是
 A0 的 hom-setoid 同构。 
*)
Lemma lift_transpose_inj {x : D} {b : B} (g h : L0 x ~{B}~> b) :
  to (@adj _ _ _ _ A0 x b) g ≈ to (@adj _ _ _ _ A0 x b) h → g ≈ h.
Proof.
  intros Hgh.
  transitivity (from (@adj _ _ _ _ A0 x b) (to (@adj _ _ _ _ A0 x b) g)).
  - symmetry.
    exact (@to_adj_comp_law _ _ _ _ A0 x b g).
  - transitivity (from (@adj _ _ _ _ A0 x b) (to (@adj _ _ _ _ A0 x b) h)).
    + exact (@from_adj_respects _ _ _ _ A0 x b _ _ Hgh).
    + exact (@to_adj_comp_law _ _ _ _ A0 x b h).
Qed.

(**
** The presentation pair, transported along L0

    The canonical presentation of the comparison algebra K c is the pair
    U ε_c, U F (η0) followed by the free action; transported through the
    adjunction L0 ⊣ U ◯ R it becomes a reflexive pair in B. 

--------
** 演示对，沿 L0 传输

 比较代数 K c 的规范表示是对
 U ε_c,U F(η0)接着自由动作； 运输通过
 附加词 L0 ⊣ U ◯ R 成为 B 中的自反对。 
*)

Definition lift_pair_l (c : C) :
  L0 (U (F (U c))) ~{B}~> L0 (U c) :=
  fmap[L0] (fmap[U] (@counit _ _ _ _ A c)).

(*
The algebra action of K (R (L0 (U c))) precomposed with the T-image of
   the A0-unit: the D-level second leg of the presentation. 

--------
K (R (L0 (U c))) 的代数作用与 T 图像预合成
 A0 单元：演示的 D 级第二部分。 
*)
Definition lift_action (c : C) :
  U (F (U c)) ~{D}~> U (R (L0 (U c))) :=
  fmap[U] (@counit _ _ _ _ A (R (L0 (U c))))
    ∘ fmap[U] (fmap[F] (@unit _ _ _ _ A0 (U c))).

Definition lift_pair_r (c : C) :
  L0 (U (F (U c))) ~{B}~> L0 (U c) :=
  from (@adj _ _ _ _ A0 (U (F (U c))) (L0 (U c))) (lift_action c).

(*
L0 (U ε_c) retracts L0 η_{U c}: the L0-image of the zig-zag identity
   of A. 

--------
L0 (U ε_c) 收回 L0 η_{U c}：zig-zag 恒等式的 L0 图像
 A 的。 
*)
Lemma lift_section_l (c : C) :
  lift_pair_l c ∘ fmap[L0] (@unit _ _ _ _ A (U c)) ≈ id.
Proof.
  unfold lift_pair_l.
  rewrite <- fmap_comp.
  rewrite (@fmap_counit_unit _ _ _ _ A c).
  apply fmap_id.
Qed.

(*
Restricting the action leg along the unit of A recovers the unit of
   A0: slide η across η0 by naturality, and close with the zig-zag
   identity of A. 

--------
沿 A 单位限制动作腿可恢复单位
 A0：自然地将 η 滑过 η0，并以之字形闭合
 A 的身份。 
*)
Lemma lift_action_unit (c : C) :
  lift_action c ∘ @unit _ _ _ _ A (U c) ≈ @unit _ _ _ _ A0 (U c).
Proof.
  unfold lift_action.
  rewrite <- comp_assoc.
  rewrite <- (adj_unit_natural A (@unit _ _ _ _ A0 (U c))).
  rewrite comp_assoc.
  rewrite (@fmap_counit_unit _ _ _ _ A (R (L0 (U c)))).
  apply id_left.
Qed.

(*
The transposed action leg retracts L0 η_{U c} as well: transpose the
   previous triangle and close with the zig-zag identity of A0. 

--------
转置的动作腿也缩回 L0 η_{U c}：转置
 前一个三角形并以 A0 的锯齿形收盘。 
*)
Lemma lift_section_r (c : C) :
  lift_pair_r c ∘ fmap[L0] (@unit _ _ _ _ A (U c)) ≈ id.
Proof.
  unfold lift_pair_r.
  rewrite <- (@from_adj_nat_l _ _ _ _ A0 _ _ _
                (lift_action c) (@unit _ _ _ _ A (U c))).
  transitivity (from (@adj _ _ _ _ A0 (U c) (L0 (U c)))
                  (@unit _ _ _ _ A0 (U c))).
  - exact (@from_adj_respects _ _ _ _ A0 _ _ _ _ (lift_action_unit c)).
  - exact (@from_adj_unit _ _ _ _ A0 (U c)).
Qed.

Definition lift_reflexive (c : C) :
  ReflexivePair (lift_pair_l c) (lift_pair_r c) :=
  common_section_reflexive (lift_pair_l c) (lift_pair_r c)
    (fmap[L0] (@unit _ _ _ _ A (U c)))
    (lift_section_l c) (lift_section_r c).

(** ** The candidate adjoint values: chosen reflexive coequalizers  / ** 候选伴随值：选择的自反协均衡器*)

Definition lift_coeq (c : C) :
  ∃ (q : B) (e : L0 (U c) ~{B}~> q),
    IsCoequalizer (lift_pair_l c) (lift_pair_r c) q e :=
  @reflexive_coeq B RCB (L0 (U (F (U c)))) (L0 (U c))
    (lift_pair_l c) (lift_pair_r c) (lift_reflexive c).

Definition lift_obj (c : C) : B := `1 (lift_coeq c).

Definition lift_e (c : C) : L0 (U c) ~{B}~> lift_obj c :=
  `1 (`2 (lift_coeq c)).

Definition lift_is_coeq (c : C) :
  IsCoequalizer (lift_pair_l c) (lift_pair_r c) (lift_obj c) (lift_e c) :=
  `2 (`2 (lift_coeq c)).

Lemma lift_cofork (c : C) :
  lift_e c ∘ lift_pair_l c ≈ lift_e c ∘ lift_pair_r c.
Proof. exact (cofork (lift_is_coeq c)). Qed.

(** ** The unit carrier: the A0-transpose of the coequalizing map  / ** 单位载波：共均衡映射的 A0 转置*)

Definition lift_w (c : C) : U c ~{D}~> U (R (lift_obj c)) :=
  to (@adj _ _ _ _ A0 (U c) (lift_obj c)) (lift_e c).

(*
Pushing the coequalizing map under the algebra action: counit
   naturality at fmap[R] e, after expanding the transpose through the
   unit of A0. 

--------
将同均衡图推到代数动作下：counit
 fmap[R] e 的自然性，通过扩展转置后
 A0 单位。 
*)
Lemma lift_action_square (c : C) :
  fmap[U] (@counit _ _ _ _ A (R (lift_obj c)))
      ∘ fmap[U] (fmap[F] (lift_w c))
    ≈ fmap[U] (fmap[R] (lift_e c)) ∘ lift_action c.
Proof.
  unfold lift_w.
  rewrite (lift_transpose_unit (lift_e c)).
  rewrite (@fmap_comp D C F _ _ _
             (fmap[U] (fmap[R] (lift_e c))) (@unit _ _ _ _ A0 (U c))).
  rewrite (@fmap_comp C D U _ _ _
             (fmap[F] (fmap[U] (fmap[R] (lift_e c))))
             (fmap[F] (@unit _ _ _ _ A0 (U c)))).
  rewrite comp_assoc.
  rewrite <- (@fmap_comp C D U _ _ _
                (@counit _ _ _ _ A (R (lift_obj c)))
                (fmap[F] (fmap[U] (fmap[R] (lift_e c))))).
  rewrite (adj_counit_natural A (fmap[R] (lift_e c))).
  rewrite (@fmap_comp C D U _ _ _
             (fmap[R] (lift_e c)) (@counit _ _ _ _ A (R (L0 (U c))))).
  unfold lift_action.
  rewrite <- comp_assoc.
  reflexivity.
Qed.

(*
The commuting square of the transposed coequalizing map: it is an
   algebra homomorphism K c ~> K (R (lift_obj c)).  Transpose the cofork
   law of the coequalizer and contract with [lift_action_square]. 

--------
转置共均衡图的通勤方：它是一个
 代数同态 K c ~> K (R (lift_obj c))。 转置 cofork
 协均衡器法则以及与 [lift_action_square] 的合同。 
*)
Lemma lift_w_commutes (c : C) :
  lift_w c ∘ fmap[U] (@counit _ _ _ _ A c)
    ≈ fmap[U] (@counit _ _ _ _ A (R (lift_obj c)))
        ∘ fmap[U] (fmap[F] (lift_w c)).
Proof.
  rewrite (lift_action_square c).
  transitivity (to (@adj _ _ _ _ A0 (U (F (U c))) (lift_obj c))
                  (lift_e c ∘ lift_pair_l c)).
  - symmetry.
    exact (@to_adj_nat_l _ _ _ _ A0 _ _ _
             (lift_e c) (fmap[U] (@counit _ _ _ _ A c))).
  - transitivity (to (@adj _ _ _ _ A0 (U (F (U c))) (lift_obj c))
                    (lift_e c ∘ lift_pair_r c)).
    + exact (@to_adj_respects _ _ _ _ A0 _ _ _ _ (lift_cofork c)).
    + rewrite (lift_transpose_nat_r (lift_e c) (lift_pair_r c)).
      apply compose_respects.
      * reflexivity.
      * unfold lift_pair_r.
        exact (@from_adj_comp_law _ _ _ _ A0 _ _ (lift_action c)).
Qed.

(*
The algebra homomorphism K c ~> K (R (lift_obj c)) carried by the
   transpose of e. 

--------
所承载的代数同态 K c ~> K (R (lift_obj c))
 e 的转置 
*)
Definition lift_unit_hom (c : C) :
  K c ~{EM}~> K (R (lift_obj c)) :=
  @Build_TAlgebraHom D (U ◯ F) HM (U c) (U (R (lift_obj c)))
    (EM_Comparison_Algebra A c)
    (EM_Comparison_Algebra A (R (lift_obj c)))
    (lift_w c) (lift_w_commutes c).

(** ** The unit, through the fully faithful comparison  / ** 单位，通过完全忠实的比较*)

Definition lift_unit (c : C) : c ~{C}~> R (lift_obj c) :=
  @prefmap C EM K fullK c (R (lift_obj c)) (lift_unit_hom c).

(*
The section law of fullness, read on carriers: hom-equivalence in the
   Eilenberg-Moore category is carrier equivalence, and the carrier of
   fmap[K] is fmap[U]. 

--------
完备截面定律，在载体上阅读： 中的 hom 等价
 Eilenberg-Moore 范畴是载体等价，并且载体
 fmap[K] 是 fmap[U]。 
*)
Lemma lift_unit_w (c : C) : fmap[U] (lift_unit c) ≈ lift_w c.
Proof.
  exact (@fmap_sur C EM K fullK c (R (lift_obj c)) (lift_unit_hom c)).
Qed.

(* Faithfulness of K, read on carriers, is faithfulness of U.  / K 的忠诚度，在载体上读到，就是 U 的忠诚度。*)
Lemma lift_faithful {x y : C} (f g : x ~{C}~> y) :
  fmap[U] f ≈ fmap[U] g → f ≈ g.
Proof using A C D F U faithK.
  intros Hfg.
  apply (@fmap_inj C EM K faithK x y f g).
  exact Hfg.
Qed.

(** ** Descent: every f : c ~> R b factors through the unit  / ** 下降：每个 f : c ~> R b 通过单位的因子*)

(* The A0-inverse-transpose of U f, the map to be descended.  / U f 的 A0 逆转置，即要下降的映射。*)
Definition lift_desc_arg {c : C} {b : B} (f : c ~{C}~> R b) :
  L0 (U c) ~{B}~> b :=
  from (@adj _ _ _ _ A0 (U c) b) (fmap[U] f).

(*
Its own transposition triangle: restricting along the A0-unit
   recovers U f. 

--------
它自己的换位三角形：沿 A0 单元限制
 恢复 U f。 
*)
Lemma lift_desc_transpose {c : C} {b : B} (f : c ~{C}~> R b) :
  fmap[U] (fmap[R] (lift_desc_arg f)) ∘ @unit _ _ _ _ A0 (U c)
    ≈ fmap[U] f.
Proof.
  transitivity (to (@adj _ _ _ _ A0 (U c) b) (lift_desc_arg f)).
  - symmetry.
    exact (lift_transpose_unit (lift_desc_arg f)).
  - exact (@from_adj_comp_law _ _ _ _ A0 (U c) b (fmap[U] f)).
Qed.

(*
The D-level cofork of the descent: U f absorbs the presentation pair,
   by counit naturality at fmap[R] (lift_desc_arg f) and at f. 

--------
下降的 D 级 cofork：U f 吸收呈现对，
 通过 fmap[R] (lift_desc_arg f) 和 f 处的自然性。 
*)
Lemma lift_desc_square {c : C} {b : B} (f : c ~{C}~> R b) :
  fmap[U] f ∘ fmap[U] (@counit _ _ _ _ A c)
    ≈ fmap[U] (fmap[R] (lift_desc_arg f)) ∘ lift_action c.
Proof.
  symmetry.
  unfold lift_action.
  rewrite comp_assoc.
  rewrite <- (@fmap_comp C D U _ _ _
                (fmap[R] (lift_desc_arg f))
                (@counit _ _ _ _ A (R (L0 (U c))))).
  rewrite <- (adj_counit_natural A (fmap[R] (lift_desc_arg f))).
  rewrite (@fmap_comp C D U _ _ _
             (@counit _ _ _ _ A (R b))
             (fmap[F] (fmap[U] (fmap[R] (lift_desc_arg f))))).
  rewrite <- comp_assoc.
  rewrite <- (@fmap_comp C D U _ _ _
                (fmap[F] (fmap[U] (fmap[R] (lift_desc_arg f))))
                (fmap[F] (@unit _ _ _ _ A0 (U c)))).
  rewrite <- (@fmap_comp D C F _ _ _
                (fmap[U] (fmap[R] (lift_desc_arg f)))
                (@unit _ _ _ _ A0 (U c))).
  rewrite (lift_desc_transpose f).
  rewrite <- (@fmap_comp C D U _ _ _
                (@counit _ _ _ _ A (R b)) (fmap[F] (fmap[U] f))).
  rewrite (adj_counit_natural A f).
  exact (@fmap_comp C D U _ _ _ f (@counit _ _ _ _ A c)).
Qed.

Lemma lift_desc_cofork {c : C} {b : B} (f : c ~{C}~> R b) :
  lift_desc_arg f ∘ lift_pair_l c ≈ lift_desc_arg f ∘ lift_pair_r c.
Proof.
  transitivity (from (@adj _ _ _ _ A0 (U (F (U c))) b)
                  (fmap[U] f ∘ fmap[U] (@counit _ _ _ _ A c))).
  - symmetry.
    exact (@from_adj_nat_l _ _ _ _ A0 _ _ _
             (fmap[U] f) (fmap[U] (@counit _ _ _ _ A c))).
  - transitivity (from (@adj _ _ _ _ A0 (U (F (U c))) b)
                    (fmap[U] (fmap[R] (lift_desc_arg f)) ∘ lift_action c)).
    + exact (@from_adj_respects _ _ _ _ A0 _ _ _ _ (lift_desc_square f)).
    + exact (lift_untranspose_nat_r (lift_desc_arg f) (lift_action c)).
Qed.

Definition lift_desc {c : C} {b : B} (f : c ~{C}~> R b) :
  ∃! u : lift_obj c ~{B}~> b, u ∘ lift_e c ≈ lift_desc_arg f :=
  coeq_desc (lift_is_coeq c) (lift_desc_arg f) (lift_desc_cofork f).

Definition lift_factor {c : C} {b : B} (f : c ~{C}~> R b) :
  lift_obj c ~{B}~> b :=
  unique_obj (lift_desc f).

Definition lift_factor_e {c : C} {b : B} (f : c ~{C}~> R b) :
  lift_factor f ∘ lift_e c ≈ lift_desc_arg f :=
  unique_property (lift_desc f).

(*
The factorization law: both sides have the same U-image, and U is
   faithful. 

--------
因式分解法则：两边有相同的U像，U为
 忠实的。 
*)
Lemma lift_factor_property {c : C} {b : B} (f : c ~{C}~> R b) :
  f ≈ fmap[R] (lift_factor f) ∘ lift_unit c.
Proof using A A0 B C D F L0 R RCB U faithK fullK.
  apply lift_faithful.
  rewrite (@fmap_comp C D U _ _ _ (fmap[R] (lift_factor f)) (lift_unit c)).
  rewrite (lift_unit_w c).
  transitivity (to (@adj _ _ _ _ A0 (U c) b) (lift_desc_arg f)).
  - symmetry.
    exact (@from_adj_comp_law _ _ _ _ A0 (U c) b (fmap[U] f)).
  - transitivity (to (@adj _ _ _ _ A0 (U c) b)
                    (lift_factor f ∘ lift_e c)).
    + symmetry.
      exact (@to_adj_respects _ _ _ _ A0 _ _ _ _ (lift_factor_e f)).
    + exact (lift_transpose_nat_r (lift_factor f) (lift_e c)).
Qed.

(*
Uniqueness of the factorization: any other mediator descends the same
   map (compare transposes), so descent uniqueness identifies them. 

--------
分解的唯一性：任何其他中介都会下降相同
 映射（比较转置），因此下降唯一性可以识别它们。 
*)
Lemma lift_factor_unique {c : C} {b : B} (f : c ~{C}~> R b)
  (v : lift_obj c ~{B}~> b) (Hv : f ≈ fmap[R] v ∘ lift_unit c) :
  lift_factor f ≈ v.
Proof.
  apply (uniqueness (lift_desc f)).
  apply lift_transpose_inj.
  transitivity (fmap[U] (fmap[R] v) ∘ lift_w c).
  - exact (lift_transpose_nat_r v (lift_e c)).
  - transitivity (fmap[U] (fmap[R] v ∘ lift_unit c)).
    + rewrite (@fmap_comp C D U _ _ _ (fmap[R] v) (lift_unit c)).
      apply compose_respects.
      * reflexivity.
      * symmetry.
        exact (lift_unit_w c).
    + transitivity (fmap[U] f).
      * now rewrite Hv.
      * symmetry.
        exact (@from_adj_comp_law _ _ _ _ A0 (U c) b (fmap[U] f)).
Qed.

(** ** The universal arrows, and the lifted left adjoint  / ** 通用箭头和提升的左伴随*)

Definition lift_ump (c : C) (b : B) (f : c ~{C}~> R b) :
  ∃! g : lift_obj c ~{B}~> b, f ≈ fmap[R] g ∘ lift_unit c :=
  {| unique_obj      := lift_factor f
   ; unique_property := lift_factor_property f
   ; uniqueness      := fun v Hv => lift_factor_unique f v Hv |}.

Definition lift_universal_arrow (c : C) : UniversalArrow c R :=
  universal_arrow_from_UMP c R (lift_obj c) (lift_unit c)
    (fun b f => lift_ump c b f).

(**
The adjoint triangle theorem (Dubuc): with U of descent type, a left
    adjoint of U ◯ R and reflexive coequalizers in B induce a left
    adjoint of R. 

--------
伴随三角形定理（Dubuc）：对于下降型 U，左
 U ◯ R 的伴随和 B 中的反身余均衡器产生左
 R 的伴随。 
*)

Definition Lifted_Left_Adjoint : C ⟶ B :=
  LeftAdjointFunctorFromUniversalArrows R lift_universal_arrow.

Definition adjoint_triangle : Lifted_Left_Adjoint ⊣ R :=
  AdjunctionFromUniversalArrows R lift_universal_arrow.

End AdjointTriangle.

(** ** Transport: adjunctions into the Eilenberg–Moore category descend  / ** 交通：艾伦伯格-摩尔类别的附加项下降*)

Section TransportEM.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (E : EquivalenceOfCategories (EM_Comparison A)).
Context {B : Category}.
Context {L : @EilenbergMoore D (U ◯ F) (Adjunction_Induced_Monad A) ⟶ B}.
Context {J : B ⟶ @EilenbergMoore D (U ◯ F) (Adjunction_Induced_Monad A)}.
Context (AJ : L ⊣ J).

(*
An adjunction whose right adjoint lands in the Eilenberg-Moore
   category composes with the adjoint equivalence K ⊣ K⁻¹ of the
   comparison to one whose right adjoint lands in C. 

--------
其右伴随落在 Eilenberg-Moore 中的伴随词
 范畴由伴随等价 K ⊣ K⁻¹ 组成
 与右伴随落在 C 中的一个进行比较。 
*)
Definition EM_Adjunction_Transport :
  (L ◯ EM_Comparison A) ⊣ (@quasi_inverse _ _ _ E ◯ J) :=
  Adjunction_Compose (equiv_adjunction E) AJ.

End TransportEM.

(** ** The crude-case adjoint lifting theorem  / ** 粗例伴随提升定理*)

Section AdjointLiftingCrude.

Context {C : Category}.
Context {D : Category}.
Context {B : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (RC : HasReflexiveCoequalizers C).
Context (pres : PreservesReflexiveCoequalizers U).
Context (refl : ReflectsIsos U).
Context {R : B ⟶ C}.
Context {L0 : D ⟶ B}.
Context (A0 : L0 ⊣ U ◯ R).
Context (RCB : HasReflexiveCoequalizers B).

(*
The crude monadicity equivalence makes the comparison full and
   faithful. 

--------
粗略的一元性等价使得比较充分并且
 忠实的。 
*)
Definition adjoint_lifting_full : Full (EM_Comparison A) :=
  Equivalence_Full (crude_monadicity A RC pres refl).

Definition adjoint_lifting_faithful : Faithful (EM_Comparison A) :=
  Equivalence_Faithful (crude_monadicity A RC pres refl).

(**
The adjoint lifting theorem, crude case: if F ⊣ U satisfies the
    crude monadicity hypotheses, then any functor R into C whose
    composite with U has a left adjoint itself has a left adjoint,
    provided the domain of R has reflexive coequalizers. 

--------
伴随提升定理，粗略情况：如果 F ⊣ U 满足
 粗略的一元性假设，然后任何函子 R 进入 C ，其
 与 U 的复合有一个左伴随，它本身也有一个左伴随，
 假设 R 的域具有自反协均衡器。 
*)

Theorem adjoint_lifting : ∃ L : C ⟶ B, L ⊣ R.
Proof using A A0 B C D F L0 R RC RCB U pres refl.
  exists (Lifted_Left_Adjoint A
            adjoint_lifting_full adjoint_lifting_faithful A0 RCB).
  exact (adjoint_triangle A
           adjoint_lifting_full adjoint_lifting_faithful A0 RCB).
Defined.

End AdjointLiftingCrude.

(** The same statement with the monadicity data packaged as [Monadic].  / 与打包为 [Monadic] 的单性数据相同的语句。*)

Theorem adjoint_lifting_monadic {C D B : Category} {U : C ⟶ D}
  (M : Monadic U) {R : B ⟶ C} {L0 : D ⟶ B}
  (A0 : L0 ⊣ U ◯ R) (RCB : HasReflexiveCoequalizers B) :
  ∃ L : C ⟶ B, L ⊣ R.
Proof.
  exists (Lifted_Left_Adjoint (`1 (`2 M))
            (Equivalence_Full (`2 (`2 M)))
            (Equivalence_Faithful (`2 (`2 M))) A0 RCB).
  exact (adjoint_triangle (`1 (`2 M))
           (Equivalence_Full (`2 (`2 M)))
           (Equivalence_Faithful (`2 (`2 M))) A0 RCB).
Defined.
