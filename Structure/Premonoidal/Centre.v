Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Binoidal.Central.
Require Import Category.Structure.Premonoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(*
   * * The centre of a premonoidal category is monoidal

   nLab: https://ncatlab.org/nlab/show/premonoidal+category
   (the centre Z(C) and its monoidal structure are discussed there)

   Structure/Binoidal/Central.v packages the central morphisms of a
   binoidal category as a wide subcategory Z(C) = [Centre C], and records
   why closure of centrality under the interleaved tensor [composite_ff']
   is out of reach in a bare binoidal category: the required commuting
   square lives at the nested tensor (x ⊗ x') ⊗ a, and without structural
   morphisms there is nothing connecting the two nesting levels.  A
   premonoidal category (Structure/Premonoidal.v) supplies exactly the
   missing ingredient — a central associator, natural in each variable
   separately — and this file completes the development:

   - [composite_ff'_central]: if f and f' are central, so is
   [composite_ff' f f'].  Each defining square of the composite is
   conjugated by the associator, trading the single unreachable
   square at the nested tensor for three one-variable naturality
   squares plus two single-level centrality squares (Power–Robinson,
   "Premonoidal categories and notions of computation", 1997).

   - [Centre_Tensor]: the tensor restricts to a genuine bifunctor
   Z(C) ∏ Z(C) ⟶ Z(C).  On the centre, [composite_ff'] is jointly
   functorial because the one-sided interchange lemma
   [composite_ff'_comp_l] of Structure/Binoidal/Central.v receives
   its centrality hypothesis from the hom witnesses, and the tensor
   of two central morphisms is again central by the closure theorem.

   - [Centre_Monoidal]: Z(C) is a monoidal category.  Unit, unitors
   and associator are inherited from the premonoidal structure (the
   forward components are central by the class fields, the inverses
   by [central_iso_from]); every coherence field is an equation
   between underlying morphisms of C because [Sub]-homsets compare
   first projections, so the [composite_ff']-phrased translation
   lemmas of Structure/Premonoidal.v discharge them verbatim.

   Together these discharge the promise recorded above [central] in
   Structure/Binoidal.v: the central morphisms form the centre, a
   monoidal subcategory of C. 

   --------
   * * 预单范畴的中心是单范畴的

   nLab:  https://ncatlab.org/nlab/show/premonoidal+category
   （其中讨论了中心 Z(C) 及其单范畴结构）

   Structure/Binoidal/Central.v 将二范畴的中心态射组织为宽子范畴 Z(C) = [Centre C]，并记录了为什么在一个纯二范畴中，中心性在交错张量 [composite_ff'] 下封闭是无法实现的：所需的交换方形存在于嵌套张量 (x ⊗ x') ⊗ a 中，没有结构态射时，两个嵌套层之间毫无联系。预单范畴 (Structure/Premonoidal.v) 正好提供了缺失的成分——一个对每个变量分别自然的中心结合子——此文件完成了该发展的内容：- [composite_ff'_central]：如果 f 和 f' 是中心的，那么 [composite_ff' f f'] 也是中心的。复合的每个定义方块都被结合子共轭，将嵌套张量中唯一无法到达的方块替换为三个单变量自然性方块加两个单层中心性方块（Power–Robinson，《前单类范畴与计算的概念》，1997 年）。

   - [Centre_Tensor]：张量限制为真正的双函子 Z(C) ∏ Z(C) ⟶ Z(C)。在中心上，[composite_ff'] 是联合函子性的，因为单边交换引理 [composite_ff'_comp_l]（出自 Structure/Binoidal/Central.v）从同态证人那里接受其中心性假设，并且两个中心态射的张量根据闭包定理再次是中心的。-  [Centre_Monoidal] ：Z(C) 是一个单幺范畴。单位元、单元子和结合子继承自前单幺结构（由类字段，前向分量是中心的，逆元由 [central_iso_from] 提供）；每个相容性字段都是 C 的底层态射之间的等式，因为 [Sub] -hom 集比较第一个投影，因此 Structure/Premonoidal.v 中的 [composite_ff'] 表述的翻译引理可以原封不动地解答它们。

   这些共同解答了上文 [central] 在 Structure/Binoidal.v 中记录的承诺：中心态射构成了中心，是 C 的单幺子范畴。
*)

Section PremonoidalCentre.

Context {C : Category}.
Context `{B : @Binoidal C}.
Context `{P : @Premonoidal C B}.

(*
 Section-local object-level tensor, exactly as in
 Structure/Premonoidal.v: the unscoped notation makes ⊗ mean the OBJECT
 tensor everywhere inside this section, while morphism-level interleaved
 tensoring is always written [composite_ff']. 

 --------
 段内局部对象级张量，正如在 Structure/Premonoidal.v 中一样：未加作用域的符号使得 ⊗ 在本段的任何地方都表示对象张量，而态射级交错张量总是写作 [composite_ff']。
*)
Local Notation "x ⊗ y" := (tensor x y)
  (at level 30, right associativity).

(*
   * ** Closure of centrality under the tensor

   For central f : x ~> y and f' : x' ~> y', the interleaved tensor
   [composite_ff' f f'] is central.  Writing α for [to premon_assoc],
   the first defining square (against an arbitrary h : a ~> b) is
   conjugated by α : ((y ⊗ y') ⊗ b) ≅ (y ⊗ (y' ⊗ b)); expanding
   [fmap[inj_left _]] over the two factors of the composite and pushing
   α through each factor with the three one-variable naturality squares
   ([premon_assoc_natural_middle], [_left], [_right]) brings both sides
   to a word in which the two centrality squares — [central f] against
   (x' ⋊ h) and [central f'] against h — apply at a SINGLE tensor level;
   both sides land on the common normal form

   (y ⋊ (y' ⋊ h)) ∘ (y ⋊ (f' ⋉ a)) ∘ (f ⋉ (x' ⊗ a)) ∘ α.

   The second square mirrors the first with the from-direction
   naturality squares (conjugating by [from premon_assoc]) and the
   second conjuncts of the two centrality hypotheses.  Each square is
   established after composing with the conjugating isomorphism on the
   left, which is sufficient because the [to] and [from] components of
   an isomorphism are monic ([iso_to_monic] and [iso_from_monic],
   Theory/Isomorphism.v).  Note that
   [composite_f'f f' f] is definitionally [composite_ff' f' f], so no
   mirror closure lemma is needed. 

   --------
   * ** 张量下中心性的闭包

   对于中心 f ： x ~> y 和 f' ： x' ~> y'，即交错张量
   [composite_ff' f f']是核心。为[to premon_assoc]写作α，
   第一个定义方阵（对任意 h ： a ~> b）为
   通过α共轭：（（（y ⊗ y'） ⊗ b） ≅ （y ⊗ （y' ⊗ b））;展开
   [fmap[inj_left _] ] 在复合体和推力两个因素上
   用三个一变量自然性平方α每个因子
   （[premon_assoc_natural_middle]，[_left]，[_right]）双方都有
   一个两个中心性平方——[central f] 对立的词
   （x' ⋊ h）和[central f']对 h —— 作用于单一张量级;
   双方都落在共同的标准形上

   （y ⋊ （y' ⋊ h）） ∘ （y ⋊ （f' ⋉ a）） ∘ （f ⋉ （x' ⊗ a）） ∘ α。第二个方格反映了第一个方格，其中包含来自方向的自然性方格（通过 [from premon_assoc] 共轭）以及两个中心性假设的第二个合取。每个方格在与左侧的共轭同构组合后建立，这已经足够，因为同构的 [to] 和 [from] 分量是单射（[iso_to_monic] 和 [iso_from_monic]，Theory/Isomorphism.v）。注意 [composite_f'f f' f] 在定义上等于 [composite_ff' f' f]，因此不需要镜像封闭引理。
*)

Theorem composite_ff'_central {x x' y y'} {f : x ~> y} {f' : x' ~> y'} :
  central f → central f' → central (composite_ff' f f').
Proof using B C P.
  intros cf cf' a b h.
  split.
  - (* Square 1, on (x ⊗ x') ⊗ a ~~> (y ⊗ y') ⊗ b. / 方形 1，在 (x ⊗ x') ⊗ a ~~> (y ⊗ y') ⊗ b。 *)
    destruct (cf (x' ⊗ a) (x' ⊗ b) (fmap[inj_right x'] h)) as [cfh _].
    destruct (cf' a b h) as [cf'h _].
    apply (iso_to_monic (@premon_assoc C B P y y' b)).
    unfold composite_ff'.
    rewrite !fmap_comp.
    rewrite !comp_assoc.
    transitivity
      ((((y ⋊ (y' ⋊ h)) ∘ (y ⋊ (f' ⋉ a))) ∘ (f ⋉ (x' ⊗ a)))
         ∘ to (@premon_assoc C B P x x' a)).
    { (* Left side: push α through the middle, left and right factors, then swap with the two centralities. / 左边：把α推进中间，左右因子，然后与两个中心性交换。 *)
      transitivity
        ((((y ⋊ (f' ⋉ b)) ∘ to (@premon_assoc C B P y x' b))
            ∘ ((f ⋉ x') ⋉ b)) ∘ ((x ⊗ x') ⋊ h)).
      { do 2 (apply compose_respects; [|reflexivity]).
        symmetry; apply premon_assoc_natural_middle. }
      transitivity
        ((((y ⋊ (f' ⋉ b)) ∘ (f ⋉ (x' ⊗ b)))
            ∘ to (@premon_assoc C B P x x' b)) ∘ ((x ⊗ x') ⋊ h)).
      { apply compose_respects; [|reflexivity].
        rewrite <- !comp_assoc.
        apply compose_respects; [reflexivity|].
        symmetry; apply premon_assoc_natural_left. }
      transitivity
        ((((y ⋊ (f' ⋉ b)) ∘ (f ⋉ (x' ⊗ b))) ∘ (x ⋊ (x' ⋊ h)))
           ∘ to (@premon_assoc C B P x x' a)).
      { rewrite <- !comp_assoc.
        do 2 (apply compose_respects; [reflexivity|]).
        symmetry; apply premon_assoc_natural_right. }
      transitivity
        ((((y ⋊ (f' ⋉ b)) ∘ (y ⋊ (x' ⋊ h))) ∘ (f ⋉ (x' ⊗ a)))
           ∘ to (@premon_assoc C B P x x' a)).
      { apply compose_respects; [|reflexivity].
        rewrite <- !comp_assoc.
        apply compose_respects; [reflexivity|].
        apply cfh. }
      do 2 (apply compose_respects; [|reflexivity]).
      rewrite <- !fmap_comp.
      now rewrite cf'h. }
    { (* Right side: the same three naturality squares, no swaps. / 右边：相同的三个自然性方块，没有交换。 *)
      symmetry.
      transitivity
        ((((y ⋊ (y' ⋊ h)) ∘ to (@premon_assoc C B P y y' a))
            ∘ ((y ⋊ f') ⋉ a)) ∘ ((f ⋉ x') ⋉ a)).
      { do 2 (apply compose_respects; [|reflexivity]).
        symmetry; apply premon_assoc_natural_right. }
      transitivity
        ((((y ⋊ (y' ⋊ h)) ∘ (y ⋊ (f' ⋉ a)))
            ∘ to (@premon_assoc C B P y x' a)) ∘ ((f ⋉ x') ⋉ a)).
      { apply compose_respects; [|reflexivity].
        rewrite <- !comp_assoc.
        apply compose_respects; [reflexivity|].
        symmetry; apply premon_assoc_natural_middle. }
      rewrite <- !comp_assoc.
      do 2 (apply compose_respects; [reflexivity|]).
      symmetry; apply premon_assoc_natural_left. }
  - (* Square 2, on a ⊗ (x ⊗ x') ~~> b ⊗ (y ⊗ y'). / 方块 2，在 ⊗ (x ⊗ x') ~~> b ⊗ (y ⊗ y') 上。 *)
    destruct (cf a b h) as [_ cf2].
    destruct (cf' (a ⊗ y) (b ⊗ y) (fmap[inj_left y] h)) as [_ cf'2].
    apply (iso_from_monic (@premon_assoc C B P b y y')).
    unfold composite_ff'.
    rewrite !fmap_comp.
    rewrite !comp_assoc.
    transitivity
      (((((b ⊗ y) ⋊ f') ∘ ((b ⋊ f) ⋉ x')) ∘ ((h ⋉ x) ⋉ x'))
         ∘ from (@premon_assoc C B P a x x')).
    { (* Left side: push α⁻¹ through, then swap with the two centralities' second conjuncts. / 左侧：将 α⁻¹ 推过，然后与两个中心性的第二个合取分量交换。 *)
      transitivity
        (((((h ⋉ y) ⋉ y') ∘ from (@premon_assoc C B P a y y'))
            ∘ (a ⋊ (y ⋊ f'))) ∘ (a ⋊ (f ⋉ x'))).
      { do 2 (apply compose_respects; [|reflexivity]).
        symmetry; apply premon_assoc_natural_left_from. }
      transitivity
        (((((h ⋉ y) ⋉ y') ∘ ((a ⊗ y) ⋊ f'))
            ∘ from (@premon_assoc C B P a y x')) ∘ (a ⋊ (f ⋉ x'))).
      { apply compose_respects; [|reflexivity].
        rewrite <- !comp_assoc.
        apply compose_respects; [reflexivity|].
        symmetry; apply premon_assoc_natural_right_from. }
      transitivity
        (((((h ⋉ y) ⋉ y') ∘ ((a ⊗ y) ⋊ f')) ∘ ((a ⋊ f) ⋉ x'))
           ∘ from (@premon_assoc C B P a x x')).
      { rewrite <- !comp_assoc.
        do 2 (apply compose_respects; [reflexivity|]).
        symmetry; apply premon_assoc_natural_middle_from. }
      transitivity
        (((((b ⊗ y) ⋊ f') ∘ ((h ⋉ y) ⋉ x')) ∘ ((a ⋊ f) ⋉ x'))
           ∘ from (@premon_assoc C B P a x x')).
      { do 2 (apply compose_respects; [|reflexivity]).
        apply cf'2. }
      apply compose_respects; [|reflexivity].
      rewrite <- !comp_assoc.
      apply compose_respects; [reflexivity|].
      transitivity (((h ⋉ y) ∘ (a ⋊ f)) ⋉ x').
      { symmetry.
        exact (@fmap_comp C C (@inj_left C B x') (a ⊗ x) (a ⊗ y) (b ⊗ y)
                 (fmap[@inj_left C B y] h) (fmap[@inj_right C B a] f)). }
      transitivity (((b ⋊ f) ∘ (h ⋉ x)) ⋉ x').
      { now rewrite cf2. }
      exact (@fmap_comp C C (@inj_left C B x') (a ⊗ x) (b ⊗ x) (b ⊗ y)
               (fmap[@inj_right C B b] f) (fmap[@inj_left C B x] h)). }
    { (* Right side: the same three from-direction squares, no swaps. / 右边：相同的三个来自方向的方块，没有交换。 *)
      symmetry.
      transitivity
        (((((b ⊗ y) ⋊ f') ∘ from (@premon_assoc C B P b y x'))
            ∘ (b ⋊ (f ⋉ x'))) ∘ (h ⋉ (x ⊗ x'))).
      { do 2 (apply compose_respects; [|reflexivity]).
        symmetry; apply premon_assoc_natural_right_from. }
      transitivity
        (((((b ⊗ y) ⋊ f') ∘ ((b ⋊ f) ⋉ x'))
            ∘ from (@premon_assoc C B P b x x')) ∘ (h ⋉ (x ⊗ x'))).
      { apply compose_respects; [|reflexivity].
        rewrite <- !comp_assoc.
        apply compose_respects; [reflexivity|].
        symmetry; apply premon_assoc_natural_middle_from. }
      rewrite <- !comp_assoc.
      do 2 (apply compose_respects; [reflexivity|]).
      symmetry; apply premon_assoc_natural_left_from. }
Qed.

(*
   * ** Lifting central isomorphisms to the centre

   A C-isomorphism whose forward component is central lifts to an
   isomorphism in Z(C): the inverse is central by [central_iso_from],
   and both inverse laws are the underlying C-equations because
   [Sub]-homsets compare first projections.  The objects are arbitrary
   objects of the centre (their [poly_unit] witnesses need not be
   [ttt]), which is exactly the generality [Build_Monoidal] requires
   below. 

   --------
   * ** 将中心同构提升到中心

   一个 C-同构，其正向分量是中心同构，可以提升为 Z(C) 中的同构：其逆同构是中心的，依据 [central_iso_from]，并且两个逆律是基本的 C-方程，因为 [Sub] -同态集比较第一个投影。对象是中心的任意对象（它们的 [poly_unit] 见证不必是 [ttt]），这正是下面 [Build_Monoidal] 所要求的通用性。
*)

Definition Centre_lift_iso {p q : @Centre C B} (i : `1 p ≅[C] `1 q)
           (ci : central (to i)) : p ≅[@Centre C B] q :=
  @Build_Isomorphism (@Centre C B) p q
    (to i; ci)
    (from i; central_iso_from i ci)
    (iso_to_from i)
    (iso_from_to i).

(* * ** The tensor bifunctor on the centre / * ** 中心上的张量双函子 *)

Definition Centre_Tensor_obj (p : @Centre C B ∏ @Centre C B) :
  @Centre C B := (`1 (fst p) ⊗ `1 (snd p); ttt).

Definition Centre_Tensor_fmap (p q : @Centre C B ∏ @Centre C B)
           (fg : p ~{@Centre C B ∏ @Centre C B}~> q) :
  Centre_Tensor_obj p ~{@Centre C B}~> Centre_Tensor_obj q :=
  (composite_ff' (`1 (fst fg)) (`1 (snd fg));
   composite_ff'_central (`2 (fst fg)) (`2 (snd fg))).

Lemma Centre_Tensor_respects (p q : @Centre C B ∏ @Centre C B) :
  Proper (equiv ==> equiv) (Centre_Tensor_fmap p q).
Proof.
  intros fg hk [e1 e2]; simpl.
  apply composite_ff'_respects; assumption.
Qed.

Lemma Centre_Tensor_id (p : @Centre C B ∏ @Centre C B) :
  Centre_Tensor_fmap p p (@id (@Centre C B ∏ @Centre C B) p) ≈ id.
Proof.
  simpl.
  rewrite composite_id_left.
  exact (@fmap_id C C (@inj_right C B (`1 (fst p))) (`1 (snd p))).
Qed.

(*
 Joint functoriality: on the centre the one-sided interchange
 [composite_ff'_comp_l] receives its centrality hypothesis from the
 hom witness of the first component. 

 --------
 联合函子性：在中心单边交换 [composite_ff'_comp_l] 从第一个分量的同态见证中接收其中心性假设。
*)
Lemma Centre_Tensor_comp (p q r : @Centre C B ∏ @Centre C B)
      (fg : q ~{@Centre C B ∏ @Centre C B}~> r)
      (hk : p ~{@Centre C B ∏ @Centre C B}~> q) :
  Centre_Tensor_fmap p r (fg ∘ hk)
    ≈ Centre_Tensor_fmap q r fg ∘ Centre_Tensor_fmap p q hk.
Proof.
  simpl.
  apply composite_ff'_comp_l.
  exact (`2 (fst fg)).
Qed.

Definition Centre_Tensor : (@Centre C B ∏ @Centre C B) ⟶ @Centre C B := {|
  fobj := Centre_Tensor_obj;
  fmap := Centre_Tensor_fmap;
  fmap_respects := Centre_Tensor_respects;
  fmap_id := Centre_Tensor_id;
  fmap_comp := Centre_Tensor_comp
|}.

(*
   * ** Z(C) is a monoidal category (Power–Robinson)

   Every equational field of [Monoidal] at the centre is, by the
   [Sub]-homset convention, an equation between underlying morphisms of
   C, and those equations are precisely the [composite_ff']-phrased
   translation lemmas of Structure/Premonoidal.v: the unitor squares and
   the triangle/pentagon via identity padding, and the associator
   squares via the joint naturality lemma (which needs no centrality at
   all).  This discharges the promise recorded above [central] in
   Structure/Binoidal.v. 

   --------
   * ** Z(C) 是一个单体范畴 (Power–Robinson)

   [Monoidal] 中心处的每一个方程场，根据 [Sub] 的 homset 约定，都是 C 的底层态射之间的方程，而这些方程正是 Structure/Premonoidal.v 中 [composite_ff'] 所表达的转换引理：通过恒等填充的统一子方形和三角形/五边形，以及通过联合自然性引理的结合子方形（完全不需要中心性）。这兑现了上面在 Structure/Binoidal.v 中记录的承诺 [central]。
*)

Definition Centre_Monoidal : @Monoidal (@Centre C B) :=
  @Build_Monoidal (@Centre C B)
    (@premon_I C B P; ttt)
    Centre_Tensor
    (fun p =>
       @Centre_lift_iso (Centre_Tensor_obj ((@premon_I C B P; ttt), p)) p
         (@premon_unit_left C B P (`1 p))
         (@premon_unit_left_central C B P (`1 p)))
    (fun p =>
       @Centre_lift_iso (Centre_Tensor_obj (p, (@premon_I C B P; ttt))) p
         (@premon_unit_right C B P (`1 p))
         (@premon_unit_right_central C B P (`1 p)))
    (fun p q r =>
       @Centre_lift_iso
         (Centre_Tensor_obj (Centre_Tensor_obj (p, q), r))
         (Centre_Tensor_obj (p, Centre_Tensor_obj (q, r)))
         (@premon_assoc C B P (`1 p) (`1 q) (`1 r))
         (@premon_assoc_central C B P (`1 p) (`1 q) (`1 r)))
    (fun p q g => premon_unit_left_natural_ff' (`1 g))
    (fun p q g => premon_unit_left_natural_from_ff' (`1 g))
    (fun p q g => premon_unit_right_natural_ff' (`1 g))
    (fun p q g => premon_unit_right_natural_from_ff' (`1 g))
    (fun p q r s t u g h i =>
       premon_joint_assoc_natural (`1 g) (`1 h) (`1 i))
    (fun p q r s t u g h i =>
       premon_joint_assoc_natural_from (`1 g) (`1 h) (`1 i))
    (fun p q => @premon_triangle_ff' C B P (`1 p) (`1 q))
    (fun p q r s =>
       @premon_pentagon_ff' C B P (`1 p) (`1 q) (`1 r) (`1 s)).

End PremonoidalCentre.
