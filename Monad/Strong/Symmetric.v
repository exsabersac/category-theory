Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Functor.Strong.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Monad.Strong.

Generalizable All Variables.

(** Strong monads over a symmetric monoidal base: the full right strength.  / 对称幺半群基上的强单子：完全正确的强度。*)

(*
nLab: https://ncatlab.org/nlab/show/strong+monad
   nLab: https://ncatlab.org/nlab/show/commutative+monad

   Monad/Strong.v derives, for a strong monad M over a symmetric monoidal
   base, the braid-conjugated right strength

       rstr = M(β) ∘ t ∘ β  :  M x ⨂ y ~> M (x ⨂ y)

   together with its naturality ([rstr_natural]) and its two
   monad-compatibility laws ([rstr_ret], [rstr_join]) — but stops short of
   packaging it as a [RightStrongFunctor]: the two functor-level coherences
   (the ρ-law [rrstrength_id_right] and the α-law [rstrength_assoc]) need the
   braid/unitor coherence ρ ≈ λ ∘ β of Joyal & Street ("Braided tensor
   categories", Adv. Math. 102, 1993, Prop. 2.1), which the bare
   [SymmetricMonoidal] axiomatization does not hand out directly.  That
   coherence is now proved from the hexagons in
   Structure/Monoidal/Braided/Proofs.v ([braid_unit_left],
   [braid_unit_right]), and this file completes the programme:

   1. the naturality corollaries of the left and right strengths in
      single-variable rewrite form ([strength_natural_l/r],
      [rstr_natural_l/r]), the workhorses of every proof below and of the
      Kleisli premonoidal development (Monad/Kleisli/Premonoidal.v);

   2. the double-strength toolkit: unit laws for [dstr] and [dstr'] against
      ret in either factor ([dstr_ret_left], [dstr_ret_right],
      [dstr'_ret_left], [dstr'_ret_right]), joint naturality
      ([dstr_natural], [dstr'_natural]), and Führmann-style reassociation
      lemmas ([dstr_reassoc_left], [dstr_reassoc_left'],
      [dstr'_reassoc_right], [dstr'_reassoc_right']) that rebracket a double
      strength through an extra M-layer (Führmann, "Direct models of the
      computational lambda-calculus", MFPS 1999);

   3. the two missing coherences [rstr_id_right] and [rstr_assoc], plus the
      mixed associativity coherence [strength_rstr_assoc] relating the left
      and the derived right strength across the associator — the key lemma
      behind associativity of the premonoidal tensor on Kl(M);

   4. the packaging: [rstr_nat] (the right strength as a natural
      transformation (⨂) ◯ M ∏⟶ Id ⟹ M ◯ (⨂)), the instances
      [rstr_RightStrongFunctor] and [rstr_RightStrongMonad], and the bridge
      between the concrete commutativity predicate [commutative_sm] and the
      abstract [CommutativeStrongMonad] class, in both directions
      ([commutative_CommutativeStrongMonad], [CSM_commutative_sm]) with the
      round trip [commutative_sm_round_trip].

   The bridge's converse direction is honest: an abstract
   [CommutativeStrongMonad] bundles its own right strength, which need not
   be the braid-derived one, so the converse takes the agreement of the two
   right strengths as an explicit hypothesis.  At the instance produced by
   the forward direction that hypothesis holds by reflexivity, which is
   exactly the round-trip corollary. 

--------
nLab：https://ncatlab.org/nlab/show/strong+monad
 nLab：https://ncatlab.org/nlab/show/commutative+monad

Monad/Strong.v 推导，对于对称幺半群上的强单子 M
 基底，编织物共轭右强度

rstr = M(β) ∘ t ∘ β : M x ⨂ y ~> M (x ⨂ y)

连同它的自然性（[rstr_natural]）和它的两个
 monad 兼容性法则（[rstr_ret]、[rstr_join]）——但还不够
 将其包装为 [RightStrongFunctor]：两个函子级一致性
 （ρ 律 [rrstrength_id_right] 和 α 律 [rstrength_assoc]）需要
 Joyal & Street 的辫子/单位相干性 ρ ≈ λ ∘ β (“辫子张量
 类别”，Adv. Math. 102, 1993, Prop. 2.1），其中
 [SymmetricMonoidal] 公理化不直接分发。 那
 现在从六边形中证明了一致性
 结构/单峰/编织/Proofs.v（[braid_unit_left]，
 [braid_unit_right])，该文件完成了程序：

1.左右优势的自然推论
 单变量重写形式（[strength_natural_l/r]，
 [rstr_natural_l/r]），下面每个证明的主力
 Kleisli premonoidal 发育 (Monad/Kleisli/Premonoidal.v)；

2.双强工具包：针对[dstr]和[dstr']的单位法则
 ret 任一因素（[dstr_ret_left]、[dstr_ret_right]、
 [dstr'_ret_left]、[dstr'_ret_right])、关节自然度
 （[dstr_natural]、[dstr'_natural]）和 Führmann 式重新关联
 引理（[dstr_reassoc_left]、[dstr_reassoc_left']、
 [dstr'_reassoc_right]、[dstr'_reassoc_right']）重新安装双
 通过额外的 M 层增强强度（Führmann，“直接模型
 计算 lambda 演算”，MFPS 1999）；

3. 两个缺失的相干性 [rstr_id_right] 和 [rstr_assoc]，加上
 混合关联性一致性 [strength_rstr_assoc] 与左侧相关
 以及通过关联器导出的正确强度——关键引理
 Kl(M) 上前幺半群张量的关联性背后；

4. 包装：[rstr_nat]（天然强度合适）
 变换 (⨂) ◯ M ∏⟶ Id ⟹ M ◯ (⨂))，实例
 [rstr_RightStrongFunctor] 和 [rstr_RightStrongMonad]，以及桥接器
 具体交换性谓词 [commutative_sm] 和
 抽象 [CommutativeStrongMonad] 类，双向
 （[commutative_CommutativeStrongMonad]、[CSM_commutative_sm]）与
 往返 [commutative_sm_round_trip]。

桥的相反方向是诚实的：抽象
 [CommutativeStrongMonad] 捆绑了其自身的优势，无需
 是辫子派生的，所以反过来取两者的一致
 正确的优势作为明确的假设。 在产生的实例中
 假设通过自反性所持有的前进方向，即
 正是往返的必然结果。 
*)

Section StrongSymmetric.

Context {C : Category}.
Context `{SM : @SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{SMon : @StrongMonad C _ M}.

(* ------------------------------------------------------------------ *)
(** ** Naturality corollaries in single-variable rewrite form.           / ** 单变量重写形式的自然推论。*)
(* ------------------------------------------------------------------ *)

(* Clean the identity components out of a joint naturality square.  / 从联合自然性方块中清除身份组件。*)
Local Ltac cleanup_nat SN :=
  repeat (rewrite ?bimap_id_id in SN; rewrite ?fmap_id in SN);
  rewrite ?id_left, ?id_right in SN.

(* Massage a joint (factored) naturality square into single-bimap form.  / 将关节​​（因子）自然方块按摩成单 bimap 形式。*)
Local Ltac fuse_nat SN :=
  rewrite <- ?fmap_comp in SN;
  rewrite <- ?comp_assoc in SN;
  rewrite ?bimap_id_left_right in SN.

Lemma strength_natural_l {x y z} (g : x ~> y) :
  fmap[M] (g ⨂ id[z]) ∘ strength[M] ≈ strength[M] ∘ (g ⨂ id[M z]).
Proof.
  pose proof (@strength_natural _ _ M _ x y g z z (id[z])) as SN.
  simpl in SN.
  cleanup_nat SN.
  exact SN.
Qed.

Lemma strength_natural_r {x z w} (h : z ~> w) :
  fmap[M] (id[x] ⨂ h) ∘ strength[M] ≈ strength[M] ∘ (id[x] ⨂ fmap[M] h).
Proof.
  pose proof (@strength_natural _ _ M _ x x (id[x]) z w h) as SN.
  simpl in SN.
  cleanup_nat SN.
  exact SN.
Qed.

Lemma rstr_natural_l {x z y} (f : x ~> z) :
  fmap[M] (f ⨂ id[y]) ∘ rstr ≈ rstr ∘ (fmap[M] f ⨂ id[y]).
Proof.
  pose proof (@rstr_natural _ _ M _ x z y y f (id[y])) as RN.
  rewrite ?fmap_id in RN.
  exact RN.
Qed.

Lemma rstr_natural_r {x y w} (g : y ~> w) :
  fmap[M] (id[x] ⨂ g) ∘ rstr ≈ rstr ∘ (id[M x] ⨂ g).
Proof.
  pose proof (@rstr_natural _ _ M _ x x y w (id[x]) g) as RN.
  rewrite ?fmap_id in RN.
  exact RN.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The double-strength toolkit: unit laws and naturality.            / ** 双强度工具包：单位定律和自然性。*)
(* ------------------------------------------------------------------ *)

(*
Feeding a returned value into the left factor of [dstr] leaves just the
   left strength: the rstr leg collapses by [rstr_ret] and [join_ret]. 

--------
将返回值输入 [dstr] 的左侧因子中，仅留下
 左侧力量：rstr 腿因 [rstr_ret] 和 [join_ret] 而塌陷。 
*)
Lemma dstr_ret_left {x y} :
  dstr ∘ (ret[M] ⨂ id[M y]) ≈ (strength[M] : x ⨂ M y ~> M (x ⨂ y)).
Proof.
  unfold dstr.
  rewrite <- !comp_assoc.
  rewrite rstr_ret.
  rewrite <- fmap_ret.
  rewrite comp_assoc.
  rewrite join_ret.
  now rewrite id_left.
Qed.

(*
Mirror: feeding a returned value into the right factor of [dstr'] leaves
   just the derived right strength. 

--------
镜像：将返回值输入 [dstr'] 叶子的正确因子中
 只是衍生出正确的力量。 
*)
Lemma dstr'_ret_right {x y} :
  dstr' ∘ (id[M x] ⨂ ret[M]) ≈ (rstr : M x ⨂ y ~> M (x ⨂ y)).
Proof.
  unfold dstr'.
  rewrite <- !comp_assoc.
  rewrite strength_ret.
  rewrite <- fmap_ret.
  rewrite comp_assoc.
  rewrite join_ret.
  now rewrite id_left.
Qed.

(*
The two cross unit laws: [dstr'] against ret on the left and [dstr]
   against ret on the right.  Here the returned value enters the *outer*
   strength of the composite, so the collapse goes through naturality
   (pushing ret across the strength), the opposite compatibility law under
   fmap, and [join_fmap_ret]. 

--------
两个跨单位法则：左边的 [dstr'] 对抗 ret 和 [dstr]
 反对右边的ret。 这里返回值进入*outer*
 复合材料的强度，因此塌陷是自然发生的
 （将 ret 推过强度），相反的相容律
 fmap 和 [join_fmap_ret]。 
*)
Lemma dstr'_ret_left {x y} :
  dstr' ∘ (ret[M] ⨂ id[M y]) ≈ (strength[M] : x ⨂ M y ~> M (x ⨂ y)).
Proof.
  unfold dstr'.
  rewrite <- !comp_assoc.
  rewrite <- strength_natural_l.
  rewrite (comp_assoc (fmap[M] rstr)).
  rewrite <- fmap_comp.
  rewrite rstr_ret.
  rewrite comp_assoc.
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

Lemma dstr_ret_right {x y} :
  dstr ∘ (id[M x] ⨂ ret[M]) ≈ (rstr : M x ⨂ y ~> M (x ⨂ y)).
Proof.
  unfold dstr.
  rewrite <- !comp_assoc.
  rewrite <- rstr_natural_r.
  rewrite (comp_assoc (fmap[M] strength[M])).
  rewrite <- fmap_comp.
  rewrite strength_ret.
  rewrite comp_assoc.
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

(*
Both factors pure at once: the double strength collapses to the unit.
   Shared by [kl_pure_tensor] (Monad/Kleisli/Commutative.v) and the
   thunkability development (Monad/Thunkable.v). 

--------
这两个因素同时纯粹：双倍强度分解为单位。 
由 [kl_pure_tensor] (Monad/Kleisli/Commutative.v) 和
 thunkability 开发 (Monad/Thunkable.v)。 
*)
Lemma dstr_ret_ret {x y} :
  dstr ∘ (ret[M] ⨂ ret[M]) ≈ (ret[M] : x ⨂ y ~{C}~> M (x ⨂ y)).
Proof.
  transitivity (dstr ∘ ((ret[M] ⨂ id[M y]) ∘ (id[x] ⨂ ret[M]))).
  - apply compose_respects; [reflexivity|].
    rewrite <- bimap_comp.
    now rewrite id_left, id_right.
  - rewrite comp_assoc.
    rewrite dstr_ret_left.
    apply strength_ret.
Qed.

Lemma dstr_natural {x y z w} (u : x ~> z) (v : y ~> w) :
  fmap[M] (u ⨂ v) ∘ dstr ≈ dstr ∘ (fmap[M] u ⨂ fmap[M] v).
Proof.
  unfold dstr.
  rewrite !comp_assoc.
  rewrite <- join_fmap_fmap.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  pose proof (@strength_natural _ _ M _ x z u y w v) as SN.
  simpl in SN.
  fuse_nat SN.
  rewrite <- (@rstr_natural _ _ M _ x z (fobj[M] y) (fobj[M] w) u (fmap[M] v)).
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  rewrite SN.
  reflexivity.
Qed.

Lemma dstr'_natural {x y z w} (u : x ~> z) (v : y ~> w) :
  fmap[M] (u ⨂ v) ∘ dstr' ≈ dstr' ∘ (fmap[M] u ⨂ fmap[M] v).
Proof.
  unfold dstr'.
  rewrite !comp_assoc.
  rewrite <- join_fmap_fmap.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  pose proof (@strength_natural _ _ M _ (fobj[M] x) (fobj[M] z) (fmap[M] u) y w v) as SN.
  simpl in SN.
  fuse_nat SN.
  rewrite <- SN.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  rewrite (@rstr_natural _ _ M _ x z y w u v).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Führmann's reassociation lemmas.                                  / ** 富尔曼的重联想引理。*)
(* ------------------------------------------------------------------ *)

(*
Rebracketing [dstr] through an extra M-layer on the left factor: for ANY
   f, applying [fmap ret] to the left component and then collapsing with
   join ∘ fmap rstr computes [dstr] again. 

--------
通过左侧因子上的额外 M 层重新包围 [dstr]：对于 ANY
 f，将 [fmap ret] 应用于左侧组件，然后折叠
 join ∘ fmap rstr 再次计算 [dstr]。 
*)
Lemma dstr_reassoc_left {a b c d} (f : a ~> M b) (g : c ~> M d) :
  join[M] ∘ fmap[M] rstr ∘ dstr ∘ ((fmap[M] ret[M] ∘ f) ⨂ g)
    ≈ dstr ∘ (f ⨂ g).
Proof.
  assert (E : (fmap[M] ret[M] ∘ f) ⨂ g ≈ (fmap[M] ret[M] ⨂ id) ∘ (f ⨂ g)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite E; clear E.
  rewrite <- (@fmap_id _ _ M d).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ dstr).
  rewrite <- dstr_natural.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[M] rstr)).
  rewrite <- fmap_comp.
  rewrite rstr_ret.
  rewrite (comp_assoc join[M]).
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

(*
The same expression with a bare ret in place of fmap ret instead
   computes the sibling double strength [dstr']. 

--------
相同的表达式，用裸 ret 代替 fmap ret
 计算同级双倍强度 [dstr']。 
*)
Lemma dstr_reassoc_left' {a b c d} (f : a ~> M b) (g : c ~> M d) :
  join[M] ∘ fmap[M] rstr ∘ dstr ∘ ((ret[M] ∘ f) ⨂ g)
    ≈ dstr' ∘ (f ⨂ g).
Proof.
  assert (E : (ret[M] ∘ f) ⨂ g ≈ (ret[M] ⨂ id[M d]) ∘ (f ⨂ g)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite E; clear E.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ dstr).
  rewrite dstr_ret_left.
  unfold dstr'.
  reflexivity.
Qed.

(* Mirror reassociation on the right factor of [dstr'].  / 镜像重新关联 [dstr'] 的正确因子。*)
Lemma dstr'_reassoc_right {a b c d} (g : c ~> M d) (f : a ~> M b) :
  join[M] ∘ fmap[M] strength[M] ∘ dstr' ∘ (g ⨂ (fmap[M] ret[M] ∘ f))
    ≈ dstr' ∘ (g ⨂ f).
Proof.
  assert (E : g ⨂ (fmap[M] ret[M] ∘ f) ≈ (id ⨂ fmap[M] ret[M]) ∘ (g ⨂ f)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite E; clear E.
  rewrite <- (@fmap_id _ _ M d).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ dstr').
  rewrite <- dstr'_natural.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[M] strength[M])).
  rewrite <- fmap_comp.
  rewrite strength_ret.
  rewrite (comp_assoc join[M]).
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

(* Mirror: the bare-ret variant computes [dstr].  / 镜子：bare-ret 变体计算 [dstr]。*)
Lemma dstr'_reassoc_right' {a b c d} (g : c ~> M d) (f : a ~> M b) :
  join[M] ∘ fmap[M] strength[M] ∘ dstr' ∘ (g ⨂ (ret[M] ∘ f))
    ≈ dstr ∘ (g ⨂ f).
Proof.
  assert (E : g ⨂ (ret[M] ∘ f) ≈ (id[M d] ⨂ ret[M]) ∘ (g ⨂ f)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite E; clear E.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ dstr').
  rewrite dstr'_ret_right.
  unfold dstr.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The two right-strength coherences.                                / ** 二正劲相干。*)
(* ------------------------------------------------------------------ *)

(*
Kock's associativity law for the left strength, solved for the composite
   strength ∘ (id ⨂ strength): every proof below uses it in this
   orientation, which requires no bracket surgery at the rewrite site. 

--------
左强度的Coq结合律，求解复合
 强度 ∘ (id ⨂ 强度)：下面的每个证明都使用它
 定向，无需在重写部位进行托槽手术。 
*)
Lemma strength_assoc_solved {a b c} :
  strength[M] ∘ (id[a] ⨂ strength[M])
    ≈ fmap[M] (to (@tensor_assoc _ _ a b c)) ∘ strength[M]
        ∘ from (@tensor_assoc _ _ a b (M c)).
Proof.
  rewrite strength_assoc.
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

(*
The braid-word coherence at the heart of both associativity proofs: the
   two ways of moving the outer factor a of (c ⨂ b) ⨂ a to the front — braid
   the inner pair first and then braid a across the tensor, or braid a
   across in one step on either side of the associator — agree.  It is the
   hexagon [hexagon_b] composed against the solved hexagon
   [hexagon_a_solved], glued by naturality of the braiding. 

--------
辫子词连贯性是两个关联性证明的核心：
 将 (c ⨂ b) ⨂ a 的外部因子 a 移到前面的两种方法 — 辫子
 首先将内部对，然后将 a 编织到张量上，或者将 a 编织
 一步跨过关联器的任一侧——同意。 它是
 六边形 [hexagon_b] 根据已解决的六边形组成
 [hexagon_a_solved]，通过自然的编织粘合。 
*)
Lemma braid_swap_assoc {a b c} :
  from (@tensor_assoc _ _ a b c) ∘ (braid ∘ (braid ⨂ id[a]))
    ≈ (braid ∘ ((id[c] ⨂ braid) ∘ to (@tensor_assoc _ _ c b a))
         : (c ⨂ b) ⨂ a ~> (a ⨂ b) ⨂ c).
Proof.
  rewrite <- bimap_braid.
  rewrite hexagon_b.
  rewrite hexagon_a_solved.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(*
The same coherence solved against the associator: precomposing the braid
   word with to tensor_assoc on the left cancels the inverse associator. 

--------
针对关联器解决了相同的连贯性：预合成辫子
 左侧带有 totensor_assoc 的单词取消逆关联器。 
*)
Lemma braid_swap_assoc_solved {a b c} :
  to (@tensor_assoc _ _ a b c) ∘ braid ∘ (id[c] ⨂ braid)
    ∘ to (@tensor_assoc _ _ c b a)
    ≈ (braid ∘ (braid ⨂ id[a]) : (c ⨂ b) ⨂ a ~> a ⨂ (b ⨂ c)).
Proof.
  rewrite <- !comp_assoc.
  rewrite <- braid_swap_assoc.
  rewrite (cancel_to_from_cons tensor_assoc).
  reflexivity.
Qed.

(*
The ρ-coherence of the derived right strength: M(ρ) ∘ rstr ≈ ρ.  The
   braid/unitor exchange of Joyal & Street ([braid_unit_right]) turns the
   fused fmap argument ρ ∘ β into λ, the left strength's own unit coherence
   [strength_id_left] absorbs it, and [braid_unit_left] at M x closes the
   remaining λ ∘ β. 

--------
导出的右强度的 ρ 相干性：M(ρ) ∘ rstr ≈ ρ。 的
 Joyal & Street ([braid_unit_right]) 的辫子/单元交换将
 将 fmap 参数 ρ ∘ β 融合为 λ，左强度自身的单位相干性
 [strength_id_left] 吸收它，[braid_unit_left] 在 M x 处关闭
 剩余 λ ∘ β。 
*)
Lemma rstr_id_right {x} :
  fmap[M] (to unit_right) ∘ rstr ≈ to (@unit_right _ _ (M x)).
Proof.
  unfold rstr.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite braid_unit_right.
  rewrite strength_id_left.
  apply braid_unit_left.
Qed.

(*
The α-coherence of the derived right strength, in the to-oriented form
   from which the class field's from-oriented form follows by iso
   cancellation.  The chase: unfold rstr, slide the braids outward by
   naturality of the braiding and of the strength, absorb the two stacked
   strengths with [strength_assoc_solved], convert the residual braid word
   with [braid_swap_assoc], and finish with [braid_swap_assoc_solved] inside
   the fmap argument. 

--------
导出的正确强度的 α 连贯性，以 to 为导向的形式
 类字段的面向 from 的形式遵循 iso
 取消。 追逐：展开rstr，将辫子向外滑动
 编织的自然性和强度，吸收两个堆叠的
 与[strength_assoc_solved]的长处，转换残辫子字
 带有 [braid_swap_assoc]，并在内部带有 [braid_swap_assoc_solved]
 fmap 参数。 
*)
Lemma rstr_assoc_to {x y z} :
  fmap[M] (to (@tensor_assoc _ _ x y z)) ∘ rstr ∘ bimap rstr id
    ≈ rstr ∘ to (@tensor_assoc _ _ (M x) y z).
Proof.
  unfold rstr.
  rewrite <- !comp_assoc.
  rewrite <- bimap_braid.
  rewrite !bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (id[z] ⨂ fmap[M] braid)).
  rewrite <- strength_natural_r.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (id[z] ⨂ strength[M])).
  rewrite strength_assoc_solved.
  rewrite <- !comp_assoc.
  rewrite bimap_braid.
  rewrite braid_swap_assoc.
  rewrite (comp_assoc braid (id[M x] ⨂ braid)).
  rewrite <- bimap_braid.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (braid ⨂ id[M x])).
  rewrite <- strength_natural_l.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  rewrite braid_swap_assoc_solved.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite braid_invol.
  rewrite id_left.
  rewrite bimap_id_id.
  now rewrite id_right.
Qed.

(* The α-coherence in the [RightStrongFunctor] field orientation.  / [RightStrongFunctor] 场方向的 α 相干性。*)
Lemma rstr_assoc {x y z} :
  rstr ∘ bimap rstr id ∘ from (@tensor_assoc _ _ (M x) y z)
    ≈ fmap[M] (from (@tensor_assoc _ _ x y z)) ∘ rstr.
Proof.
  apply (iso_to_epic tensor_assoc).
  rewrite <- !comp_assoc.
  rewrite iso_from_to.
  rewrite id_right.
  rewrite <- rstr_assoc_to.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite iso_from_to.
  rewrite fmap_id.
  now rewrite id_left.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The mixed associativity coherence.                                / ** 混合联想性连贯性。*)
(* ------------------------------------------------------------------ *)

(*
The coherence that mixes the left strength and the derived right
   strength across the associator:

       M(α) ∘ rstr ∘ (t ⨂ id) ≈ t ∘ (id ⨂ rstr) ∘ α

   on (x ⨂ M y) ⨂ z.  This is the hardest single equation of the
   development; its sole consumer is the middle-associativity naturality
   square of the Kleisli premonoidal tensor
   (kl_assoc_natural_middle in Monad/Kleisli/Premonoidal.v).

   The proof is staged: first the symmetric hexagon in solved "cons" form
   (assert S1), which rewrites the inverse-associator-after-braid tail of
   the unfolded left side; then naturality of the strength slides the
   remaining braid under fmap; both sides collapse onto a common
   strength-spine, and the residual fmap argument is the first hexagon plus
   [braid_invol].

   A fallback route, recorded for maintainers: the same equation can
   instead be established at its point of use, by inlining the statement
   into the proof of [kl_assoc_natural_middle] and staging further
   intermediate asserts there against the unfolded Kleisli composite; the
   ingredients — the hexagon lemmas, the strength coherences and
   [braid_invol] — are unchanged, only the staging site moves. 

--------
在结合器中混合左强度和导出右强度的相干性：

M(α) ∘ rstr ∘ (t ⨂ id) ≈ t ∘ (id ⨂ rstr) ∘ α

在 (x ⨂ M y) ⨂ z 上。这是整个开发过程中最难的单个方程；它唯一的使用者是 Kleisli 前单模张量的中间结合律自然性方框（Monad/Kleisli/Premonoidal.v 中的 kl_assoc_natural_middle）。

证明是分阶段的：首先是已解“cons”形式的对称六边形（断言 S1），它重写了展开的左侧的逆结合子后缀的尾部；然后强度的自然性将剩余的编织滑动到 fmap 下；两边都塌缩到一个共同的强度主干上，剩余的 fmap 参数是第一个六边形加上 [braid_invol]。

一个备用路线，为维护者记录：同样的方程可以在其使用点建立，通过将语句内联到 [kl_assoc_natural_middle] 的证明中，并在那里针对展开的 Kleisli 复合物设置进一步的中间断言；成分——六边形引理、强度一致性和 [braid_invol]——保持不变，只是阶段站点移动了。 
*)
Lemma strength_rstr_assoc {x y z} :
  fmap[M] (to (@tensor_assoc _ _ x y z)) ∘ rstr ∘ bimap strength[M] id
    ≈ strength[M] ∘ bimap id rstr ∘ to (@tensor_assoc _ _ x (M y) z).
Proof.
  (* Stage 1: the symmetric hexagon, solved for α⁻¹ ∘ β.  / 第 1 阶段：对称六边形，求解 α⁻1 ∘ β。*)
  assert (S1 : from (@tensor_assoc _ _ z x (M y))
                 ∘ @braid C _ (x ⨂ M y)%object z
                 ≈ (braid ⨂ id[M y])
                     ∘ (from (@tensor_assoc _ _ x z (M y))
                          ∘ ((id[x] ⨂ braid)
                               ∘ to (@tensor_assoc _ _ x (M y) z)))).
  { apply (iso_to_epic (iso_sym tensor_assoc)).
    rewrite <- !comp_assoc.
    rewrite iso_to_from.
    rewrite id_right.
    rewrite !comp_assoc.
    apply hexagon_identity_sym. }
  unfold rstr.
  rewrite <- !comp_assoc.
  (* Stage 2: normalize both sides onto the common strength-spine.  / 第二阶段：将两侧标准化到共同的力量脊柱上。*)
  rewrite <- bimap_braid.
  rewrite !bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (id[x] ⨂ fmap[M] braid)).
  rewrite <- strength_natural_r.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (id[z] ⨂ strength[M])).
  rewrite (comp_assoc strength[M] (id[x] ⨂ strength[M])).
  rewrite !strength_assoc_solved.
  rewrite <- !comp_assoc.
  rewrite S1.
  rewrite (comp_assoc strength[M] (braid ⨂ id[M y])).
  rewrite <- strength_natural_l.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  (* Stage 3: the residual braid word is the first hexagon plus invol.  / 第三阶段：残留辫子字是第一个六边形加invol。*)
  rewrite hexagon_identity.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite braid_invol.
  rewrite id_left.
  rewrite bimap_id_id.
  now rewrite id_right.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Packaging: the right strong functor and right strong monad.       / ** 包装：正确的强函子和正确的强单子。*)
(* ------------------------------------------------------------------ *)

(*
The derived right strength as a natural transformation
   (⨂) ◯ M ∏⟶ Id ⟹ M ◯ (⨂): the shape demanded by the
   [RightStrongFunctor] field.  The component at (x, y) is definitionally
   [rstr], so the coherence laws transfer on the nose. 

--------
作为自然变换而导出的正确力量
 (⨂) ◯ M ∏⟶ Id ⟹ M ◯ (⨂): 所要求的形状
 [RightStrongFunctor] 字段。 (x, y) 处的分量定义为
 [rstr]，因此相干定律转移到鼻子上。 
*)
Definition rstr_nat : (⨂) ◯ M ∏⟶ Id ⟹ M ◯ (⨂).
Proof using C M SM SMon.
  refine (@Build_Transform' (C ∏ C) C ((⨂) ◯ M ∏⟶ Id) (M ◯ (⨂))
            (fun p => match p with (x, y) => @rstr C SM M SMon x y end) _).
  intros [x1 x2] [y1 y2] [f g]; simpl.
  exact (@rstr_natural C SM M SMon x1 y1 x2 y2 f g).
Defined.

(*
The packaging that Monad/Strong.v deferred: rstr, with the ρ- and
   α-coherences proved above, is a [RightStrongFunctor] structure on M. 

--------
Monad/Strong.v 推迟的包装：rstr，带有 ρ- 和
 上面证明的α-相干性是M上的[RightStrongFunctor]结构。 
*)
Definition rstr_RightStrongFunctor : @RightStrongFunctor C _ M :=
  @Build_RightStrongFunctor C _ M
    rstr_nat
    (fun x => @rstr_id_right x)
    (fun x y z => @rstr_assoc x y z).

(* Sanity check: the packaged right strength is definitionally [rstr].  / 健全性检查：包装的正确强度定义为 [rstr]。*)
Corollary rstrength_is_rstr {x y} :
  @rstrength C _ M rstr_RightStrongFunctor x y ≈ rstr.
Proof. reflexivity. Qed.

(*
Together with the monad-compatibility laws [rstr_ret] and [rstr_join]
   from Monad/Strong.v, every strong monad over a symmetric base is a right
   strong monad. 

--------
与 monad 兼容性法则 [rstr_ret] 和 [rstr_join] 一起
 来自 Monad/Strong.v，对称基上的每个强 monad 都是一个右
 强单子。 
*)
Definition rstr_RightStrongMonad : @RightStrongMonad C _ M :=
  @Build_RightStrongMonad C _ M
    strongmonad_is_monad
    rstr_RightStrongFunctor
    (fun x y => @rstr_ret C SM M SMon x y)
    (fun x y => @rstr_join C SM M SMon x y).

(* ------------------------------------------------------------------ *)
(** ** The bridge to [CommutativeStrongMonad].                           / ** [CommutativeStrongMonad] 的桥梁。*)
(* ------------------------------------------------------------------ *)

(*
Forward direction: the concrete commutativity predicate over the derived
   right strength yields the abstract class.  Both sides of the
   [commutativity] field are definitionally [dstr] and [dstr'] once the
   packaged rstrength unfolds to [rstr]. 

--------
前向：导出的具体交换性谓词
 正确的强度产生抽象类。 两侧
 [commutativity] 字段定义为 [dstr] 和 [dstr'] 一旦
 打包的 rstrength 展开为 [rstr]。 
*)
Definition commutative_CommutativeStrongMonad
  (comm : @commutative_sm C SM M SMon) : @CommutativeStrongMonad C _ M :=
  @Build_CommutativeStrongMonad C _ M
    SMon
    rstr_RightStrongFunctor
    (fun x y => @rstr_ret C SM M SMon x y)
    (fun x y => @rstr_join C SM M SMon x y)
    (fun x y => comm x y).

(*
Converse direction.  An abstract [CommutativeStrongMonad] carries its own
   bundled right strength, which need not be the braid-derived one, so the
   honest converse takes the agreement E of the two right strengths — over
   the strong monad bundled in H' itself — as an explicit hypothesis and
   produces the concrete predicate for that strong monad. 

--------
逆转方向。 抽象 [CommutativeStrongMonad] 拥有自己的
 捆绑正确的强度，不一定是辫子衍生的强度，所以
 诚实的对话需要两个正确优势的一致 E — 结束
 强单子捆绑在 H' 本身中——作为一个明确的假设和
 产生该强单子的具体谓词。 
*)
Definition CSM_commutative_sm
  (H' : @CommutativeStrongMonad C _ M)
  (E : ∀ x y, @rstrength C _ M (@comm_is_rstrong C _ M H') x y
                ≈ @rstr C SM M (@comm_is_strong C _ M H') x y) :
  @commutative_sm C SM M (@comm_is_strong C _ M H').
Proof.
  intros x y.
  unfold dstr, dstr'.
  rewrite <- !E.
  exact (@commutativity C _ M H' x y).
Qed.

(*
Round trip: at the instance produced by the forward direction, the
   agreement hypothesis holds by reflexivity — the packaged right strength
   IS rstr — and the underlying strong monad is definitionally the ambient
   one, so the composite of the two bridges reproduces a commutativity
   witness for the ambient strong monad. 

--------
往返行程：在向前方向产生的情况下，
 一致假设通过自反性成立——打包的正确强度
 IS rstr — 底层的强单子定义为环境
 一，因此两个桥的复合再现了交换律
 环境强单子的见证。 
*)
Corollary commutative_sm_round_trip
  (comm : @commutative_sm C SM M SMon) : @commutative_sm C SM M SMon.
Proof.
  apply (CSM_commutative_sm (commutative_CommutativeStrongMonad comm)).
  intros x y.
  reflexivity.
Qed.

End StrongSymmetric.
