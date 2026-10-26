Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Closed.

Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(*
   * * Awodey's topological caveat: the inverse image on OPENS

   Awodey, “Category Theory”, §9.4 Example 9.12.  There is no page image
   for that book here, so the clause is quoted from the catalog issue's
   own transcription: after the direct-image / inverse-image adjunction
   on power sets, Awodey observes that for a continuous map the inverse
   image on OPEN SETS keeps its right adjoint but need not keep its left
   one, because the direct image of an open set need not be open.

   nLab: https://ncatlab.org/nlab/show/frame
   nLab: https://ncatlab.org/nlab/show/locale
   nLab: https://ncatlab.org/nlab/show/inverse+image
   nLab: https://ncatlab.org/nlab/show/interior

   ** WHAT IS DELIVERED, WITH GRADES

   (A) [Opens_preimage g : Opens X ⟶ Opens Y] for a continuous
   [g : Y ~> X], the inverse image on opens AS A FUNCTOR.  Its object
   action IS Instance/Top/Closed.v's [open_preimage] at [eq_refl]
   ([Opens_preimage_obj]); that constant was an object assignment
   only, with no arrow action, and NO functor in the tree had it as
   its object action -- Instance/Top/Closed.v's [OpensF] uses it
   in its ARROW action only, its object action being the
   setoid of opens of a SPACE, and it lands in [Sets] rather than in
   the category [Opens].  Read the claim at that
   scope: functors out of [Opens] do exist, namely
   Instance/Top/Closed.v's [OpenCompl] and its inverse, which
   are complementation and not preimage.  All three functor laws
   are free: [Opens] has the trivial hom-setoid, so every one of
   them is an equation between parallel arrows of a thin category.

   (B) THE NEGATIVE HALF, PROVED, not asserted.  [NatInf_Top] is
   [option nat] under Leibniz equality with [None] playing infinity:
   a predicate is open exactly when, IF it contains infinity, it
   contains a tail.  [TopSpace] has seven fields: the two data
   fields are the carrier and the openness predicate, and the five
   proof fields are discharged by named lemmas (the union takes the
   tail of whichever member contains infinity, the intersection the
   larger of two tails).  [nat_inf_point] is the
   constant map from the one-point space at infinity, continuous for
   free because every predicate on a point is open.  Then
   **[nat_inf_no_left_adjoint]**: NO functor
   [L : Opens Point_Top ⟶ Opens NatInf_Top] is left adjoint to
   [Opens_preimage nat_inf_point].  The argument transposes twice:
   the identity at [L whole] shows [L whole] contains infinity, hence
   a tail from some [N]; the open [nat_inf_punctured N] (everything
   but [Some N]) pulls back to the whole point, so transposing the
   other way gives [L whole ⊆ nat_inf_punctured N], which at
   [Some N] is a contradiction.  The statement quantifies over
   [Adjunction] DIRECTLY: [Opens]' homs are [Type]-valued, so
   Instance/Proset/Galois.v's [GaloisConnection] -- whose relations
   must be [Prop]-valued -- does not apply here, unlike in
   Instance/Powerset.v.

   (C) THE POSITIVE HALF, AT ITS TRUE STRENGTH.  The GENERAL right
   adjoint is the interior of the dual image, a union over ALL opens
   contained in a predicate, and that union IS NOT FORMABLE in this
   [Top]: [OpenSet X : Type@{u}] sits one level ABOVE the points
   (Instance/Top/Closed.v with [u0 < u]) while [open_union]
   indexes only by [I : Type@{o}] at the points' level.  The
   rejection is pinned as the probe's formability negative, against
   [open_union] at a small index as the control; the same wall
   Instance/Top/Kolmogorov.v records for its indistinguishability
   relation.  Measured but NOT pinned: the [Powerset_squash]-truncated
   variant of that union DOES form as a Prop-valued predicate, but
   its openness is not derivable from [open_union] with a large
   index, so truncating relocates the obstruction rather than
   removing it.  What IS delivered is the right adjoint AT THE
   WITNESS: [nat_inf_right_adjoint] with
   **[nat_inf_preimage_adjunction : Opens_preimage nat_inf_point ⊣
   nat_inf_right_adjoint]** -- so at this one map the inverse image
   keeps its right adjoint and provably loses its left one, which is
   Awodey's sentence exactly.  No second space is built and no
   general positive statement is claimed.

   ** WHAT IS NOT DELIVERED

   No frame or locale structure on [Opens X], no interior operator, no
   general right adjoint, no direct image on opens (the very thing
   whose non-existence is the point), no relation to
   Instance/Powerset.v's [Subsets]
   (an open is not a subset in this presentation: [OpenSet] carries its
   openness as data and lives a universe up), and nothing about the
   closed-set side of Instance/Top/Closed.v.

   ** UNIVERSES

   [Opens X : Category@{u u0 u0}] with [u0 < u] is the donor's; every
   constant here inherits it.  [NatInf_Top] carries [Set < o], declared
   explicitly on [nat_inf_carrier], plus stdlib bounds and nothing more.
   Measured per constant in the report.

   ** TRANSPARENCY

   Two proofs here end in [Defined], [nat_inf_punctured_open] and the
   inline [point_into_punctured], because each produces Type-valued
   data ([IsOpen] is [Type]-valued); neither is read through by a later
   conversion, and each compiles as [Qed], measured by flipping.

   ** REGISTRATION

   Nothing here is an [Instance]. 

   --------
   * * 阿沃迪的拓扑警告：开集上的逆像

   阿沃迪，《范畴论》，§9.4 示例 9.12。本书此处没有页面图片，因此该条款引用自目录期刊自身的转录：在幂集的直像 / 逆像对偶之后，阿沃迪指出，对于连续映射，开集上的逆像保持其右伴随，但不一定保持左伴随，因为开集的直像不一定开。

   nLab:  https://ncatlab.org/nlab/show/frame 
   nLab:  https://ncatlab.org/nlab/show/locale 
   nLab:  https://ncatlab.org/nlab/show/inverse+image 
   nLab:  https://ncatlab.org/nlab/show/interior 

   ** 所交付的内容，以及成绩(A) 对于一个连续的 [g : Y ~> X]，开集上的逆像作为函子。它的对象作用是在 [eq_refl]（[Opens_preimage_obj]）处的 Instance/Top/Closed.v 的 [open_preimage]；该常数只是对象分配，没有箭头作用，并且树中的没有函子将其作为对象作用——Instance/Top/Closed.v 的 [OpensF] 仅在其箭头作用中使用它，其对象作用是一个空间开集的集合类，并且它落在 [Sets] 中，而不是在范畴 [Opens] 中。在该范围内阅读该主张：来自 [Opens] 的函子确实存在，即 Instance/Top/Closed.v 的 [OpenCompl] 及其逆，它们是补集而不是逆像。所有三条函子律都是自由的：[Opens] 具有平凡的同态集合，因此它们每一条都是薄范畴中平行箭头之间的等式。(B) 否定的一半，已证明，而非断言。[NatInf_Top] 是 [option nat]，在莱布尼茨等式下以 [None] 表示无穷大：当且仅当谓词包含无穷大时，它才是开集，它包含尾部。[TopSpace] 有七个字段：两个数据字段是载体和开集谓词，五个证明字段由命名引理解除（并集取包含无穷大的成员的尾部，交集取两个尾部中较大的一个）。[nat_inf_point] 是来自无穷大单点空间的恒定映射，对所有谓词都是开集，因此连续。然后 ** [nat_inf_no_left_adjoint] **：没有函子 [L : Opens Point_Top ⟶ Opens NatInf_Top] 是 [Opens_preimage nat_inf_point] 的左伴随。这个论证交换了两次：
   在 [L whole] 的恒等映射显示 [L whole] 包含无穷，因此
   来自某个 [N] 的尾部；开放的 [nat_inf_punctured N] （除了 [Some N] 的所有东西）回拉到整个点，因此反方向交换得到 [L whole ⊆ nat_inf_punctured N]，在 [Some N] 上是矛盾。该陈述直接对 [Adjunction] 进行量化：[Opens] 的同态值为 [Type]，因此 Instance/Proset/Galois.v 的 [GaloisConnection] ——其关系必须是 [Prop] 值——在这里不适用，不像在 Instance/Powerset.v 中。(C) 正半部分，在其真实强度下。一般右伴随是对偶像的内部，是包含在一个谓词中的所有开集的并集，而这个并集在这个 [Top] 中不可构造：[OpenSet X : Type@{u}] 位于点的上一级（Instance/Top/Closed.v 与 [u0 < u]），而 [open_union] 仅在点的层次按 [I : Type@{o}] 索引。拒绝被固定为探针的不可构造性，对小索引处的 [open_union] 作为控制；同样的壁 Instance/Top/Kolmogorov.v 记录其不可区分性关系。经过测量但未固定：[Powerset_squash] 的截断变体确实形成了一个值为命题的谓词，但它的开放性不能从具有较大指数的 [open_union] 推导出来，因此截断只是重新定位了障碍而不是消除了它。真正得到的是在 WITNESS 上的右伴随：[nat_inf_right_adjoint] 具有 **[nat_inf_preimage_adjunction : Opens_preimage nat_inf_point ⊣ nat_inf_right_adjoint]** ——所以在这一映射上，逆像保持其右伴随并可证明失去了其左伴随，这正是 Awodey 的句子。没有构建第二个空间，也没有声称一般的正面陈述。

   ** 未得到的内容[Opens X] 上没有框架或地方结构，没有内部算子，没有一般的右伴随，没有对开集的直接像（正是不存在的那个事物），与 Instance/Powerset.v 的 [Subsets] 没有关系（在此表示中开集不是子集：[OpenSet] 将其开集性作为数据携带，并存在于高一层宇宙中），关于 Instance/Top/Closed.v 的闭集方面也没有任何信息。

   ** 宇宙

   [Opens X : Category@{u u0 u0}] 与 [u0 < u] 属于捐赠者；这里的每个常量都继承它。[NatInf_Top] 携带 [Set < o]，在 [nat_inf_carrier] 上显式声明，加上 stdlib 的上界，没有更多内容。按报告中的每个常量测量。

   ** 透明性这里的两个证明以 [Defined]、[nat_inf_punctured_open] 结束，行内为 [point_into_punctured]，因为每个都生成类型值数据（[IsOpen] 是 [Type] 值）；之后的转换都没有读取它们，并且每个都作为 [Qed] 编译，通过翻转来测量。

   ** 注册

   这里没有任何 [Instance]。
*)

(* ------------------------------------------------------------------------ *)
(* * ** (A) The inverse image on opens, as a functor / * **（A）开集上的逆像，作为函子 *)

Program Definition Opens_preimage {X Y : TopSpace} (g : Y ~{Top}~> X) :
  Opens X ⟶ Opens Y := {|
  fobj := open_preimage g;
  fmap := fun U V (h : ∀ x : X, `1 U x → `1 V x) =>
            fun y (u : `1 U (g y)) => h (g y) u
|}.

Example Opens_preimage_obj {X Y : TopSpace} (g : Y ~{Top}~> X)
  (U : OpenSet X) : fobj[Opens_preimage g] U = open_preimage g U := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** (B) The space, and the refutation / * **（B）空间，以及反驳 *)

(* The points: the naturals with a point at infinity. / 这些点：自然数以及位于无穷远的点。 *)
Definition nat_inf_carrier@{o | Set < o +} : SetoidObject@{o o} :=
  {| carrier   := option nat
   ; is_setoid := eq_Setoid@{o} (option nat) |}.

(*
 A predicate is open when, if it holds at infinity, it holds on a tail.
 Predicates missing infinity are unconstrained -- so the topology is
 finer than the cofinite one and every subset of the naturals proper is
 open. 

 --------
 当一个谓词在无限处成立时，它在某个尾部也成立，我们称这个谓词是开放的。缺少无限的谓词没有约束——因此拓扑比有限余拓扑更细，并且自然数的每个真子集都是开放的。
*)
Definition nat_inf_open@{o} (U : nat_inf_carrier@{o} → Type@{o}) : Type@{o} :=
  U None → { N : nat & ∀ n : nat, (N <= n)%nat → U (Some n) }.

Lemma nat_inf_respects@{o} (U V : nat_inf_carrier@{o} → Type@{o}) :
  (∀ x, U x ↔ V x) → nat_inf_open U → nat_inf_open V.
Proof.
  intros HUV HU Hv.
  destruct (HU (snd (HUV None) Hv)) as [N k].
  exists N; intros n Hn; exact (fst (HUV (Some n)) (k n Hn)).
Qed.

Lemma nat_inf_proper@{o} (U : nat_inf_carrier@{o} → Type@{o}) :
  nat_inf_open U → ∀ x y : nat_inf_carrier, x ≈ y → U x → U y.
Proof. intros _ x y Hxy Ux; rewrite <- Hxy; exact Ux. Qed.

Lemma nat_inf_union@{o} (I : Type@{o})
  (U : I → (nat_inf_carrier@{o} → Type@{o})) :
  (∀ i, nat_inf_open (U i)) → nat_inf_open (fun x => { i : I & U i x }).
Proof.
  intros HU [i u].
  destruct (HU i u) as [N k].
  exists N; intros n Hn; exact (i; k n Hn).
Qed.

Lemma nat_inf_whole@{o} : nat_inf_open@{o} (fun _ => poly_unit@{o}).
Proof. intros _; exists 0%nat; intros n _; exact ttt. Qed.

Lemma nat_inf_inter@{o} (U V : nat_inf_carrier@{o} → Type@{o}) :
  nat_inf_open U → nat_inf_open V →
  nat_inf_open (fun x => U x ∧ V x).
Proof.
  intros HU HV [u v].
  destruct (HU u) as [N1 k1]; destruct (HV v) as [N2 k2].
  exists (Nat.max N1 N2); intros n Hn; split.
  - exact (k1 n (Nat.max_lub_l _ _ _ Hn)).
  - exact (k2 n (Nat.max_lub_r _ _ _ Hn)).
Qed.

Definition NatInf_Top@{o} : TopSpace@{o} := {|
  top_carrier    := nat_inf_carrier@{o};
  IsOpen         := nat_inf_open@{o};
  open_respects  := nat_inf_respects@{o};
  open_proper    := nat_inf_proper@{o};
  open_union     := nat_inf_union@{o};
  open_whole     := nat_inf_whole@{o};
  open_inter     := nat_inf_inter@{o}
|}.

(*
 The constant map from the point at infinity.  Continuity is free: the
 preimage of any predicate is a constant predicate on a one-point
 space, and [Point_Top] is discrete. 

 --------
 从无穷远点到常量的映射。连续性是免费的：任何谓词的原像是在一点评空间上的常量谓词，并且 [Point_Top] 是离散的。
*)
Definition nat_inf_point : Point_Top ~{Top}~> NatInf_Top := {|
  continuous_map :=
    const_morphism (top_carrier Point_Top) (top_carrier NatInf_Top) None;
  continuity := fun U _ x y _ h => h
|}.

(* The whole point, as an open of the one-point space. / 整个要点，作为单点空间的开端。 *)
Definition point_whole : OpenSet Point_Top :=
  (fun _ => poly_unit; open_whole Point_Top).

(*
 Everything except [Some N].  Written as ONE Prop-valued predicate
 rather than a two-branch match: a match with [poly_unit] at infinity
 and a negated equation at the naturals mixes [Type] with [Prop] and is
 rejected, whereas [∀ n, x = Some n → n = N → False] holds vacuously at
 infinity and is a [Prop] uniformly (Instance/Top/Kolmogorov.v's
 [tri_point_open] is the precedent for a Prop-valued open).  It is open
 because it contains the tail from N+1. 

 --------
 除了 [Some N] 之外的所有内容。写为一个 Prop 值谓词，而不是一个两分支匹配：一个在无穷处与 [poly_unit] 匹配且在自然数中为否定方程的匹配会混合 [Type] 与 [Prop] 并被拒绝，而 [∀ n, x = Some n → n = N → False] 在无穷处是空洞成立的，并且是一个 [Prop] 一致的（Instance/Top/Kolmogorov.v 的 [tri_point_open] 是 Prop 值开集的前例）。它是开放的，因为它包含从 N+1 起的尾部。
*)
Lemma nat_inf_punctured_open@{o +} (N : nat) :
  IsOpen NatInf_Top@{o}
    (fun x : NatInf_Top@{o} => ∀ n : nat, x = Some n → n = N → False).
Proof.
  intros _; exists (S N); intros n Hn m Hm HmN.
  assert (Hnm : n = m) by (injection Hm; intro h; exact h).
  rewrite Hnm, HmN in Hn.
  exact (PeanoNat.Nat.nle_succ_diag_l N Hn).
Defined.

Definition nat_inf_punctured@{o +} (N : nat) : OpenSet NatInf_Top@{o} :=
  existT _ _ (nat_inf_punctured_open@{o} N).

(*
 The preimage of a punctured open along the constant map at infinity is
 the whole point: the map lands at infinity, which every punctured open
 contains vacuously. 

 --------
 沿着无穷处常值映射的打空开集的原像是整个点：映射落在无穷处，而每个打空开集中都虚无地包含无穷处。
*)
Definition point_into_punctured (N : nat) :
  point_whole ~{Opens Point_Top}~> open_preimage nat_inf_point
                                     (nat_inf_punctured N).
Proof. intros pt _ n Hn; discriminate Hn. Defined.

(** THE REFUTATION. No left adjoint exists. / 反驳。不存在左伴随。 *)
Theorem nat_inf_no_left_adjoint
  (L : Opens Point_Top ⟶ Opens NatInf_Top)
  (A : L ⊣ Opens_preimage nat_inf_point) : False.
Proof.
  (*
 Transposing the identity at [L point_whole] shows that open contains
 infinity, hence a tail from some N. 

 --------
 在 [L point_whole] 上置换恒等式显示开集包含无穷大，因此存在从某个 N 开始的尾部。
*)
  pose proof (to (@adj _ _ _ _ A point_whole (L point_whole))
                (id[L point_whole])) as Hinf.
  destruct (`2 (L point_whole) (Hinf ttt ttt)) as [N k].
  (*
 Transposing the other way at the punctured open gives an inclusion
 of [L point_whole] into it, contradicted at [Some N]. 

 --------
 在穿孔开的地方以相反的方式移调会将 [L point_whole] 包含在其中，但在 [Some N] 处出现矛盾。
*)
  pose proof (from (@adj _ _ _ _ A point_whole (nat_inf_punctured N))
                (point_into_punctured N)) as Hincl.
  exact (Hincl (Some N) (k N (PeanoNat.Nat.le_refl N)) N eq_refl eq_refl).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** (C) The right adjoint, AT THIS WITNESS / * **（C）右伴随，在这个证人处 *)

(* [R U] holds at infinity exactly when [U] holds at the point, and holds at every natural. Open: if it contains infinity it contains the tail from 0, every natural being in it. / [R U] 当且仅当 [U] 在该点成立时才在无穷处成立，并且在每个自然数处成立。开放：如果它包含无穷，它就包含从 0 开始的尾部，每个自然数都包含在其中。 *)
Definition nat_inf_R_pred (U : OpenSet Point_Top) :
  NatInf_Top → Type :=
  fun x => match x with
           | None   => `1 U ttt
           | Some _ => poly_unit
           end.

Lemma nat_inf_R_open (U : OpenSet Point_Top) :
  IsOpen NatInf_Top (nat_inf_R_pred U).
Proof. intros _; exists 0%nat; intros n _; exact ttt. Qed.

Program Definition nat_inf_right_adjoint :
  Opens Point_Top ⟶ Opens NatInf_Top := {|
  fobj := fun U => (nat_inf_R_pred U; nat_inf_R_open U);
  fmap := fun U V (h : ∀ pt : Point_Top, `1 U pt → `1 V pt) =>
            fun x => match x
                     return nat_inf_R_pred U x → nat_inf_R_pred V x with
                     | None   => h ttt
                     | Some _ => fun w => w
                     end
|}.

(*
 The transposition.  Both directions are one-line implications at
 infinity, and the point's own [ttt] is recovered by case analysis on
 [poly_unit]. 

 --------
 转置。两个方向在无穷远处都是一行的蕴含，通过对 [poly_unit] 进行分类讨论，可以恢复该点自身的 [ttt]。
*)
Program Definition nat_inf_preimage_adjunction :
  Opens_preimage nat_inf_point ⊣ nat_inf_right_adjoint := {|
  adj := fun U V =>
    {| to   := {| morphism := fun h x =>
                    match x
                    return `1 U x → nat_inf_R_pred V x with
                    | None   => h ttt
                    | Some _ => fun _ => ttt
                    end |}
     ; from := {| morphism := fun k pt (u : `1 U (nat_inf_point pt)) =>
                    match pt return `1 V pt with
                    | ttt => k None u
                    end |} |}
|}.

Example nat_inf_adjunction_left :
  Opens_preimage nat_inf_point ⊣ nat_inf_right_adjoint
  := nat_inf_preimage_adjunction.
