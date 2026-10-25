Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.DoubleCategory.

Generalizable All Variables.

(** * Companions and conjoints in a double category / * 双范畴中的伴随与伴元 *)

(*
nLab: https://ncatlab.org/nlab/show/companion+pair

   In a double category, a COMPANION of a vertical morphism [u : a ~> b] is a
   horizontal 1-cell [comp_hor : dhor a b] together with two binding squares

        a ==1a=> a                a --û--> b
        |        |                |        |
        id   η   u    and         u    ε   id
        v        v                v        v
        a --û--> b                b ==1b=> b

   (the unit [η] and counit [ε]) subject to two zigzag identities: pasting
   [η] beside [ε] horizontally is the composite of the unitors of [û]
   ([comp_zig] below), and pasting [η] above [ε] vertically is the horizontal
   identity square on [u].  The class [DoubleCategory] deliberately has no
   primitive producing a horizontal identity square on a general vertical
   morphism (only [dsq_vid], whose vertical edges are identities), so the
   vertical zigzag is not expressible in its textbook form here.  We state it
   instead in its standard equivalent REPRESENTABILITY form: the pair
   [(η, ε)] induces a transposition bijection between squares

        a --h'-> b                 a --h'-> b
        |        |                 |        |
        u        id      and       id       id
        v        v                 v        v
        b ==1b=> b                 a --û--> b

   ([companion_eval] one way, [companion_name] the other), and the two
   binding identities [comp_zag_eval]/[comp_zag_name] say the round trips
   are the identity.  In any double category with horizontal identity
   squares and natural unitors this is equivalent to the vertical zigzag;
   here it is exactly the strength needed to make companions unique up to a
   canonical invertible globular square ([companion_unique] below).

   Strength note: the record captures the POINTWISE-bijection form of the
   zigzag — the two round trips only, with no naturality of the
   transposition in [h'] — which is precisely what the uniqueness theorems
   below consume.  The equivalence with the textbook vertical zigzag quoted
   above holds against the richer signature (horizontal identity squares on
   verticals, natural unitors) that [DoubleCategory] deliberately does not
   require (see the SCOPE note in Theory/DoubleCategory.v), so it is stated
   for orientation, not re-proven here.

   A CONJOINT of [u] is the horizontal-opposite notion: a 1-cell
   [conj_hor : dhor b a] with binding squares mirrored left-to-right, and
   the transposition stated for squares whose RIGHT edge is [u].

--------
nLab：https://ncatlab.org/nlab/show/companion+pair

在一个双范畴中，一个垂直态射 [u : a ~> b] 的伴随 (COMPANION) 是一个水平 1-范畴 [comp_hor : dhor a b] 以及两个绑定方格

a ==1a=> a                a --û--> b
        |        |                |        |
        id   η   u    和         u    ε   id
        v        v                v        v
        a --û--> b                b ==1b=> b

(单位 [η] 和余单位 [ε]) 遵循两个折线恒等式：水平拼接 [η] 和 [ε] 是 [û] 的幺元的复合（[comp_zig] 在下方），而垂直拼接 [η] 在 [ε] 之上是 [u] 的水平恒等方格。类 [DoubleCategory] 故意没有生成一般垂直态射上的水平恒等方格的原始元素（仅 [dsq_vid]，其垂直边是恒等），因此这里无法用教科书形式表示垂直折线。我们改为用其标准等价的 REPRESENTABILITY 形式陈述：一对 [(η, ε)] 诱导方格之间的易位双射。

a --h'-> b                 a --h'-> b
        |        |                 |        |
        u        id      和       id       id
        v        v                 v        v
        b ==1b=> b                 a --û--> b

([companion_eval] 一个方向，[companion_name] 另一个方向)，而两个结合恒等式 [comp_zag_eval]/[comp_zag_name] 表示来回操作是恒等。在任何具有水平恒等方格和自然同构的双重范畴中，这等价于垂直之锯齿形；在这里，它正是使伴随唯一化至一个规范可逆球面方格（见下文 [companion_unique]）所需的强度。

强度说明：记录捕捉了之字形的逐点双射形式——只有两个往返，而没有 [h'] 中换位的自然性——这正是下面的唯一性定理所使用的内容。与上面引用的教科书垂直之字形的等价性在更丰富的签名下成立（垂直线上的水平恒等平方，自然单位子），而 [DoubleCategory] 故意不要求这些（参见 Theory/DoubleCategory.v 中的 SCOPE 说明），所以这里是为指导而陈述，并未重新证明。

[u] 的一个共轭是水平相对的概念：一个 1-单元 [conj_hor : dhor b a]，其绑定方块左右镜像，并且对右边缘为 [u] 的方块进行换位。
*)

(* A composite-of-identities collapse used in the transposes' boundaries. / 在易位者的边界中使用的复合恒等坍塌。 *)
Lemma triple_id {C : Category} {x : C} : id[x] ∘ (id ∘ id) ≈ id.
Proof. cat. Qed.

(**
** Boundary coercion versus vertical pasting

    The uniqueness argument must slide a boundary coercion out of one factor
    of a vertical composite.  [DoubleCategory] states its laws with
    [dsq_coerce] outermost only, and — exactly as documented for
    [dtransport_comp_l]/[dtransport_comp_r] in Theory/Displayed.v, whose
    pattern [dsq_coerce] re-applies — the interchange of coercion with
    composition is not derivable from those laws (a 2-cocycle twist model
    separates them).  We therefore package the two missing interchange laws
    as a mixin, quantified over ANY proof of the composite boundary
    relation so no proof-term surgery is ever needed at use sites.  Both
    in-tree models satisfy them: in Sq squares are propositions, and in
    Cospan/Double [dsq_coerce] leaves the apex map untouched.  Only the
    coercion-vs-VERTICAL-composition laws are packaged, because they are
    all the uniqueness proofs below need; the horizontal analogues
    (sliding [dsq_coerce] through [dsq_hcomp]) would join this mixin when
    a consumer arrives, and hold in both models for the same reasons.

--------
** 边界强制与垂直粘贴

唯一性论证必须将边界强制从一个因素中剔除
 的垂直复合体。 [DoubleCategory] 规定了其法律
 [dsq_coerce] 仅最外层，并且 — 与记录的完全一致
 Theory/Displayed.v 中的 [dtransport_comp_l]/[dtransport_comp_r]，其
 模式 [dsq_coerce] 重新应用 — 强制与
 组成不能从这些定律推导出来（2-cocycle 扭曲模型
 将它们分开）。 因此，我们将两个缺失的交换法则打包在一起
 作为混合，通过复合边界的任何证明进行量化
 关系，因此在使用现场不需要进行长期手术。 两者都
 树内模型满足它们：Sq 方格中是命题，而
 Cospan/Double [dsq_coerce] 保持顶点图不变。 只有
 强制与垂直组合法则被打包，因为它们是
 下面需要的所有唯一性证明； 水平类比
 （通过 [dsq_hcomp] 滑动 [dsq_coerce]）将在以下情况下加入此 mixin：
 消费者到达后，出于同样的原因持有这两种型号。
*)

Class DoubleCoerceComp (D : DoubleCategory) : Type := {
  dsq_coerce_vcomp_l {a0 b0 a1 b1 a2 b2 : dcat}
    {h : dhor a0 b0} {u u' : a0 ~> a1} {v v' : b0 ~> b1} {k : dhor a1 b1}
    {w : a1 ~> a2} {x : b1 ~> b2} {l : dhor a2 b2}
    (eu : u ≈ u') (ev : v ≈ v')
    (E1 : w ∘ u ≈ w ∘ u') (E2 : x ∘ v ≈ x ∘ v')
    (s : dsq h u v k) (t : dsq k w x l) :
    dsq_vcomp (dsq_coerce eu ev s) t ≈ dsq_coerce E1 E2 (dsq_vcomp s t);

  dsq_coerce_vcomp_r {a0 b0 a1 b1 a2 b2 : dcat}
    {h : dhor a0 b0} {u : a0 ~> a1} {v : b0 ~> b1} {k : dhor a1 b1}
    {w w' : a1 ~> a2} {x x' : b1 ~> b2} {l : dhor a2 b2}
    (ew : w ≈ w') (ex : x ≈ x')
    (E1 : w ∘ u ≈ w' ∘ u) (E2 : x ∘ v ≈ x' ∘ v)
    (s : dsq h u v k) (t : dsq k w x l) :
    dsq_vcomp s (dsq_coerce ew ex t) ≈ dsq_coerce E1 E2 (dsq_vcomp s t)
}.

Section Companion.

Context {D : DoubleCategory}.

(** ** The companion transposes / ** 伴侣换位 *)

Section CompanionTranspose.

Context {a b : dcat} (u : a ~> b) (h : dhor a b).

(*
Transpose a square with left edge [u] into a globular square into [h]:
   paste the unit on its left and normalise by the unitors.

--------
将左边缘为 [u] 的方形转置为 [h] 中的球状方形：将单位粘贴到其左侧，并通过单位元进行归一化。
*)
Definition companion_name (eta : dsq (dhid a) id u h)
  {h' : dhor a b} (e : dsq h' u id (dhid b)) : dsq h' id id h :=
  dsq_coerce triple_id triple_id
    (dsq_vcomp
       (dsq_vcomp (dunit_right_from h') (dsq_hcomp eta e))
       (dunit_left_to h)).

(*
Transpose a globular square into [h] back into a square with left edge
   [u]: paste the counit underneath.

--------
将球形方块转置为 [h]，然后再转回带左边缘的方块
   [u]：在下面粘贴余单位。
*)
Definition companion_eval (eps : dsq h u id (dhid b))
  {h' : dhor a b} (g : dsq h' id id h) : dsq h' u id (dhid b) :=
  dsq_coerce (id_right u) (id_left id) (dsq_vcomp g eps).

Lemma companion_name_proper (eta : dsq (dhid a) id u h)
  {h' : dhor a b} (e e' : dsq h' u id (dhid b)) :
  e ≈ e' → companion_name eta e ≈ companion_name eta e'.
Proof.
  intros He; unfold companion_name.
  now rewrite He.
Qed.

Lemma companion_eval_proper (eps : dsq h u id (dhid b))
  {h' : dhor a b} (g g' : dsq h' id id h) :
  g ≈ g' → companion_eval eps g ≈ companion_eval eps g'.
Proof.
  intros Hg; unfold companion_eval.
  now rewrite Hg.
Qed.

End CompanionTranspose.

(** ** Companions / ** 同伴 *)

Record Companion {a b : dcat} (u : a ~> b) : Type := {
  comp_hor : dhor a b;

  (* The binding squares. / 绑定方块。 *)
  comp_unit : dsq (dhid a) id u comp_hor;
  comp_counit : dsq comp_hor u id (dhid b);

  (*
Horizontal zigzag: [η] beside [ε] is the composite of the unitors of
     the companion 1-cell (pasted side coerced onto plain side).

--------
水平之字形：[η] 旁边的 [ε] 是伴随 1-胞（将粘贴面强制连接到平面）单元器的复合体。
*)
  comp_zig :
    dsq_coerce (id_left id) (id_left id)
      (dsq_vcomp (dunit_right_to comp_hor) (dunit_left_from comp_hor))
    ≈ dsq_hcomp comp_unit comp_counit;

  (*
Vertical zigzag, in representability form: the two transposes are
     mutually inverse.

--------
垂直之之字形，在可表示性形式中：这两个转置是相互逆的。
*)
  comp_zag_eval : ∀ (h' : dhor a b) (e : dsq h' u id (dhid b)),
    companion_eval u comp_hor comp_counit
      (companion_name u comp_hor comp_unit e) ≈ e;

  comp_zag_name : ∀ (h' : dhor a b) (g : dsq h' id id comp_hor),
    companion_name u comp_hor comp_unit
      (companion_eval u comp_hor comp_counit g) ≈ g
}.

End Companion.

Arguments comp_hor {D a b u} _.
Arguments comp_unit {D a b u} _.
Arguments comp_counit {D a b u} _.
Arguments comp_zig {D a b u} _.
Arguments comp_zag_eval {D a b u} _ _ _.
Arguments comp_zag_name {D a b u} _ _ _.

(** ** Uniqueness of companions / ** 伴侣的独特性 *)

Section CompanionUnique.

Context {D : DoubleCategory}.
Context {CC : DoubleCoerceComp D}.
Context {a b : dcat} {u : a ~> b}.

(* The canonical comparison: transpose [P]'s counit through [Q]. / 典型比较：通过 [Q] 转置 [P] 的余单位。 *)
Definition companion_compare (P Q : Companion u) :
  dsq (comp_hor P) id id (comp_hor Q) :=
  companion_name u (comp_hor Q) (comp_unit Q) (comp_counit P).

(*
The round trip [P → Q → P] is the vertical identity square.  Proof:
   both sides are fixed by the transposition bijection of [P], and under
   [companion_eval P] the composite evaluates — one binding identity per
   companion — back to [P]'s counit, which is also the evaluation of the
   identity square.

--------
往返 [P → Q → P] 是垂直恒等方阵。证明：
   两边都被 [P] 的换位双射固定，并且在 [companion_eval P] 下，复合映射求值——每个伴随关联一个恒等映射——回到 [P] 的余单位，这也是恒等方阵的求值。
*)
Lemma companion_compare_zigzag (P Q : Companion u) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (companion_compare P Q) (companion_compare Q P))
  ≈ dsq_vid (comp_hor P).
Proof using CC D a b u.
  assert (A1 : u ∘ (id ∘ id) ≈ (u ∘ id) ∘ id) by cat.
  assert (A2 : id[b] ∘ (id ∘ id) ≈ (id ∘ id) ∘ id) by cat.
  assert (H1 : (u ∘ id) ∘ id ≈ u) by cat.
  assert (H2 : (id[b] ∘ id) ∘ id ≈ id) by cat.
  assert (E1 : u ∘ (id ∘ id) ≈ u ∘ id) by cat.
  assert (E2 : id[b] ∘ (id ∘ id) ≈ id ∘ id) by cat.
  assert (F1 : u ∘ (id ∘ id) ≈ u) by cat.
  assert (F2 : id[b] ∘ (id ∘ id) ≈ id) by cat.
  assert (B1 : u ∘ id ≈ (u ∘ id) ∘ id) by cat.
  assert (B2 : id[b] ∘ id ≈ (id ∘ id) ∘ id) by cat.
  (* Transfer along the transposition bijection of [P]. / 沿着 [P] 的置换双射进行传递。 *)
  transitivity
    (companion_name u (comp_hor P) (comp_unit P)
       (companion_eval u (comp_hor P) (comp_counit P)
          (dsq_coerce (id_left id) (id_left id)
             (dsq_vcomp (companion_compare P Q) (companion_compare Q P))))).
  { symmetry; apply comp_zag_name. }
  transitivity
    (companion_name u (comp_hor P) (comp_unit P)
       (companion_eval u (comp_hor P) (comp_counit P)
          (dsq_vid (comp_hor P)))).
  2: { apply comp_zag_name. }
  apply companion_name_proper.
  (* The identity square evaluates to the counit. / 单位方块的值等于余单位。 *)
  transitivity (comp_counit P).
  2: {
    symmetry; unfold companion_eval.
    apply dsq_vid_right_any.
  }
  unfold companion_eval.
  (* Slide the boundary coercion of the composite out to the left. / 将复合材料的边界强制向左滑动。 *)
  rewrite (dsq_coerce_vcomp_l (id_left id) (id_left id) E1 E2 _
             (comp_counit P)).
  rewrite (dsq_coerce_trans_any E1 (id_right u) F1 E2 (id_left id) F2).
  (* Reassociate the triple underneath a fresh coercion. / 在新的强制转换下重新关联三元组。 *)
  rewrite <- (dsq_coerce_trans_any A1 H1 F1 A2 H2 F2).
  rewrite (dsq_vassoc_any A1 A2 (companion_compare P Q)
             (companion_compare Q P) (comp_counit P)).
  (* The lower pair is [companion_eval P] of the comparison [Q → P]. / 下方的那一对是比较 [Q → P] 的 [companion_eval P]。 *)
  rewrite (fst (dsq_coerce_flip (id_right u) (id_left id) _ _)
             (comp_zag_eval P _ (comp_counit Q))).
  (* Slide the residual coercion out to the right and collapse. / 将残余的强制滑到右边并折叠。 *)
  rewrite (dsq_coerce_vcomp_r (symmetry (id_right u))
             (symmetry (id_left id)) B1 B2 (companion_compare P Q)
             (comp_counit Q)).
  rewrite (dsq_coerce_trans_any B1 H1 (id_right u) B2 H2 (id_left id)).
  (* What remains is [companion_eval Q] of the comparison [P → Q]. / 剩下的是比较的 [companion_eval Q] [P → Q]。 *)
  apply (comp_zag_eval Q _ (comp_counit P)).
Qed.

(*
Any two companions of [u] are connected by a canonical INVERTIBLE
   globular square, packaged exactly like the coherence isomorphisms of
   [DoubleCategory] (forward square, backward square, two round trips).

--------
[u] 的任意两个伴随体都由一个范式可逆的球状方块连接，打包方式与 [DoubleCategory] 的相干同构完全相同（正向方块、反向方块、两次往返）。
*)
Definition companion_unique (P Q : Companion u) :
  { fwd : dsq (comp_hor P) id id (comp_hor Q) &
  { bwd : dsq (comp_hor Q) id id (comp_hor P) &
    prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
            ≈ dsq_vid (comp_hor P))
         (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
            ≈ dsq_vid (comp_hor Q)) } } :=
  existT _ (companion_compare P Q)
    (existT _ (companion_compare Q P)
       (companion_compare_zigzag P Q, companion_compare_zigzag Q P)).

End CompanionUnique.

(** ** Conjoints / ** 配偶 *)

Section Conjoint.

Context {D : DoubleCategory}.

Section ConjointTranspose.

Context {a b : dcat} (u : a ~> b) (h : dhor b a).

(*
Transpose a square with right edge [u] into a globular square into [h]:
   paste the unit on its right and normalise by the unitors.

--------
将右边缘为 [u] 的方形转置为 [h] 中的球状方形：将单位粘贴到其右侧，并通过单位元进行归一化。
*)
Definition conjoint_name (eta : dsq (dhid a) u id h)
  {h' : dhor b a} (e : dsq h' id u (dhid b)) : dsq h' id id h :=
  dsq_coerce triple_id triple_id
    (dsq_vcomp
       (dsq_vcomp (dunit_left_from h') (dsq_hcomp e eta))
       (dunit_right_to h)).

(*
Transpose a globular square into [h] back into a square with right edge
   [u]: paste the counit underneath.

--------
将球形方块转置为 [h]，然后再转回具有右边缘的方块
   [u]：在下面粘贴余单位。
*)
Definition conjoint_eval (eps : dsq h id u (dhid b))
  {h' : dhor b a} (g : dsq h' id id h) : dsq h' id u (dhid b) :=
  dsq_coerce (id_left id) (id_right u) (dsq_vcomp g eps).

Lemma conjoint_name_proper (eta : dsq (dhid a) u id h)
  {h' : dhor b a} (e e' : dsq h' id u (dhid b)) :
  e ≈ e' → conjoint_name eta e ≈ conjoint_name eta e'.
Proof.
  intros He; unfold conjoint_name.
  now rewrite He.
Qed.

Lemma conjoint_eval_proper (eps : dsq h id u (dhid b))
  {h' : dhor b a} (g g' : dsq h' id id h) :
  g ≈ g' → conjoint_eval eps g ≈ conjoint_eval eps g'.
Proof.
  intros Hg; unfold conjoint_eval.
  now rewrite Hg.
Qed.

End ConjointTranspose.

Record Conjoint {a b : dcat} (u : a ~> b) : Type := {
  conj_hor : dhor b a;

  (* The binding squares (companion squares mirrored left-to-right). / 绑定方格（伴随方格左右镜像）。 *)
  conj_unit : dsq (dhid a) u id conj_hor;
  conj_counit : dsq conj_hor id u (dhid b);

  (*
Horizontal zigzag: [ε] beside [η] is the composite of the unitors of
     the conjoint 1-cell.

--------
水平之字形：[ε] 在 [η] 旁边是共轭 1-单元的联合器的复合。
*)
  conj_zig :
    dsq_coerce (id_left id) (id_left id)
      (dsq_vcomp (dunit_left_to conj_hor) (dunit_right_from conj_hor))
    ≈ dsq_hcomp conj_counit conj_unit;

  (* Vertical zigzag, in representability form. / 垂直之之字形，以可表示性形式。 *)
  conj_zag_eval : ∀ (h' : dhor b a) (e : dsq h' id u (dhid b)),
    conjoint_eval u conj_hor conj_counit
      (conjoint_name u conj_hor conj_unit e) ≈ e;

  conj_zag_name : ∀ (h' : dhor b a) (g : dsq h' id id conj_hor),
    conjoint_name u conj_hor conj_unit
      (conjoint_eval u conj_hor conj_counit g) ≈ g
}.

End Conjoint.

Arguments conj_hor {D a b u} _.
Arguments conj_unit {D a b u} _.
Arguments conj_counit {D a b u} _.
Arguments conj_zig {D a b u} _.
Arguments conj_zag_eval {D a b u} _ _ _.
Arguments conj_zag_name {D a b u} _ _ _.

(** ** Uniqueness of conjoints / ** 共轭点的唯一性 *)

Section ConjointUnique.

Context {D : DoubleCategory}.
Context {CC : DoubleCoerceComp D}.
Context {a b : dcat} {u : a ~> b}.

Definition conjoint_compare (P Q : Conjoint u) :
  dsq (conj_hor P) id id (conj_hor Q) :=
  conjoint_name u (conj_hor Q) (conj_unit Q) (conj_counit P).

Lemma conjoint_compare_zigzag (P Q : Conjoint u) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (conjoint_compare P Q) (conjoint_compare Q P))
  ≈ dsq_vid (conj_hor P).
Proof using CC D a b u.
  assert (A1 : id[b] ∘ (id ∘ id) ≈ (id ∘ id) ∘ id) by cat.
  assert (A2 : u ∘ (id ∘ id) ≈ (u ∘ id) ∘ id) by cat.
  assert (H1 : (id[b] ∘ id) ∘ id ≈ id) by cat.
  assert (H2 : (u ∘ id) ∘ id ≈ u) by cat.
  assert (E1 : id[b] ∘ (id ∘ id) ≈ id ∘ id) by cat.
  assert (E2 : u ∘ (id ∘ id) ≈ u ∘ id) by cat.
  assert (F1 : id[b] ∘ (id ∘ id) ≈ id) by cat.
  assert (F2 : u ∘ (id ∘ id) ≈ u) by cat.
  assert (B1 : id[b] ∘ id ≈ (id ∘ id) ∘ id) by cat.
  assert (B2 : u ∘ id ≈ (u ∘ id) ∘ id) by cat.
  (* Transfer along the transposition bijection of [P]. / 沿着 [P] 的置换双射进行传递。 *)
  transitivity
    (conjoint_name u (conj_hor P) (conj_unit P)
       (conjoint_eval u (conj_hor P) (conj_counit P)
          (dsq_coerce (id_left id) (id_left id)
             (dsq_vcomp (conjoint_compare P Q) (conjoint_compare Q P))))).
  { symmetry; apply conj_zag_name. }
  transitivity
    (conjoint_name u (conj_hor P) (conj_unit P)
       (conjoint_eval u (conj_hor P) (conj_counit P)
          (dsq_vid (conj_hor P)))).
  2: { apply conj_zag_name. }
  apply conjoint_name_proper.
  (* The identity square evaluates to the counit. / 单位方块的值等于余单位。 *)
  transitivity (conj_counit P).
  2: {
    symmetry; unfold conjoint_eval.
    apply dsq_vid_right_any.
  }
  unfold conjoint_eval.
  (* Slide the boundary coercion of the composite out to the left. / 将复合材料的边界强制向左滑动。 *)
  rewrite (dsq_coerce_vcomp_l (id_left id) (id_left id) E1 E2 _
             (conj_counit P)).
  rewrite (dsq_coerce_trans_any E1 (id_left id) F1 E2 (id_right u) F2).
  (* Reassociate the triple underneath a fresh coercion. / 在新的强制转换下重新关联三元组。 *)
  rewrite <- (dsq_coerce_trans_any A1 H1 F1 A2 H2 F2).
  rewrite (dsq_vassoc_any A1 A2 (conjoint_compare P Q)
             (conjoint_compare Q P) (conj_counit P)).
  (* The lower pair is [conjoint_eval P] of the comparison [Q → P]. / 下方的配对是比较 [Q → P] 的 [conjoint_eval P]。 *)
  rewrite (fst (dsq_coerce_flip (id_left id) (id_right u) _ _)
             (conj_zag_eval P _ (conj_counit Q))).
  (* Slide the residual coercion out to the right and collapse. / 将残余的强制滑到右边并折叠。 *)
  rewrite (dsq_coerce_vcomp_r (symmetry (id_left id))
             (symmetry (id_right u)) B1 B2 (conjoint_compare P Q)
             (conj_counit Q)).
  rewrite (dsq_coerce_trans_any B1 H1 (id_left id) B2 H2 (id_right u)).
  (* What remains is [conjoint_eval Q] of the comparison [P → Q]. / 剩下的是比较的 [conjoint_eval Q] [P → Q]。 *)
  apply (conj_zag_eval Q _ (conj_counit P)).
Qed.

(*
Any two conjoints of [u] are connected by a canonical INVERTIBLE
   globular square.

--------
[u] 的任意两个伴随元通过一个典型的可逆球形交换方相连接。
*)
Definition conjoint_unique (P Q : Conjoint u) :
  { fwd : dsq (conj_hor P) id id (conj_hor Q) &
  { bwd : dsq (conj_hor Q) id id (conj_hor P) &
    prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
            ≈ dsq_vid (conj_hor P))
         (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
            ≈ dsq_vid (conj_hor Q)) } } :=
  existT _ (conjoint_compare P Q)
    (existT _ (conjoint_compare Q P)
       (conjoint_compare_zigzag P Q, conjoint_compare_zigzag Q P)).

End ConjointUnique.
