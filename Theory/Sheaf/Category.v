Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Sheaf.
Require Import Coq.Vectors.Vector.

Generalizable All Variables.

(**
* The category of sheaves over a site

    nLab: https://ncatlab.org/nlab/show/category+of+sheaves
    Wikipedia: https://en.wikipedia.org/wiki/Sheaf_(mathematics)

    [Sheaves C] is the FULL subcategory of the presheaf category
    [Presheaves C Sets] (= [C^op, Sets]) on the [Sheaf] predicate of
    Theory/Sheaf.v, built with Construction/Subcategory.v exactly as
    Construction/Reflective.v, Construction/Localization.v and
    Theory/Lawvere/Model.v build their full subcategories: [sobj]
    selects the sheaf witnesses and [shom] retains every natural
    transformation ([True]/[I]).

    SCOPE NOTE, stating the weaknesses of the underlying donor
    precisely.  (i) The [Site] encoding in Theory/Sheaf.v picks a
    SINGLE covering family per object rather than the usual collection
    of covering families — less general than a full coverage.  (ii)
    Deeper, found during this phase's review: the inherited [Sheaf]
    predicate is NOT the textbook unique-gluing condition even for
    that one family.  Its gluing clause is per-leg (a single section
    over one [u_i], not a simultaneous matching family), and its
    compatibility antecedent quantifies over ALL sections of the other
    leg — instantiating [v := u_i], [g := h := id] and the SAME leg
    [j := i] makes the antecedent force [x_i ≈ x_j] for every
    [x_j : X u_i], so the hypothesis is satisfiable only when [X u_i]
    is a subsingleton, and the condition is vacuous at any covered
    object with two inequivalent sections.  "Sheaf" throughout this
    file therefore means: EXACTLY Theory/Sheaf.v's predicate, no more.
    Everything below (the category, the fully faithful inclusion,
    closure under isomorphism) is a genuine theorem about that
    predicate and survives a future repair structurally; the repair
    itself — re-founding [Sheaf] on honest matching families — is a
    named deferral alongside sheafification (ledger entry 1).

    Sheafification (the left adjoint to [Sheaves_Incl], exhibiting
    [Sheaves C] as a reflective subcategory of presheaves) is a named
    deferral: LEDGER ENTRY 1.

--------
* 一个拓扑站点上的层的范畴

nLab：https://ncatlab.org/nlab/show/category+of+sheaves
维基百科：https://en.wikipedia.org/wiki/Sheaf_(mathematics)

[Sheaves C] 是预层范畴 [Presheaves C Sets] (= [C^op, Sets]) 在 Theory/Sheaf.v 的 [Sheaf] 命题上的完整子范畴，构建方式与 Construction/Subcategory.v 完全相同，就像 Construction/Reflective.v、Construction/Localization.v 和 Theory/Lawvere/Model.v 构建它们的完整子范畴一样：[sobj] 选择层的见证，[shom] 保留每个自然变换 ([True]/[I])。

范围说明，准确说明底层供体的弱点。(i) Theory/Sheaf.v 中的 [Site] 编码为每个对象选择单个覆盖族，而不是通常的覆盖族集合——比完整覆盖的通用性要低。(ii) 在本阶段审核期间发现的更深入问题：继承的 [Sheaf] 谓词即使对于那一个族，也不是教科书上的唯一粘合条件。
它的粘合子句是每腿一次（在一个 [u_i] 上的单个部分，而不是同时匹配的系列），并且它的兼容前提量化在另一条腿的所有部分——实例化 [v := u_i]、[g := h := id] 和同一条腿 [j := i] 会使前提对每个 [x_j : X u_i] 强制 [x_i ≈ x_j]，因此假设仅在 [X u_i] 是子单集时可满足，并且在任何有两个不等效部分的覆盖对象上该条件都是空的。因此，在本文件中“层”意味着：完全等同 Theory/Sheaf.v 的谓词，仅此而已。
下面的所有内容（范畴、完全忠实的包含、同构下的封闭性）都是关于该谓词的真实定理，并且在未来的结构性修复中仍然成立；修复本身——在诚实匹配族上重新建立 [Sheaf] ——是一种命名的延迟，与层化（账目条目 1）并列。

Sheafification（[Sheaves_Incl] 的左伴随，展示 [Sheaves C] 作为预层的反射子范畴）是一个命名的延迟：账簿条目 1。
*)

(**
Pointwise implication for the Type-valued [ForallT] of
    Theory/Sheaf.v: a function of witnesses at every element maps a
    [ForallT P] witness over a vector to a [ForallT Q] witness over
    the same vector.  Used twice below, once for the outer family of
    gluing statements and once for the inner compatibility family.

--------
类型值 [ForallT] 的逐点蕴涵，来自 Theory/Sheaf.v：在每个元素处的见证函数将一个向量上的 [ForallT P] 见证映射为相同向量上的 [ForallT Q] 见证。下面使用了两次，一次用于外层的粘合语句族，一次用于内层的兼容性语句族。
*)
Lemma ForallT_impl {A : Type} (P Q : A → Type)
  (h : ∀ a : A, P a → Q a) :
  ∀ {n : nat} (v : Vector.t A n), ForallT P v → ForallT Q v.
Proof.
  intros n v HP; induction HP; constructor; auto.
Qed.

Section SheafCategory.

Context (C : Category).
Context `{@Site C}.

(**
The full subcategory data: objects are presheaves equipped with a
    [Sheaf] witness; every natural transformation between two sheaves
    is a morphism of sheaves ([True]), so closure under identity and
    composition is trivial ([I]).

--------
完整的子范畴数据：对象是配备有 [Sheaf] 证明的预层；两个层之间的每一个自然变换都是层的态射（[True]），因此在恒等映射和复合下的封闭性是显而易见的（[I]）。
*)
Definition Sheaves_sub : Subcategory (@Presheaves C Sets) :=
  @Build_Subcategory (@Presheaves C Sets)
    (fun X : Presheaf C Sets => Sheaf X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Sheaves : Category := Sub (@Presheaves C Sets) Sheaves_sub.

(** The inclusion of sheaves into presheaves. / 从层到预层的包含。 *)
Definition Sheaves_Incl : Sheaves ⟶ @Presheaves C Sets :=
  Incl (@Presheaves C Sets) Sheaves_sub.

(**
The subcategory is full by construction, so the inclusion is a
    full functor (via [Full_Implies_Full_Functor]).  Kept [Defined]
    for uniformity, though [Full_Implies_Full_Functor] is itself
    opaque, so the chosen preimage does not compute through this
    route; a transparent inline construction (the preimage is
    literally [(g; I)]) is available should a consumer ever need it
    to compute.

--------
该子范畴在构造上是满的，因此包含是一个满函子（通过 [Full_Implies_Full_Functor]）。为了统一性保留了 [Defined]，尽管 [Full_Implies_Full_Functor] 本身是透明的，因此所选择的原像不会通过此途径计算；如果使用者需要计算，则可以使用一个透明的内联构造（原像就是字面上的 [(g; I)]）。
*)
Lemma Sheaves_Full : Functor.Full Sheaves_Incl.
Proof.
  apply Full_Implies_Full_Functor.
  intros x y ox oy f; exact I.
Defined.

(**
The inclusion is faithful: on hom-sets it is the first projection
    out of a sigma type, and the hom-setoid of [Sub] is equality of
    first projections, so injectivity is immediate.

--------
这一包含是忠实的：在 Hom 集上它是 sigma 类型的第一个投影，而 [Sub] 的 Hom-等价关系是第一个投影的相等性，因此单射性是显而易见的。
*)
Lemma Sheaves_Faithful : Functor.Faithful Sheaves_Incl.
Proof.
  constructor; simpl; intros x y f g Hfg; exact Hfg.
Qed.

(**
** Repleteness: the sheaf condition is closed under isomorphism

    If X ≅ Y in [Presheaves C Sets] and X is a sheaf, then Y is a
    sheaf.  The unique-gluing data is transported componentwise across
    the natural isomorphism: a matching family for Y is pulled back
    along [from iso] to a matching family for X (naturality moves the
    restriction maps across the components), X's unique glued section
    is pushed forward along [to iso], and its uniqueness transfers
    because the components are mutually inverse setoid bijections.
    Kept [Defined] so downstream users can compute with the
    transported gluing data.

--------
** 充足性：层条件在同构下是闭合的

如果 X ≅ Y 在 [Presheaves C Sets] 中，并且 X 是一个层，那么 Y 也是一个层。唯一粘合的数据通过自然同构逐分量地传递：Y 的匹配族沿着 [from iso] 回拉得到 X 的匹配族（自然性使限制映射在各分量之间移动），X 的唯一粘合截面沿 [to iso] 推前，其唯一性得到保持，因为各分量是互为逆集合同构。保留 [Defined]，以便下游用户可以使用传递的粘合数据进行计算。
*)
Theorem sheaf_iso_closed
  (X Y : Presheaf C Sets) (iso : X ≅[@Presheaves C Sets] Y) :
  Sheaf X → Sheaf Y.
Proof.
  intros HX.
  constructor; intro u.
  pose proof (@restriction C _ X HX u) as HR.
  revert HR.
  destruct (coverage u) as [n fam].
  apply ForallT_impl.
  intros [uᵢ fᵢ] Hglue yᵢ Hcompat.
  (*
Pull the matching family for Y back along [from iso], obtaining a
     matching family for X at the pulled-back section.

--------
沿 [from iso] 将 Y 的匹配族拉回，得到 X 在拉回截面上的匹配族。
*)
  assert (HXc : ∀ (v : C) (g : v ~> uᵢ),
            ForallT (A := ∃ uⱼ, uⱼ ~> u)
              (λ '(uⱼ; fⱼ),
                ∀ h : v ~> uⱼ,
                  fᵢ ∘ g ≈ fⱼ ∘ h →
                  ∀ xⱼ : X uⱼ,
                    fmap[X] g (transform[from iso] uᵢ yᵢ) ≈ fmap[X] h xⱼ)
              fam).
  { intros v g.
    generalize (Hcompat v g).
    apply ForallT_impl.
    intros [uⱼ fⱼ] Hj h e xⱼ.
    (*
Naturality of [from iso] at g and at h, plus the iso round
       trip at uⱼ, reduce the X-compatibility square to the given
       Y-compatibility square.

--------
[from iso] 在 g 和 h 下的自然性，加上在 uⱼ 的同构来回，能将 X-兼容方形简化为给定的 Y-兼容方形。
*)
    pose proof (naturality (from iso) uᵢ v g yᵢ) as HA; simpl in HA.
    pose proof (naturality (from iso) uⱼ v h (transform[to iso] uⱼ xⱼ)) as HB;
      simpl in HB.
    pose proof (iso_from_to iso uⱼ xⱼ) as HC; simpl in HC.
    rewrite HA.
    rewrite (Hj h e (transform[to iso] uⱼ xⱼ)).
    rewrite <- HB.
    apply (proper_morphism (fmap[X] h)).
    rewrite HC.
    exact (@fmap_id _ _ X uⱼ xⱼ). }
  destruct (Hglue (transform[from iso] uᵢ yᵢ) HXc) as [x Hx Hun].
  unshelve econstructor.
  - (* the glued section for Y: push X's glued section forward / Y 的粘合部分：将 X 的粘合部分向前推进 *)
    exact (transform[to iso] u x).
  - (* it restricts correctly, by naturality of [to iso] / 它通过 [to iso] 的自然性正确地限制 *)
    pose proof (naturality (to iso) u uᵢ fᵢ x) as HN; simpl in HN.
    pose proof (iso_to_from iso uᵢ yᵢ) as HD; simpl in HD.
    rewrite HN, Hx, HD.
    exact (@fmap_id _ _ Y uᵢ yᵢ).
  - (*
uniqueness: any other glued section for Y pulls back to a glued
       section for X, so it agrees with x, hence with [to iso u x]

--------
唯一性：Y 的任何其他粘合部分都会回溯到 X 的粘合部分，因此它与 x 一致，因此与 [to iso u x] 一致
*)
    intros y' Hy'; simpl in Hy'.
    pose proof (naturality (from iso) u uᵢ fᵢ y') as HN; simpl in HN.
    assert (Hx' : x ≈ transform[from iso] u y'). {
      apply Hun.
      rewrite HN.
      now rewrite Hy'.
    }
    pose proof (iso_to_from iso u y') as HD; simpl in HD.
    rewrite Hx', HD.
    exact (@fmap_id _ _ Y u y').
Defined.

End SheafCategory.
