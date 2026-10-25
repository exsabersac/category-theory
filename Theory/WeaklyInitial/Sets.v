Require Import Category.Lib.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Theory.WeaklyInitial.

Generalizable All Variables.

(**
* The initial-object characterization at Sets

    The witness for Theory/WeaklyInitial.v's biconditional (#435, Mac Lane
    §V.6 Theorem 1): [Sets] is complete (Instance/Sets/Complete.v
    [Sets_Complete]) and has equalizers (Adjunction/GAFT/Sets.v
    [Sets_HasEqualizers]), so [initial_iff_weakly_initial_family_complete]
    applies, and the round trip runs — the initial object
    (Instance/Sets.v [Sets_Initial]) becomes the singleton family
    [Sets_wif], Freyd's product-and-equalizer construction turns that back
    into an initial object [Sets_initial_recovered], and
    Structure/Initial.v's [initial_unique] gives the canonical
    isomorphism [Sets_roundtrip_iso] with the original.  The DERIVED
    singleton family's index and member read back at [eq_refl], through
    the transparent biconditional; nothing about the recovered initial
    object does.

    A separate leaf because of closure: this file's closure is 53 modules
    (Adjunction/GAFT/Sets.v 15 at the margin, the other six `Require`s 0)
    against Theory/WeaklyInitial.v's 29, and Adjunction/GAFT*.v [Require]
    Theory/WeaklyInitial.v, not this satellite, so there is no cycle.  The
    object-carrier universe lands at [Sets@{Set u}] with `Set < u` on every
    head, exactly as Adjunction/GAFT/Sets.v's header discloses for GAFT
    (CORRECTION, #452: that pin was lifted with the one GAFT/Sets.v's
    RECORDED CORRECTION describes; measured, [About Sets_initial_recovered]
    reads [@Initial Sets@{u0 u}] with [u0 < u] and no [Set]);
    the caps `JMeq`, `False_rect` and `projections` arrive with
    [Sets_Complete].  Six `.glob` heads, all `def`, all "Closed under the
    global context", zero `Axioms:` lines, no `Qed`, no `Defined`, none of
    the seven `Require`s droppable, zero name collisions.  NOT delivered:
    a witness at any other category ([FinSet] would need a [Complete
    FinSet] that does not exist); any [eq_refl] reading of the round trip
    beyond the family's index and member (the recovered initial object is
    Freyd's equalizer of endomorphisms, compared with the original only
    through [initial_unique]'s [≅]).

--------
* 集合中的初始对象刻画

Theory/WeaklyInitial.v 的双条件陈述的证人 (#435, Mac Lane §V.6 定理 1)：[Sets] 是完备的 (Instance/Sets/Complete.v [Sets_Complete]) 并且有等化器 (Adjunction/GAFT/Sets.v [Sets_HasEqualizers])，因此 [initial_iff_weakly_initial_family_complete] 适用，并且往返转换可以运行——初始对象 (Instance/Sets.v [Sets_Initial]) 变为单元素族 [Sets_wif]，Freyd 的积与等化器构造将其变回初始对象 [Sets_initial_recovered]，而 Structure/Initial.v 的 [initial_unique] 提供了与原对象的典范同构 [Sets_roundtrip_iso]。在 [eq_refl] 通过透明的双条件返回读取派生单例家族的索引和成员；关于恢复的初始对象没有任何信息。

因为封闭而产生的单独叶子：此文件的封闭为 53 个模块（Adjunction/GAFT/Sets.v 15 在边缘，其他六个 `Require` 为 0）相比 Theory/WeaklyInitial.v 的 29，以及 Adjunction/GAFT*.v [Require] Theory/WeaklyInitial.v，而不是这个卫星，因此没有循环。物体承载宇宙降落在 [Sets@{Set u}]，每个人头上都有 `Set < u`，正如 Adjunction/GAFT/Sets.v 的标题对 GAFT 所描述的那样（更正，#452：该销钉与 GAFT/Sets.v 所记录更正中描述的销钉一起被取下；测量后，[About Sets_initial_recovered] 显示为 [@Initial Sets@{u0 u}]，带有 [u0 < u] 且没有 [Set]）；帽子 `JMeq`、`False_rect` 和 `projections` 搭配 [Sets_Complete] 一起到达。六个 `.glob` 头，都为 `def`，都“在全局上下文中关闭”，零个 `Axioms:` 行，没有 `Qed`，没有 `Defined`，七个 `Require` 中没有可丢弃的，零名称冲突。未交付：
    在任何其他范畴的证人（[FinSet] 需要一个不存在的 [Complete FinSet]）；对家族索引和成员之外的往返读取的任何 [eq_refl]（恢复的初始对象是 Freyd 的自同态等化器，仅通过 [initial_unique] 的 [≅] 与原始对象进行比较）。
*)

Definition Sets_initial_characterization :
  @Initial Sets ↔ WeaklyInitialFamily Sets :=
  initial_iff_weakly_initial_family_complete Sets_Complete Sets_HasEqualizers.

(*
The round trip: the initial object, as a singleton family, through
   Freyd's construction, back to an initial object.

--------
往返旅行：初始对象，作为单例族，通过弗雷德的构造，回到初始对象。
*)
Definition Sets_wif : WeaklyInitialFamily Sets :=
  fst Sets_initial_characterization Sets_Initial.

Definition Sets_initial_recovered : @Initial Sets :=
  snd Sets_initial_characterization Sets_wif.

Definition Sets_roundtrip_iso :
  @initial_obj Sets Sets_initial_recovered ≅ @initial_obj Sets Sets_Initial :=
  initial_unique Sets_initial_recovered Sets_Initial.

(* The family is the singleton at the empty set, on the nose. / 这个族是空集上的单元素集，正好如此。 *)
Example Sets_wif_index : wif_index Sets_wif = poly_unit := eq_refl.

Example Sets_wif_obj (u : poly_unit) :
  wif_obj Sets_wif u = @initial_obj Sets Sets_Initial := eq_refl.
