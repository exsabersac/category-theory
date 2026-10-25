Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Span.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Structure.UniversalProperty.Limit.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   * * Essential uniqueness of limits: reconciliations

   Structure/Limit/Unique.v proves Riehl's Proposition 3.1.7 from the
   mediator calculus.  This satellite ties the three pre-existing
   routes to it, so they stop being unrelated developments:

   - [equalizer_unique] (Structure/Equalizer/Fork.v) and
   [pullback_unique] (Structure/Pullback.v) are the hand-rolled
   shape-specific results, each concluding a bare ≅ from its own
   universal property.  Through the in-tree bridges
   ([is_equalizer_limit], [Pullback_from_Universal]) both are shown
   to AGREE with [limit_unique_iso]: the isomorphisms have the same
   forward component ([equalizer_unique_agrees],
   [pullback_unique_agrees]).  Their terminating [Qed]s become
   [Defined]s for exactly this purpose — the statements say nothing
   about the components, so agreement is expressible only against
   the transparent terms; no proof text changed.  In particular the
   general theorem strictly subsumes both: it adds the
   leg-commutation equations and the uniqueness clause the bare ≅
   lacked.

   - [univ_property_unique_up_to_unique_iso]
   (Structure/UniversalProperty.v) is the generic representability
   route, in tree instantiated only at terminal and initial objects
   (Structure/UniversalProperty/Terminal.v) and never at limits —
   the gap issue #950 records.  [limit_unique_up_to_transport_iso]
   takes it at [LimitIsUniversalProperty]: two limit witnesses of one diagram
   are related by an isomorphism (in C^op) UNIQUE among those
   transporting one witness's representation to the other's.  The
   identification of that transport with precomposition of the limit
   legs — which would let the generic isomorphism be compared
   componentwise with [limit_unique_iso] — is NOT proved here: the
   generic route's representation equivalence is assembled by hint
   automation, and no in-tree lemma characterises its action on leg
   families (the gap issue #950 itself documents).  What this file
   contributes is the instantiation, so the generic statement is
   finally available at limits at all; the componentwise comparison
   remains open alongside that characterisation. 

   --------
   * * 极限的基本唯一性：调和

   Structure/Limit/Unique.v 证明了 Riehl 在中介计算中提出的命题 3.1.7。
   这个附属内容将其三个已有的路线联系起来，因此它们不再是无关的发展：-  [equalizer_unique]（Structure/Equalizer/Fork.v）和 [pullback_unique]（Structure/Pullback.v）是手工编写的特定形状结果，每个结果都通过其自身的泛性质得出一个裸 ≅。通过树内桥梁（[is_equalizer_limit]、[Pullback_from_Universal]），两者都被证明与 [limit_unique_iso] 一致：同构具有相同的前向分量（[equalizer_unique_agrees]、[pullback_unique_agrees]）。它们的终止 [Qed] 变成了 [Defined]，正是为了这个目的——这些陈述没有涉及分量，因此一致性只能针对透明项表达；证明文本未发生变化。特别是，一般定理严格包含两者：它增加了腿交换方程和裸 ≅ 所缺少的唯一性条款。-  [univ_property_unique_up_to_unique_iso] (Structure/UniversalProperty.v) 是通用可表示性的方法，在树中仅在终端对象和初始对象上实例化 (Structure/UniversalProperty/Terminal.v)，从不在极限对象上实例化——这是间隙问题 #950 所记录的。[limit_unique_up_to_transport_iso] 在 [LimitIsUniversalProperty] 处理了此问题：同一图表的两个极限证据通过一个同构 (在 C^op 中) 相关联，该同构在将一个证据的表示传递到另一个证据时是唯一的。将该输运与极限的前复合相识别——这将使得可以对通用同构进行按分量比较 [limit_unique_iso]——在这里并未证明：通用路径的表示等价是通过提示自动化组装的，并且没有树内引理来描述它对分支族的作用（#950 问题本身已记录此差距）。这个文件的贡献是实例化，因此通用命题最终在极限处可用；而按分量的比较仍然与该表征问题一起未解决。
*)

(* * ** Equalizers: the elementary uniqueness agrees / * ** 均衡器：基本的独特性一致 *)

Section EqualizerAgrees.

Context {C : Category}.
Context {x y : C}.
Context (f g : x ~{C}~> y).

(*
 An elementary equalizer, read as a limit witness pinned at its own
 apex, through Fork.v's bridge. 

 --------
 一个初级均衡器，被读作作为自身顶点上的极限见证，通过 Fork.v 的桥。
*)
Definition is_equalizer_alimit {q : C} {e : q ~> x}
  (E : IsEqualizer f g q e) : IsALimit (APair f g) q :=
  limit_is_alimit (is_equalizer_limit f g E).

(*
 The two forward components coincide, and with them the whole
 isomorphisms ([equalizer_unique_agrees_iso], one line through
 [to_equiv_implies_iso_equiv]).  The general result adds what the
 bare ≅ could not say: the legs and the uniqueness clause of
 [limit_unique_iso_unique]. 

 --------
 两个前向分量重合，并且整个同构（[equalizer_unique_agrees_iso]，一条通过[to_equiv_implies_iso_equiv]的直线）也随之重合。一般结果补充了单纯≅无法说明的内容：[limit_unique_iso_unique]的分支和唯一性条款。
*)
Theorem equalizer_unique_agrees {q1 q2 : C} {e1 : q1 ~> x} {e2 : q2 ~> x}
  (E1 : IsEqualizer f g q1 e1) (E2 : IsEqualizer f g q2 e2) :
  to (equalizer_unique f g E1 E2)
    ≈ to (limit_unique_iso (is_equalizer_alimit E1)
                           (is_equalizer_alimit E2)).
Proof.
  apply limit_unique_iso_unique; intro p; destruct p; simpl.
  - exact (unique_property (eq_desc E2 e1 (fork_eq E1))).
  - transitivity (f ∘ (e2 ∘ unique_obj (eq_desc E2 e1 (fork_eq E1)))).
    { symmetry; apply comp_assoc. }
    now rewrite (unique_property (eq_desc E2 e1 (fork_eq E1))).
Qed.

(* ...and therefore the isomorphisms agree outright. / ...因此同构完全一致。 *)
Theorem equalizer_unique_agrees_iso {q1 q2 : C} {e1 : q1 ~> x}
  {e2 : q2 ~> x}
  (E1 : IsEqualizer f g q1 e1) (E2 : IsEqualizer f g q2 e2) :
  equalizer_unique f g E1 E2
    ≈ limit_unique_iso (is_equalizer_alimit E1) (is_equalizer_alimit E2).
Proof.
  apply to_equiv_implies_iso_equiv, equalizer_unique_agrees.
Qed.

End EqualizerAgrees.

(* * ** Pullbacks: the elementary uniqueness agrees / * ** 回调：基本唯一性一致 *)

Section PullbackAgrees.

Context {C : Category}.
Context {x y z : C}.
Context (f : x ~{C}~> z) (g : y ~{C}~> z).

(*
 A pullback square, read as a limit witness pinned at its own apex,
 through Pullback/Limit.v's bridge. 

 --------
 一个拉回方块，被理解为固定在自身顶点的极限见证，通过 Pullback/Limit.v 的桥接。
*)
Definition pullback_alimit (P : Pullback f g) :
  IsALimit ((@ASpan (C^op) _ _ _ f g)^op) (Pull f g P) :=
  limit_is_alimit (Pullback_from_Universal f g P).

Theorem pullback_unique_agrees (P Q : Pullback f g) :
  to (pullback_unique P Q)
    ≈ to (limit_unique_iso (pullback_alimit P) (pullback_alimit Q)).
Proof.
  assert (T : to (pullback_unique P Q)
                ≈ unique_obj (ump_pullbacks f g Q (Pull f g P)
                     (pullback_fst f g P) (pullback_snd f g P)
                     (pullback_commutes f g P))).
  { unfold pullback_unique; simpl.
    destruct (unique_property
      (ump_pullbacks f g Q (Pull f g P) (pullback_fst f g P)
         (pullback_snd f g P) (pullback_commutes f g P))).
    destruct (unique_property
      (ump_pullbacks f g P (Pull f g Q) (pullback_fst f g Q)
         (pullback_snd f g Q) (pullback_commutes f g Q))).
    reflexivity. }
  rewrite T.
  destruct (unique_property
    (ump_pullbacks f g Q (Pull f g P) (pullback_fst f g P)
       (pullback_snd f g P) (pullback_commutes f g P))) as [HQfst HQsnd].
  apply limit_unique_iso_unique; intro r; destruct r.
  - exact HQfst.
  - transitivity
      (f ∘ (pullback_fst f g Q
              ∘ unique_obj (ump_pullbacks f g Q (Pull f g P)
                   (pullback_fst f g P) (pullback_snd f g P)
                   (pullback_commutes f g P)))).
    { symmetry; apply comp_assoc. }
    now rewrite HQfst.
  - exact HQsnd.
Qed.

Theorem pullback_unique_agrees_iso (P Q : Pullback f g) :
  pullback_unique P Q
    ≈ limit_unique_iso (pullback_alimit P) (pullback_alimit Q).
Proof.
  apply to_equiv_implies_iso_equiv, pullback_unique_agrees.
Qed.

End PullbackAgrees.

(* * ** The generic representability route, finally instantiated / * ** 泛型可表示性路线，最终实例化 *)

Section TransportUnique.

Context {J : Category}.
Context {C : Category}.
Context (F : J ⟶ C).

(*
 The composite never before formed at limits:
 [univ_property_unique_up_to_unique_iso] at
 [LimitIsUniversalProperty].  Two limit witnesses of one diagram
 are related by an isomorphism (of C^op, the representability side's
 home) unique among those transporting the one representation to the
 other. 

 --------
 在极限处从未形成的复合体：
 [univ_property_unique_up_to_unique_iso] 在
 [LimitIsUniversalProperty] 。同一图的两个极限证人通过一个同构（C^op，即表示可表示性一侧的空间）相关联，该同构在将一个表示传送到另一个表示的同构中是唯一的。
*)
Definition limit_unique_up_to_transport_iso
  (c d : C) (Hc : IsALimit F c) (Hd : IsALimit F d) :
  @Unique (@Isomorphism C^op c d) _
    (fun p =>
       @univ_property_respects_iso C^op (fun v => IsALimit F v)
         (fun v => @LimitSetoid J C F v)
         (LimitIsUniversalProperty J C F) c d p Hc ≈ Hd) :=
  @univ_property_unique_up_to_unique_iso C^op
    (fun v => IsALimit F v)
    (fun v => @LimitSetoid J C F v)
    (LimitIsUniversalProperty J C F) c d Hc Hd.

End TransportUnique.
