Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(* * * A category read at higher universe levels / * * 在更高宇宙层次阅读的类别 *)

(*
 nLab: https://ncatlab.org/nlab/show/universe+enlargement (the general
 notion, a category of one universe re-read in a larger one; this file
 is its trivial case, the same category with nothing improved)

 WHY IT IS NEEDED.  [Category@{o h p}] is a record, and the tree's
 records are not cumulative (Instance/Sets/Classifier.v's
 [Setoid_Lift] says so of setoid objects and rebuilds them;
 Structure/Pullback/Wide/Complete.v says so of the category record): a
 [C : Category@{co ch ch}] is not itself a [Category@{xo xh xh}] when
 co < xo or ch < xh, although its objects, arrows and ≈ re-typecheck at
 the higher levels.  A statement that quantifies over every category at
 the levels (xo, xh), such as Structure/Coequalizer/Absolute.v's
 [AbsoluteCoequalizer] and Structure/Limit/Absolute.v's
 [AbsoluteLimitCone], therefore cannot be applied to C itself, nor to a
 category below (xo, xh); it can be applied to the rebuild, and that is
 what makes those predicates downward closed (#477).

 WHAT IS HERE.
 - [LiftCat C]: C rebuilt as a [Category@{xo xh xh}], with C's
 objects, arrows, ≈, identities and composites, and every law C's
 own.  The [Equivalence] and [Proper] fields are repacked, those
 records not being cumulative either.
 - [Lift_in C : C ⟶ LiftCat C], the identity on objects and on
 arrows on the nose ([Lift_in_fobj], [Lift_in_fmap], at [eq_refl]).
 - [Lift_after T : C ⟶ LiftCat X] for [T : C ⟶ X]: T read into the
 rebuild of X, with T's actions on the nose ([Lift_after_fobj],
 [Lift_after_fmap], at [eq_refl]).  In every datum it is
 [Lift_in X ◯ T], but Theory/Functor.v's [Compose] gives its three
 categories one hom level, so [Lift_in X ◯ T] cannot be formed when
 the lift's hom level is strictly above X's (refused in
 Test/ProbeAbsolute477.v); [Lift_after] is built directly.

 UNIVERSES, by [About].  [LiftCat@{co ch xo xh}] is over
 [C : Category@{co ch ch}] and returns a [Category@{xo xh xh}] under
 the constraints "co <= xo" and "ch <= xh" and no other, and
 [Lift_in@{co ch xo xh}] and its two readbacks carry the same two.
 [Lift_after@{co ch xo xh yo yh}] lifts [X : Category@{xo xh xh}] to
 [@{yo yh}] under "ch <= xh" (from [T] itself), "ch <= yh",
 "xo <= yo" and "xh <= yh", and its two readbacks the same four.  No
 block carries an equation.  The statements of [Lift_in], [Lift_after]
 and the four readbacks name the instance of the lift they speak of
 (six explicit universe instances of this file's constants): a lifted
 level is bounded below alone, and minimization would otherwise set
 it to the level it lifts.

 NOT DELIVERED.  No functor back from [LiftCat C] to C once the hom
 level is lifted: at "ch < xh" the type [LiftCat C ⟶ C] is itself
 refused ("Cannot enforce ch = …", Test/ProbeAbsolute477.v), since
 [Functor]'s [fmap_respects] is typed through [respectful] at the
 target's levels and so bounds the source's hom level by the
 target's; with the objects lifted alone the way back is formable.
 No lift of the proof level apart from the hom level.  Nothing about
 structure that [LiftCat] preserves or reflects beyond what its
 consumers in Structure/Limit/Absolute.v and Structure/Coequalizer/
 Absolute.v use, which is that its arrows, ≈ and composites are C's. 

 --------
 nLab：https://ncatlab.org/nlab/show/universe+enlargement（一般概念，一个宇宙的范畴在更大的宇宙中重新解读；此文件是其平凡情况，同一个范畴没有任何改进）为什么需要它。[Category@{o h p}] 是一个记录，而树的记录不是累积的（Instance/Sets/Classifier.v 对集合论对象的 [Setoid_Lift] 是这么说的，并且对它们进行了重建；Structure/Pullback/Wide/Complete.v 对类别记录说了同样的话）：当 co < xo 或 ch < xh 时，[C : Category@{co ch ch}] 本身并不是 [Category@{xo xh xh}]，尽管它的对象、箭头和 ≈ 在更高层次上可以重新类型检查。一个对每个层次 (xo, xh) 上的类别进行量化的语句，例如 Structure/Coequalizer/Absolute.v 的 [AbsoluteCoequalizer] 和 Structure/Limit/Absolute.v 的 [AbsoluteLimitCone]，因此不能应用于 C 自身，也不能应用于低于 (xo, xh) 的类别；它可以应用于重建，并且这正是使这些谓词向下封闭的原因 (#477)。这里的内容。
 - [LiftCat C]：C 被重建为 [Category@{xo xh xh}]，包含 C 的对象、箭头、≈、恒等和复合，以及 C 自身的每条定律。[Equivalence] 和 [Proper] 字段被重新打包，这些记录也不是累积的。
 - [Lift_in C : C ⟶ LiftCat C]，对象和箭头上的恒等 ([Lift_in_fobj], [Lift_in_fmap], 位于 [eq_refl])。
 - [Lift_after T : C ⟶ LiftCat X] 对于 [T : C ⟶ X]：T 被读入 X 的重建，T 的操作精确应用 ([Lift_after_fobj], [Lift_after_fmap], 位于 [eq_refl])。在每个数据中，它是 [Lift_in X ◯ T]，但 Theory/Functor.v 的 [Compose] 给它的三个范畴一个同态层，因此当提升的同态层严格高于 X 时无法形成 [Lift_in X ◯ T]（在 Test/ProbeAbsolute477.v 中被拒绝）；[Lift_after] 直接构建。宇宙，由 [About] 创作。[LiftCat@{co ch xo xh}] 位于 [C : Category@{co ch ch}] 之上，并在约束条件“co <= xo”和“ch <= xh”下返回 [Category@{xo xh xh}]，除此之外没有其他约束；[Lift_in@{co ch xo xh}] 及其两个回读具有相同的两者。[Lift_after@{co ch xo xh yo yh}] 在“ch <= xh”（来自 [T] 本身）、“ch <= yh”、“xo <= yo”和“xh <= yh”的约束下，将 [X : Category@{xo xh xh}] 提升到 [@{yo yh}]，并且其两个回读相同四者。没有块包含方程。[Lift_in]、[Lift_after] 及四个回读的语句都指明了它们所谈论的提升的实例（本文件常量的六个显式宇宙实例）：提升的层级单独在下方有界，否则最小化将其设置为它所提升的层级。未交付。从 [LiftCat C] 到 C 没有函子返回，一旦同态层被提升：在 “ch < xh” 时，类型 [LiftCat C ⟶ C] 本身被拒绝（“无法强制 ch = …”，Test/ProbeAbsolute477.v），因为 [Functor] 的 [fmap_respects] 是通过 [respectful] 在目标层级上进行类型化的，因此通过目标层级界定了源的同态层；仅提升对象时，回路是可形成的。除了同态层之外，证明层没有提升。关于 [LiftCat] 保持或反映的结构，没有超出其在 Structure/Limit/Absolute.v 和 Structure/Coequalizer/Absolute.v 中使用的那部分，那部分是它的箭头、≈ 和复合是 C 的。
*)

(*
   【LiftCat 定义展开】/ LiftCat walkthrough
   （口吻对齐 Theory/Category.v；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      Coq 宇宙不累积：Category@{co ch} 不能直接当成更高宇宙的 Category。
      LiftCat C 用同一套对象/箭头/≈/运算，在更高宇宙里「重包」一遍。
      Rebuild C at higher universes; data unchanged.
      不是数学上的新构造，是证明助手工程需要（#477 绝对余极限等）。

   2) 交付 / Deliverables
      LiftCat C : Category@{xo xh}（需 co≤xo, ch≤xh）
      Lift_in : C ⟶ LiftCat C（对象与箭头定义性恒等）
      Lift_after T：把 T : C ⟶ X 读进 LiftCat X

   阅读：宇宙约束 → 同数据重包 → Lift_in 当「恒等嵌入」。
   Read: universe bounds → same data → identity-like Lift_in.
*)

Definition LiftCat@{co ch xo xh +} (C : Category@{co ch ch}) :
  Category@{xo xh xh}.
Proof.
  unshelve refine
    {| obj := @obj C;
       hom := fun x y => @hom C x y;
       homset := fun x y =>
         {| equiv := fun f g => @equiv _ (@homset C x y) f g;
            setoid_equiv := _ |};
       id := fun x => @id C x;
       compose := fun x y z f g => @compose C x y z f g |}.
  - constructor.
    + intro f.
      exact (@Equivalence_Reflexive _ _ (@setoid_equiv _ (@homset C x y)) f).
    + intros f g H.
      exact (@Equivalence_Symmetric _ _ (@setoid_equiv _ (@homset C x y))
               f g H).
    + intros f g h H1 H2.
      exact (@Equivalence_Transitive _ _ (@setoid_equiv _ (@homset C x y))
               f g h H1 H2).
  - intros x y z f f2 Hf g g2 Hg.
    exact (@compose_respects C x y z f f2 Hf g g2 Hg).
  - intros x y f. exact (@id_left C x y f).
  - intros x y f. exact (@id_right C x y f).
  - intros x y z w f g h. exact (@comp_assoc C x y z w f g h).
  - intros x y z w f g h. exact (@comp_assoc_sym C x y z w f g h).
Defined.

Definition Lift_in@{co ch xo xh +} (C : Category@{co ch ch}) :
  C ⟶ LiftCat@{co ch xo xh} C.
Proof.
  unshelve refine (@Build_Functor C (LiftCat C)
    (fun x : C => x) (fun (x y : C) (f : x ~{C}~> y) => f) _ _ _).
  - intros x y f g H. exact H.
  - intros x. simpl. reflexivity.
  - intros x y z f g. simpl. reflexivity.
Defined.

Example Lift_in_fobj@{co ch xo xh +} (C : Category@{co ch ch}) (x : C) :
  fobj[Lift_in@{co ch xo xh} C] x = x := eq_refl.

Example Lift_in_fmap@{co ch xo xh +} (C : Category@{co ch ch}) {x y : C}
  (f : x ~{C}~> y) : fmap[Lift_in@{co ch xo xh} C] f = f := eq_refl.

Definition Lift_after@{co ch xo xh yo yh +}
  {C : Category@{co ch ch}} {X : Category@{xo xh xh}} (T : C ⟶ X) :
  C ⟶ LiftCat@{xo xh yo yh} X.
Proof.
  unshelve refine (@Build_Functor C (LiftCat X)
    (fun x : C => T x) (fun (x y : C) (f : x ~{C}~> y) => fmap[T] f)
    _ _ _).
  - intros x y f g H. exact (@fmap_respects _ _ T x y f g H).
  - intros x. exact (@fmap_id _ _ T x).
  - intros x y z f g. exact (@fmap_comp _ _ T x y z f g).
Defined.

Example Lift_after_fobj@{co ch xo xh yo yh +}
  {C : Category@{co ch ch}} {X : Category@{xo xh xh}} (T : C ⟶ X) (x : C) :
  fobj[Lift_after@{co ch xo xh yo yh} T] x = T x := eq_refl.

Example Lift_after_fmap@{co ch xo xh yo yh +}
  {C : Category@{co ch ch}} {X : Category@{xo xh xh}} (T : C ⟶ X)
  {x y : C} (f : x ~{C}~> y) :
  fmap[Lift_after@{co ch xo xh yo yh} T] f = fmap[T] f := eq_refl.
