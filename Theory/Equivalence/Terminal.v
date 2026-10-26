Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Construction.Subcategory.Terminal.

Generalizable All Variables.

(*
Riehl, CTiC, Exercise 1.6.ii(ii): terminal objects transport along an
   equivalence.  Uniqueness first, since it carries the content.

   Given two arrows d ~> F 1, push them through the quasi-inverse G.  The
   unit component 1 ≅ G (F 1) is invertible, so composing with its
   [from] leg lands both images in G d ~> 1, where [one_unique] identifies
   them; cancelling the monic [from] leg gives fmap[G] f ≈ fmap[G] g, and
   G is faithful ([Equivalence_Inverse_Faithful]), so f ≈ g.

   ROUTE NOTE.  The issue suggested chaining [Terminal_Limit]
   (Structure/Limit/Terminal.v) with [equivalence_preserves_limits]
   (Theory/Equivalence/Limit.v).  That route does close in principle --
   [↔] is [iffT], so the data is extractable, and the empty diagram is
   the one shape for which the in-tree apex-only [PreservesLimit] is not
   deficient, its legs being vacuous.  But it costs the empty functor
   from Instance/Zero.v, a [Cone]/[IsALimit]-to-[Limit] repackaging, the
   whole RAPL chain behind [equivalence_preserves_limits], and a separate
   colimit-side argument for the initial dual; and the resulting terminal
   object is the limit apex, recoverable as F 1 only after unfolding
   several layers.  The direct transport below is three lemmas, needs no
   limit machinery at all, dualizes symmetrically, and chooses
   F 1 definitionally ([Terminal_transport_obj]).

--------
Riehl，CTiC，练习 1.6.ii(ii)：终对象沿等价映射传输。先讨论唯一性，因为它包含内容。

给定两个箭头 d ~> F 1，通过准逆 G 推它们。单位分量 1 ≅ G (F 1) 是可逆的，所以与它的 [from] 腿组成时，两个像都会落在 G d ~> 1 中，其中 [one_unique] 将它们识别出来；通过抵消单射 [from] 腿得到 fmap[G] f ≈ fmap[G] g，并且 G 是忠实的（[Equivalence_Inverse_Faithful]），所以 f ≈ g。

路线说明。问题建议将 [Terminal_Limit]（Structure/Limit/Terminal.v）与 [equivalence_preserves_limits]（Theory/Equivalence/Limit.v）链式连接。原则上该路线可以闭合——[↔] 是 [iffT]，因此数据是可提取的，并且空图是树内仅顶点 [PreservesLimit] 不不足的唯一形状，其边是空的。但这需要 Instance/Zero.v 中的空函子，一个 [Cone]/[IsALimit] 到 [Limit] 的重包装，整个 [equivalence_preserves_limits] 后面的 RAPL 链，以及为初始对偶所做的单独余极限端的论证；而由此得到的终对象是极限顶点，仅在展开若干层后才能作为 F 1 恢复。下面的直接传输是三个引理，根本不需要极限机制，对偶性对称，并且定义上选择 F 1（[Terminal_transport_obj]）。
*)
Lemma terminal_transport_unique {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (T : @Terminal C) (d : D)
  (f g : d ~{D}~> F (@terminal_obj C T)) : f ≈ g.
Proof.
  apply (fmap_inj (Faithful := Equivalence_Inverse_Faithful E)).
  apply (monic (Monic := iso_from_monic
                  (@equivalence_unit_at C D F E (@terminal_obj C T)))).
  apply (@one_unique C T).
Qed.

(*
Existence: cross the counit backwards into the image of the
   quasi-inverse, then apply F to the unique arrow G d ~> 1.

--------
存在性：将余单位向后穿过拟逆的像，然后将 F 应用于唯一箭头 G d ~> 1。
*)
Definition terminal_transport_arrow {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (T : @Terminal C) (d : D) :
  d ~{D}~> F (@terminal_obj C T) :=
  fmap[F] (@one C T (@quasi_inverse C D F E d))
    ∘ from (@equivalence_counit_at C D F E d).

Definition Terminal_transport {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (T : @Terminal C) : @Terminal D :=
  @Build_Terminal D (F (@terminal_obj C T))
    (fun d => terminal_transport_arrow E T d)
    (fun d f g => terminal_transport_unique E T d f g).

(*
The initial dual, argued directly rather than by opposing E.

   The duality route DOES exist: [EquivalenceOfCategories_op] at
   Theory/Equivalence/Limit.v opposes an equivalence, and
   [Terminal_transport (EquivalenceOfCategories_op E) I0] discharges this
   in one line.  It is not taken here because of where that constructor
   lives -- Theory/Equivalence/Limit.v carries the limit-preservation and
   RAPL development, and importing it would make this otherwise-light file
   depend on the whole chain.  Repeating a three-line argument with [epic]
   for [monic] and [zero_unique] for [one_unique] is the cheaper trade.
   Anyone who already has Limit.v in scope should prefer the one-liner.

--------
最初的对偶，直接论证而不是通过对立的 E。

对偶路径确实存在：[EquivalenceOfCategories_op] 位于 Theory/Equivalence/Limit.v 中反对一个等价，而 [Terminal_transport (EquivalenceOfCategories_op E) I0] 在一行中解决了这个问题。这里没有使用它是因为该构造所在的位置——Theory/Equivalence/Limit.v 包含极限保持和 RAPL 开发，引入它会使这个本来轻量的文件依赖整个链条。使用 [epic] 对 [monic] 和 [zero_unique] 对 [one_unique] 重复三行论证是更廉价的折衷。任何已经在作用域中包含 Limit.v 的人应该偏好使用这一行的方法。
*)
Lemma initial_transport_unique {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (I0 : @Initial C) (d : D)
  (f g : F (@initial_obj C I0) ~{D}~> d) : f ≈ g.
Proof.
  apply (fmap_inj (Faithful := Equivalence_Inverse_Faithful E)).
  apply (epic (Epic := iso_to_epic
                 (@equivalence_unit_at C D F E (@initial_obj C I0)))).
  apply (@zero_unique C I0).
Qed.

Definition initial_transport_arrow {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (I0 : @Initial C) (d : D) :
  F (@initial_obj C I0) ~{D}~> d :=
  to (@equivalence_counit_at C D F E d)
    ∘ fmap[F] (@zero C I0 (@quasi_inverse C D F E d)).

(*
[@Initial D] is notation for [@Terminal (D^op)], so the record is built
   with [Build_Terminal] at D^op; the arrow and uniqueness components are
   stated in D and accepted by conversion, which avoids writing any
   composite in the opposite category.

--------
[@Initial D] 是 [@Terminal (D^op)] 的符号表示，所以记录是用 [Build_Terminal] 在 D^op 中构建的；箭头和唯一性组件在 D 中声明并被转换接受，这避免了在对立范畴中书写任何复合结构。
*)
Definition Initial_transport {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (I0 : @Initial C) : @Initial D :=
  @Build_Terminal (D^op) (F (@initial_obj C I0))
    (fun d => initial_transport_arrow E I0 d)
    (fun d f g => initial_transport_unique E I0 d f g).

(* The transported structures choose the image of the original, on the nose. / 被运输的结构选择原始的图像，正中目标。 *)
Corollary Terminal_transport_obj {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (T : @Terminal C) :
  @terminal_obj D (Terminal_transport E T) = F (@terminal_obj C T).
Proof. reflexivity. Qed.

Corollary Initial_transport_obj {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (I0 : @Initial C) :
  @initial_obj D (Initial_transport E I0) = F (@initial_obj C I0).
Proof. reflexivity. Qed.

Section TerminalSubContractible.

Context {C : Category}.

(*
Riehl, CTiC, Lemma 1.6.16, strongest packaging: as soon as C HAS a
   terminal object, the subcategory of Block D is equivalent to the
   terminal category -- a contractible groupoid.

   The functor to 1 is [Erase]; the quasi-inverse is constant at the
   chosen object.  The counit cell is any two functors into 1 agreeing,
   which is Cat's own terminality ([Cat_Terminal], Instance/One.v); doing
   it by hand instead collapses 1's hom universe to Set and then fails a
   universe check.  The unit cell is componentwise [terminal_sub_iso],
   with the [Functor_Setoid] coherence discharged by
   [terminal_sub_hom_unique] -- in a category whose hom-sets are
   singletons, EVERY diagram commutes.

   CONSTRUCTIVE SCOPE.  Riehl's “empty or contractible” cannot be stated
   as a decidable disjunction here: `Sub C TerminalObjects` inhabited-or-
   not is exactly excluded middle for “C has a terminal object”, and this
   library is axiom-free.  What is delivered is the two halves that the
   disjunction packages: the contractibility below, conditioned on an
   inhabitant, and -- holding unconditionally, hence vacuously in the
   empty case -- [terminal_sub_hom_contractible] and [terminal_sub_IsIso]
   of Block D.

--------
Riehl, CTiC, 引理 1.6.16，最强的封装：一旦 C 有一个终对象，Block D 的子范畴等价于终范畴——一个可收缩群化范畴。

到 1 的函子是 [Erase]；准逆是恒定于所选择的对象。余单位元胞是任意两个同意的 1 中的函子，这正是 Cat 的终端性（[Cat_Terminal]，Instance/One.v）；如果手动操作，则会将 1 的 hom 宇宙折叠为 Set，然后导致宇宙检查失败。单位元胞是按分量的 [terminal_sub_iso]，其 [Functor_Setoid] 相容性通过 [terminal_sub_hom_unique] 处理——在同态集为单例的范畴中，每个图表都是交换的。

建设性范围。Riehl 的“空或可收缩”在这里不能表示为可判定的析取：`Sub C TerminalObjects` 已占有还是未占有，正好排除了“C 有终对象”的中值律，而这个库是无公理的。所提供的是该析取所包含的两部分：在有占有者的条件下的可收缩性，以及——无条件成立，因此在空情形下也是空的——Block D 的 [terminal_sub_hom_contractible] 和 [terminal_sub_IsIso]。
*)
Program Definition terminal_sub_point (T : @Terminal C) :
  _1 ⟶ Sub C TerminalObjects := {|
  fobj := fun _ => terminal_sub_obj T;
  fmap := fun _ _ _ => id
|}.

Lemma terminal_sub_counit (T : @Terminal C) :
  Erase (Sub C TerminalObjects) ◯ terminal_sub_point T ≈ Id[_1].
Proof. apply (@one_unique Cat Cat_Terminal). Qed.

Lemma terminal_sub_unit (T : @Terminal C) :
  Id[Sub C TerminalObjects]
    ≈ terminal_sub_point T ◯ Erase (Sub C TerminalObjects).
Proof.
  unshelve eexists.
  - intro a; exact (terminal_sub_iso a (terminal_sub_obj T)).
  - intros a b f; apply terminal_sub_hom_unique.
Qed.

Definition terminal_sub_contractible (T : @Terminal C) :
  EquivalenceOfCategories (Erase (Sub C TerminalObjects)) :=
  @Build_EquivalenceOfCategories (Sub C TerminalObjects) _1
    (Erase (Sub C TerminalObjects))
    (terminal_sub_point T)
    (terminal_sub_counit T)
    (terminal_sub_unit T).

End TerminalSubContractible.

Section InitialSubContractible.

Context {C : Category}.

Program Definition initial_sub_point (I0 : @Initial C) :
  _1 ⟶ Sub C InitialObjects := {|
  fobj := fun _ => initial_sub_obj I0;
  fmap := fun _ _ _ => id
|}.

Lemma initial_sub_counit (I0 : @Initial C) :
  Erase (Sub C InitialObjects) ◯ initial_sub_point I0 ≈ Id[_1].
Proof. apply (@one_unique Cat Cat_Terminal). Qed.

Lemma initial_sub_unit (I0 : @Initial C) :
  Id[Sub C InitialObjects]
    ≈ initial_sub_point I0 ◯ Erase (Sub C InitialObjects).
Proof.
  unshelve eexists.
  - intro a; exact (initial_sub_iso a (initial_sub_obj I0)).
  - intros a b f; apply initial_sub_hom_unique.
Qed.

Definition initial_sub_contractible (I0 : @Initial C) :
  EquivalenceOfCategories (Erase (Sub C InitialObjects)) :=
  @Build_EquivalenceOfCategories (Sub C InitialObjects) _1
    (Erase (Sub C InitialObjects))
    (initial_sub_point I0)
    (initial_sub_counit I0)
    (initial_sub_unit I0).

End InitialSubContractible.
