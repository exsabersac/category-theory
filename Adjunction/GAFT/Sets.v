Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.GAFT.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Adjoints.

Generalizable All Variables.

(** * The General Adjoint Functor Theorem, run at [Sets]  / * 一般伴随定理，在 [Sets] 上运行*)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   [GAFT] (Adjunction/GAFT.v) has the shape, its named hypotheses
   rewritten here as arrows,

     GAFT (U : C ⟶ D) : @Complete C
                        → @PreservesImageLimit C D U
                        → (∀ d : D, SolutionSet U d)
                        → { F : D ⟶ C & F ⊣ U }

   and before this file no closed constant of the library applied it.
   [Adjunction/SAFT.v] does call it, and [SAFT] is applied since #437;
   [Adjunction/GAFT/Examples.v] exercises the universal-arrow half
   [GAFT_from_initials], which consumes comma-category initial objects
   directly and so meets none of the three premises above.  This file applies
   [GAFT] itself, at a concrete functor, with each premise supplied by an
   in-tree construction.

   THIS IS A TOY, AND SAYING SO IS THE POINT

   The functor is [Id : Sets ⟶ Sets], so the left adjoint the theorem returns
   is naturally isomorphic to [Id] again -- [GAFT_at_Sets_Id_is_Id] proves
   that rather than leaving it to be taken on trust.  Nothing about the
   CONCLUSION is news.  What is new is that the three premises are
   simultaneously met by objects this library builds, so [GAFT] is now a
   theorem the library has run and not only a theorem it has proved:

     [@Complete Sets]                     [Sets_Complete]
                                          (Instance/Sets/Complete.v), the
                                          tree's first [Complete] instance;

     [@PreservesImageLimit Sets Sets Id]  [right_adjoint_PreservesImageLimit]
                                          (Construction/Comma/Limit.v) at
                                          [adj_id] (Instance/Adjoints.v);

     [∀ d, SolutionSet Id d]              [Sets_Id_SolutionSet] below: the
                                          one-member family at [d] itself,
                                          with [sol_arr := id].

   Of the three, only [Complete] wanted an inhabitant.  The second has a
   general in-tree supply -- [right_adjoint_PreservesImageLimit] discharges
   it for EVERY right adjoint, fed by [adj_id] and [Δ ⊣ ×] -- and since #436
   the third has the same: [solution_set_of_adjunction] builds it for every
   right adjoint, agreeing with [Sets_Id_SolutionSet] below at [eq_refl] on
   index, member and arrow.  docs/INHABITATION.md records the row.

   WHY [Id], AND WHAT A REAL APPLICATION WOULD NEED

   The solution set is the hard input: it is where the smallness condition of
   Freyd's proof does its work (Mac Lane CWM V.6).  At [U := Id] it collapses
   to the identity arrow, which is why this application is cheap.  A
   non-degenerate one would want a [U] whose comma categories carry small
   weakly initial families -- the forgetful functor of an algebraic category
   is the standard choice.  The library has no such forgetful functor into
   [Sets] with its solution set constructed, and none is attempted here.

   THE UNIVERSE INSTANCE, DISCLOSED

   [GAFT] is a [Qed]-opaque [Theorem], so its universe context is frozen at
   whatever its own proof needed.  Since the PR "algebraic carriers are sets"
   (2026-09-17) that context leaves both categories' hom and proof universes
   FREE, and the application inherits the freedom ([About], re-wrapped):

     GAFT@{cobj dobj h u u0 u1} :
       ∀ {C : Category@{cobj h h}} {D : Category@{dobj h h}}
         (U : C ⟶ D), ...

     GAFT_at_Sets_Id@{u u0 u1 u2} :
       ∃ F : Sets@{u0 u} ⟶ Sets@{u0 u}, F ⊣ Id[Sets@{u0 u}]     with u0 < u

   -- so the application IS at the polymorphic [Sets], the one
   [Sets_Complete] and [Sets_HasIndexedProducts] are stated over.

   RECORDED CORRECTION, AND IT REVERSES A CONCLUSION rather than a number.
   An earlier revision of this section read: "that context pins the hom and
   proof universes of both categories to [Set]", quoted
   [GAFT@{u u0 u1 u2 u3 u4} : ∀ {C : Category@{u1 Set Set}}
   {D : Category@{u2 Set Set}} …] and [GAFT_at_Sets_Id@{u u0 u1} :
   ∃ F : Sets@{Set u} ⟶ Sets@{Set u}, F ⊣ Id[Sets@{Set u}]], and concluded:
   "[Sets@{Set u}] … is ONE instance of the polymorphic [Sets@{u0 u}], the
   smallest … So the application demonstrates [GAFT] at a concrete category,
   not at [Sets] in the generality in which the rest of this development
   speaks of it.  The restriction comes from [GAFT], predates this file, and
   is not lifted by it."  Every clause of that was true when written.  The
   restriction was a universe-minimization artifact of Instance/Discrete.v's
   unannotated [DiscreteCat_Functor], reaching [GAFT]'s statement through
   the discrete shape its proof takes a limit over; annotating the donor at
   Instance/Discrete.v lifted it.  So the standing reading is the
   opposite of the old one: this file's application is at [Sets] in the
   generality the rest of the development speaks of, and no [Set] instance
   is involved.  What is NOT affected is the honesty of the application
   itself -- it is still [Id], and the solution set is still the degenerate
   one; see the previous section.

   A BY-PRODUCT: EQUALIZERS IN [Sets]

   [Complete_HasEqualizers] (Adjunction/GAFT.v) turns any [Complete]
   category into a [HasEqualizers] one.  At [Sets_Complete] it yields
   [Sets_HasEqualizers], one of THREE library-file inhabitants -- see the
   note below the definition.  It is left a [Definition], not an [Instance]:
   no in-tree consumer resolves [HasEqualizers] by typeclass search
   (Theory/WeaklyInitial.v takes it as an explicit argument and [GAFT]
   passes [Complete_HasEqualizers] by hand), so registering it would add
   resolution surface with no consumer.  It stands at the same [Sets@{u0 u}]
   as [Sets_Complete] -- and so, since the 2026-09-17 repair recorded above,
   does [GAFT_at_Sets_Id].  An earlier revision of this sentence contrasted
   the two, saying this one carries "no [Set] pinning" UNLIKE that one; there
   is no longer a contrast to draw.

   STATUS: axiom-free.  [Print Assumptions] reports "Closed under the global
   context" for every constant below; the Makefile's [print-assumptions]
   target audits [GAFT_at_Sets_Id] and [Sets_HasEqualizers]. *)

(** ** The three premises  / ** 三个处所*)

(*
[Id] is a right adjoint -- to itself, by [adj_id] -- so the general bridge
   of Construction/Comma/Limit.v supplies its cone-level preservation. 

--------
XPROTECT 0X 是 XPROTECT 1X 对其自身的右伴随，因此 Construction/Comma/Limit.v 的通用桥提供其锥体级保留。 
*)
Definition Sets_Id_PreservesImageLimit : @PreservesImageLimit Sets Sets Id :=
  right_adjoint_PreservesImageLimit (@adj_id Sets).

(*
A solution set at [d] for [Id]: the one-member family whose single object
   is [d] and whose single arrow is [id[d]].  Every [h : d ~> c] factors as
   [fmap[Id] h ∘ id ≈ h], which is [id_right].

   [Build_SolutionSet] is applied with all four of its parameters written out.
   That is not stylistic: it was forced by a measured break.  A record literal
   [{| sol_arr := fun _ => id ; ... |}] elaborates its fields before the
   ascribed type has fixed [U] and [D], so [id] is elaborated against
   [?d ~{?D}~> fobj[?U] d].  Rocq 9.1 resolves that from the ascription; Coq
   8.19 and 8.20 do not, and report "The term id{?Category} ... is expected to
   have type ?d ~{?D}~> fobj[?U] d" (observed on both, through
   [nix build .#category-theory_8_19 .#category-theory_8_20]).  Naming the
   parameters removes the metavariables.  Closing the covering equation with
   [exact (id_right h)] rather than [apply id_right] is defensive against the
   same class of problem and was not separately measured: [exact] settles
   [fmap[Id] h ∘ id ≈ h] by CONVERSION, [fmap[Id]] beta-iota-reducing to the
   identity, instead of leaving that reduction to unification. 

--------
[d] 为 [Id] 设置的解决方案：单成员家族，其单个对象
 是 [d]，其单箭头是 [id[d]]。 每个 [h : d ~> c] 因子为
 [fmap[Id] h ∘ id ≈ h]，即 [id_right]。

应用 [Build_SolutionSet] 时，其所有四个参数均已写出。 
这不符合风格：这是有节制的休息所迫使的。 记录文字
 [{| sol_arr := fun _ => id ; ... |}] 在之前详细阐述了它的字段
 归因类型已固定[U]和[D]，因此[id]针对
 [?d ~{?D}~> fobj[?U] d]。 Rocq 9.1 从归属中解决了这个问题； 柯克
 8.19 和 8.20 没有，并报告“术语 id{?Category} ... 预计
 具有类型 ?d ~{?D}~> fobj[?U] d" （在两者上观察到，通过
 [nix build .#category-theory_8_19 .#category-theory_8_20]）。 命名
 参数删除元变量。 封闭覆盖方程
 [exact (id_right h)] 而非 [apply id_right] 可以防御
 同一类问题且未单独测量：[exact] 解决
 [fmap[Id] h ∘ id ≈ h] 通过转换，[fmap[Id]] beta-iota 还原为
 身份，而不是将这种简化留给统一。 
*)
Definition Sets_Id_SolutionSet (d : Sets) : SolutionSet (@Id Sets) d.
Proof.
  unshelve refine (@Build_SolutionSet Sets Sets (@Id Sets) d
                     poly_unit
                     (fun _ : poly_unit => d)
                     (fun _ : poly_unit => @id Sets d)
                     _).
  intros c h.
  exists ttt.
  exists h.
  exact (id_right h).
Defined.

(** ** The application  / ** 应用*)

(*
[GAFT] at [Id : Sets ⟶ Sets], all three premises discharged by in-tree
   constructions.  An earlier revision of this comment pointed at "the [Set]
   pinning this inherits from [GAFT]'s frozen universe context"; that pinning
   was removed on 2026-09-17 and the header records the measurement. 

--------
[GAFT] 和 [Id : Sets ⟶ Sets]，所有三个场所均由 in-tree 释放
 建筑。 此评论的早期修订版指出“[Set]
 固定它继承自 [GAFT] 的冻结宇宙上下文”； 那个固定
 于 2026-09-17 被删除，标题记录了测量结果。 
*)
Definition GAFT_at_Sets_Id : { F : Sets ⟶ Sets & F ⊣ Id } :=
  GAFT (@Id Sets) Sets_Complete
    Sets_Id_PreservesImageLimit Sets_Id_SolutionSet.

(*
The produced left adjoint is naturally isomorphic to [Id], as it must be:
   left adjoints to a fixed functor are unique up to natural isomorphism
   ([left_adjoint_iso], Theory/Adjunction.v), and [adj_id] exhibits [Id]
   as a second left adjoint to [Id].  This is what makes the "toy" label
   above a proved statement rather than an editorial one. 

--------
生成的左伴随自然与 [Id] 同构，因为它必须是：
 固定函子的左伴随物在自然同构方面是唯一的
 （[left_adjoint_iso]，Theory/Adjunction.v）和 [adj_id] 展示了 [Id]
 作为 [Id] 的第二个左伴随。 这就是“玩具”标签的由来
 以上是经过验证的陈述，而不是社论的陈述。 
*)
Definition GAFT_at_Sets_Id_is_Id : projT1 GAFT_at_Sets_Id ≈ @Id Sets :=
  left_adjoint_iso (@Id Sets) (projT1 GAFT_at_Sets_Id) (@Id Sets)
    (projT2 GAFT_at_Sets_Id) (@adj_id Sets).

(** ** By-product: equalizers in [Sets]  / ** 副产品：[Sets] 中的均衡器*)

(*
Read off completeness by [Complete_HasEqualizers]; NOT the first and not
   the only inhabitant -- see the note below.  Kept a [Definition]. 

--------
通过[Complete_HasEqualizers]读取完整性； 不是第一个也不是
 唯一的居民——见下面的注释。 保留了 [Definition]。 
*)
Definition Sets_HasEqualizers : HasEqualizers Sets :=
  Complete_HasEqualizers Sets_Complete.

(* IT IS NOT THE ONLY ONE, IN EITHER SENSE.  THREE library files inhabit
   [HasEqualizers Sets]: this one, [SetsEqualizers]
   (Adjunction/CokernelPair.v, whose own comment calls its
   route "the cheapest of the three in-tree routes"), and
   [DiagSets_HasEqualizers] (Adjunction/Diagonal/Finite.v); all three
   are registered in _CoqProject.  Test/ProbeToposInstances404.v adds a
   fourth, CONDITIONAL one resting on [Untruncate].  None of the four is
   compared with any other: their types line up and no agreement proof is
   built.  An earlier revision of this note, and of the header sentence
   above, called this the only library-file inhabitant; that was false when
   written -- the other two predate it -- and is corrected here rather than
   amended away.  The note stays below the definition so that the line
   number of [Sets_HasEqualizers] does not move.  State the criterion, since
   the number moves with it: FIVE `.v` files cited that line number before
   this change, seven occurrences counting CLAUDE.md's two, and
   Instance/Sets/Cone.v is the sixth `.v` citation. *)

(**
** The characterization at [Sets], and that its reverse half is the
       application already here 

--------
** [Sets] 的表征，其反半部分是
 申请已经在这里 
*)

(*
#436's [GAFT_iff] read at [Id : Sets ⟶ Sets].  These are cross-checks,
   not new results: they demonstrate that the biconditional's reverse half
   IS [GAFT_at_Sets_Id] above, on the nose, and that the solution set the
   forward half manufactures out of an adjunction agrees with the
   hand-built [Sets_Id_SolutionSet] in index, member and arrow — while
   NOT being the same record, since the two [sol_covers] witnesses differ
   (Test/ProbeGAFTCharacterization436.v pins that). 

--------
#436 的 [GAFT_iff] 在 [Id : Sets ⟶ Sets] 处读取。 这些都是交叉检查，
 不是新结果：它们证明了双条件的反向一半
 是 [GAFT_at_Sets_Id] 上面，在鼻子上，并且该解决方案设置了
 前半部分制造商同意
 在索引、成员和箭头中手工构建 [Sets_Id_SolutionSet] — 同时
 不是相同的记录，因为两个 [sol_covers] 见证人不同
 （Test/ProbeGAFTCharacterization436.v 引脚）。 
*)

Definition GAFT_iff_at_Sets_Id :
  { F : Sets ⟶ Sets & F ⊣ Id }
    ↔ (@PreservesImageLimit Sets Sets Id * (∀ d : Sets, SolutionSet (@Id Sets) d))
  := GAFT_iff (@Id Sets) Sets_Complete.

Definition Sets_Id_has_left : { F : Sets ⟶ Sets & F ⊣ Id } :=
  snd GAFT_iff_at_Sets_Id (Sets_Id_PreservesImageLimit, Sets_Id_SolutionSet).

Definition Sets_Id_has_left_is_GAFT_at_Sets_Id :
  Sets_Id_has_left = GAFT_at_Sets_Id := eq_refl.

(*
The manufactured family at [Id], and its agreement with the hand-built
   one at each of the three data fields. 

--------
[Id] 的制造系列及其与手工构建的协议
 三个数据字段中的每一个字段都有一个。 
*)

Definition Sets_Id_SolutionSet_of_adjunction (d : Sets) : SolutionSet (@Id Sets) d :=
  solution_set_of_adjunction (@adj_id Sets) d.

Definition Sets_Id_sols_index (d : Sets) :
  sol_index (Sets_Id_SolutionSet_of_adjunction d)
    = sol_index (Sets_Id_SolutionSet d) := eq_refl.

Definition Sets_Id_sols_obj (d : Sets) (i : poly_unit) :
  sol_obj (Sets_Id_SolutionSet_of_adjunction d) i
    = sol_obj (Sets_Id_SolutionSet d) i := eq_refl.

Definition Sets_Id_sols_arr (d : Sets) (i : poly_unit) :
  sol_arr (Sets_Id_SolutionSet_of_adjunction d) i
    = sol_arr (Sets_Id_SolutionSet d) i := eq_refl.
