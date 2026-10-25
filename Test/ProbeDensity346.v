Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Elements.
Require Import Category.Construction.Elements.Kan.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Density.

Generalizable All Variables.

(** * Boundary probes for Theory/Density.v (issue #346) / * 针对 Theory/Density.v 的边界探针（问题 #346） *)

(*
WHY THIS FILE EXISTS, AND WHAT IT ADDS OVER THE IN-FILE PROBES.

   Theory/Density.v already carries four negatives with their controls.
   Those are sound, but they cannot guard the SIX constants the negatives
   name that are declared in that same file -- [DensityDiagram],
   [ElementsOp], [density_med], [density_inj], [density] and
   [PDensityDiagram].  A rename of any of them would rewrite the [Fail]
   bodies and the in-file controls IN LOCKSTEP, leaving every negative
   vacuously green while the build stayed clean.  That is the same
   instrument defect this tree records elsewhere: a rename simulation is
   meaningless for a constant declared in the file under test, and the
   remedy is to restate the boundary from OUTSIDE, where the names are
   not renamed alongside.

   This file is that outside.  It Requires Category.Theory.Density and
   names all six, so a rename upstream breaks THIS file loudly instead of
   silencing a probe.  The in-file negatives already cover the six DONOR
   constants they name ([Curried_Hom], [Curried_CoHom], [Elements_proj],
   [PElements_proj], [Cocone], [cocone_inj]) at 6/6, so between the two
   files every constant a negative names is guarded.

   If the [Fail] commands here stop failing, that is a real change in the
   development and this file breaks the build on purpose.

--------
为什么这个文件存在，以及它比文件内探针增加了什么内容。

Theory/Density.v 已经带有四个负例及其控制。这些负例是正确的，但它们无法保护同一文件中声明的六个常量——[DensityDiagram]、[ElementsOp]、[density_med]、[density_inj]、[density] 和 [PDensityDiagram]。重命名其中任何一个都会以 LOCKSTEP 方式重写 [Fail] 的主体以及文件内的控制，使每个负例表面上都是绿色，同时构建保持干净。这就是该树在其他地方也记录的同样的仪器缺陷：对于在被测试文件中声明的常量，重命名模拟是没有意义的，解决方法是从外部重新声明边界，在那里名称不会被同步重命名。

这个文件就是那个外部文件。它需要 Category.Theory.Density 并且列出了所有六个名称，所以上游重命名会明显破坏这个文件，而不会让探测静默。文件内的负值已经覆盖了它们命名的六个 DONOR 常量（[Curried_Hom]、[Curried_CoHom]、[Elements_proj]、[PElements_proj]、[Cocone]、[cocone_inj]），覆盖率为 6/6，所以在这两个文件之间，每个负值所命名的常量都受到保护。

如果这里的 [Fail] 命令不再失败，那就是开发中的一个真正变化，而这个文件是故意破坏构建的。
*)

Section ProbeDensityConversion.

Context {C : Category}.
Context (P : C^op ⟶ Sets).

(* CONTROL: the presheaf diagram is nameable and agrees on objects. / CONTROL: the presheaf diagram is nameable and agrees on objects. / 控制：预层图是可命名的，并且在对象上是一致的。 *)
Check @PDensityDiagram.
Check (fun (c : C) (x : P c) =>
         PDensityDiagram P ((c; x) : PElements P)).

(*
NEGATIVE 1, CONVERSION.  The two functor RECORDS are not equal: they
   differ in their functor-law fields, which [PElements_proj] supplies as
   opaque [Program] obligations while the composite rebuilds them.
   Stripped: "cannot unify PDensityDiagram P and
   Curried_CoHom C ◯ PElements_proj P".

--------
负 1，转换。两个函子 RECORDS 不相等：它们在函子定律字段上存在差异，[PElements_proj] 提供这些字段作为不透明的 [Program] 义务，而复合结构在重建它们时。简化："无法统一 PDensityDiagram P 和 Curried_CoHom C ◯ PElements_proj P"
*)
Fail Example probe_pdd_records :
  PDensityDiagram P = Curried_CoHom C ◯ PElements_proj P := eq_refl.

End ProbeDensityConversion.

Section ProbeDensityMediator.

Context {D : Category}.
Context (K : D ⟶ Sets).

(*
CONTROLS: all four file-local names below are nameable, and the
   triangle holds at [≈].

--------
控制：以下四个文件本地名称都可以命名，三角形停留在 [≈]。
*)
Check @DensityDiagram.
Check @ElementsOp.
Check @density.
Example probe_ctrl_diag :
  DensityDiagram K = Curried_Hom D ◯ (Elements_proj K)^op := eq_refl.
Definition probe_ctrl_commutes (M : Cocone (DensityDiagram K))
  (j : ElementsOp K) :
  density_med K M ∘ density_inj K j ≈ cocone_inj M j
  := density_med_commutes K M j.

(*
NEGATIVE 2, CONVERSION.  The mediating triangle is [≈] and NOT
   [eq_refl]: the mediator evaluates the competing cocone at the index
   object (e, fmap[K] g x) while the right-hand side evaluates it at j,
   and the two are reconciled only by cocone coherence at
   [Elements_lift], which is a [≈] fact.  Stripped: "cannot unify
   density_med K M ∘ density_inj K j and cocone_inj M j".

--------
负 2，转换。调解三角形是 [≈]，而不是 [eq_refl]：调解者在指标对象 (e, fmap[K] g x) 上评估竞争余锥，而右侧在 j 上评估，只有在 [Elements_lift] 上通过余锥相干性才能调和这两者，这是一条 [≈] 事实。简化："无法统一 density_med K M ∘ density_inj K j 与 cocone_inj M j"。
*)
Fail Example probe_med_strict (M : Cocone (DensityDiagram K))
  (j : ElementsOp K) :
  density_med K M ∘ density_inj K j = cocone_inj M j := eq_refl.

(*
CONTROL for negative 3: the composite IS formable with the OPPOSITE of
   the projection, which is what the diagram uses.

--------
负3的控制：复合体可以与投影的相反方向形成，这正是图中使用的。
*)
Check (Curried_Hom D ◯ (Elements_proj K)^op).

(*
NEGATIVE 3, TYPING -- the variance.  The diagram of representables
   cannot be indexed by [Elements K] covariantly, because [d ↦ [Hom d,─]]
   is contravariant.  Stripped: "Elements_proj K has type
   Elements K ⟶ D while it is expected to have type Elements K ⟶ D^op".

--------
负 3，类型检查——方差。可表示对象的图不能通过 [Elements K] 协变地建立索引，因为 [d ↦ [Hom d,─] 是逆变的。简化："Elements_proj K 的类型是 Elements K ⟶ D，而预期类型是 Elements K ⟶ D^op"。
*)
Fail Check (Curried_Hom D ◯ Elements_proj K).

End ProbeDensityMediator.

Section ProbeDensityUniverse.

Universe uo uh us.
Constraint uh < uo.
Constraint uh < us.

(*
CONTROLS: over a category whose OBJECTS sit strictly ABOVE its homs,
   the index category and the Yoneda injection are both formable, so the
   rejection below is attributable to the DIAGRAM and not to the levels
   themselves or to the index.

--------
控制：对于其对象严格位于其同态之上的范畴，可以形成指标范畴和Yoneda注入，因此下面的拒绝是由图形引起的，而不是由层次本身或指标引起的。
*)
Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) => ElementsOp K).
Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) => @yo_inj D K).

(*
NEGATIVE 4, FORMABILITY (universe).  [DensityDiagram] carries
   [u <= u0] -- D's objects at or below D's homs -- and the pin enters at
   the DIAGRAM rather than at the index or at [yo_inj].  Stripped, this
   reports a universe inconsistency naming the declared levels:
   "Cannot enforce uh = _ because uh < uo <= _".  Inherited from the
   donors, NOT introduced by Theory/Density.v, and not claimed
   unavoidable.

--------
负 4，可塑性（宇宙）。[DensityDiagram] 携带 [u <= u0] —— D 的对象位于或低于 D 的同类 —— 并且销针进入图表而不是索引或 [yo_inj]。简化后，这会报告一个宇宙不一致，命名为已声明的层级："无法强制 uh = _ 因为 uh < uo <= _"。继承自捐赠者，不是由 Theory/Density.v 引入的，也不被认为是不可避免的。
*)
Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              DensityDiagram K).

End ProbeDensityUniverse.

(*
Instrument check: [Fail] does report an error when its command
   SUCCEEDS, so the four negatives above are genuine failures rather than
   an inert command.

--------
仪器检查：当其命令成功时，[Fail]确实会报告错误，因此上面提到的四个负面情况是真正的故障，而不是无效命令。
*)
Fail Fail Check @density.
