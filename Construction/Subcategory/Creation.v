(*
   * * Full subcategories closed under limits are created into

   A full subcategory whose objects are closed under the limits of the
   ambient category inherits those limits, and its inclusion CREATES them
   in Mac Lane's sense (§V.1, the definition Structure/Limit/Creation.v
   carries as [CreatesLimit]): every limiting cone in the ambient category
   over a diagram of subcategory objects lifts, uniquely up to the
   canonical isomorphism, to a limiting cone in the subcategory.  This is
   the elementary half of the folklore that a limit-closed full
   subcategory is "as complete as its ambient category" (nLab:
   https://ncatlab.org/nlab/show/created+limit, and Mac Lane §V.4
   Theorem 2 for the passage from creation to completeness).  Until
   this file the tree's only route from a subcategory to [CreatesLimit]
   went through reflectivity (Construction/Reflective/Limit.v,
   [reflective_CreatesLimit]); closure under limits is the weaker and
   more common hypothesis, and it is the one Instance/Top/CompHaus.v
   needs to STATE the compact-Hausdorff creation question without a
   reflector.

   WHAT IS DELIVERED.  Over [C : Category], [S : Subcategory C] with
   [full : Full C S]:
   - [ClosedUnderLimits S : Type], the hypothesis: for every shape [J],
   diagram [K : J ⟶ Sub C S] and cone [N] over [Incl C S ◯ K] that is
   limiting in [C], the apex [vertex_obj[N]] satisfies [sobj S].  No
   clause about legs is needed: [S] is full, so every arrow of [C]
   between [S]-objects is an [S]-arrow.
   - [sub_lift N HN : Cone K], the lifted cone — the SAME apex and the
   SAME legs, packaged with the closure and fullness witnesses; both
   read back at [eq_refl] ([sub_lift_apex], [sub_lift_leg]).
   - [sub_cone_iso N HN : ConeIso (FCone (Incl C S) (sub_lift N HN)) N],
   the comparison, which is the IDENTITY isomorphism.
   - [sub_ReflectsLimitCone K : ReflectsLimitCone K (Incl C S)], from
   Theory/Equivalence/Limit.v's [ff_reflect_ump]: the inclusion is full
   ([Full_Implies_Full_Functor]) and faithful ([Incl_Faithful]), and
   fully faithful functors reflect limits — the same route
   Construction/Reflective/Limit.v takes.
   - [sub_CreatesLimit K : CreatesLimit K (Incl C S)], the three fields
   above; [sub_CreatesAllLimits : CreatesAllLimits (Incl C S)]; and
   [sub_Complete : Complete C → Complete (Sub C S)] through
   Structure/Limit/Creation.v's [creates_limits_Complete] (Mac Lane
   §V.4 Theorem 2, second half).

   HYPOTHESES SPENT.  [full] enters the lift's legs and the reflection;
   [closed] enters the lift's apex only.  Nothing is registered as an
   [Instance], following Structure/Limit/Creation.v's discipline
   that creation witnesses are passed explicitly.

   UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK OVER ALL 9 CONSTANTS. ZERO
   word-bounded [Set]. [ClosedUnderLimits@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9} :
   ∀ {C : Category@{u u0 u0}}, Subcategory@{u u0 u1 u2} C → Type@{u4}] carries
   no equation, nor do [sub_CreatesAllLimits] and [sub_Complete]. [sub_lift],
   [sub_lift_apex], [sub_lift_leg], [sub_cone_iso] and [sub_CreatesLimit] each
   carry FIVE block equations: [u0 = u11] identifies the ambient hom universe
   with the shape's — Structure/Limit/Preservation.v's [IsLimitCone] pin,
   inherited — and [u0 = u13] with [Sub]'s, imposed by [Compose] in [Incl C S
   ◯ K] ([Compose] types its three categories at one hom universe; an audit
   isolated the two causes with two probes), and [u5 = u12], [u6 = u14], [u9 =
   u10] identify the closure hypothesis' quantified shape and [Sub] levels
   with the diagram's, so the hypothesis is consumed at the diagram's own
   universe instance; [sub_ReflectsLimitCone] carries the first two only.
   [sub_CreatesLimit@{u … u17} : ∀ {C : Category@{u u0 u0}} (S :
   Subcategory@{u u0 u1 u2} C), Full C S → ClosedUnderLimits S → ∀ {J :
   Category@{u10 u11 u11}} (K : J ⟶ Sub C S), CreatesLimit@{u6 u7 u u15 u8 u10
   u11 u12} K (Incl C S)].

   COUNTS. 9/9 constants (7 [Definition], 2 [Example]) closed under the global
   context with ZERO [Axioms:] lines, all in the [make print-assumptions] gate
   FULLY QUALIFIED; no [Program]. Two [Defined]-terminated proofs:
   [sub_lift]'s flip to [Qed] breaks this file at its own readback
   [sub_lift_apex] (load-bearing); [sub_cone_iso]'s flip leaves this file,
   Instance/Top/CompHaus.v and Test/ProbeCompHaus413.v green and it is kept
   [Defined] by the data convention. Closure 35 modules excluding self —
   Theory/Equivalence/Limit.v costs 10 at the margin,
   Structure/Limit/Creation.v 3, Construction/Subcategory.v 1, each of the
   other eight [Category.*] [Require]s 0 (eleven in all, each dropped alone).
   Zero collisions over the 9 names. Pinned and read back at [eq_refl] by
   Test/ProbeCompHaus413.v: the lift's apex and legs.

   NOT DELIVERED.  The non-full case (a [Subcategory] whose [shom] is
   not everything: the lift's legs would need an [shom] witness the
   closure hypothesis does not provide); the converse (that a full
   subcategory whose inclusion creates limits is closed under them — true
   by [creates_lift], but not stated); strict creation
   ([StrictlyCreatesLimit]); the colimit dual; any witness of
   [ClosedUnderLimits] at a concrete subcategory (Instance/Top/CompHaus.v
   applies the lemma as a CONDITIONAL, [Top] having no limits beyond the
   terminal object to be closed under; CORRECTION (#410): [Top] now has
   at least one more, Instance/Top/Solenoid.v's [solenoid_limit], the
   limit of a tower of circles over [Omega^op]; CORRECTION (#461): the
   tree's first witnesses are Instance/Top/Hausdorff.v's [PSep_closed]
   and [PT3_closed], over the Prop-valued spaces [PTopCat]); and any
   relation to reflectivity (a reflective subcategory is closed under
   limits, but that implication is not proved here). 

   --------
   * * 在极限下封闭的完整子范畴被创建为一个对象在极限运算下封闭的全子范畴会继承这些极限，并且在 Mac Lane 的意义下，其包含函子会“创造”这些极限（参见 §V.1，Definition Structure/Limit/Creation.v 中的 [CreatesLimit]）：在上层范畴中，对子范畴对象的图的每一个极限锥都可以唯一地（至规范同构）提升为子范畴中的极限锥。这是一个极其基础的经验法则的一半，即一个极限闭全子范畴“和它的上层范畴一样完备”（nLab: https://ncatlab.org/nlab/show/created+limit, 以及 Mac Lane §V.4 定理 2，将创造性极限推向完备性的论述）。直到这个文件之前，树从子类别到 [CreatesLimit] 的唯一路径是通过反射率 (Construction/Reflective/Limit.v, [reflective_CreatesLimit])；在极限下闭合是较弱且更常见的假设，而 Instance/Top/CompHaus.v 需要它来陈述紧致-豪斯多夫生成问题，而无需反射器。交付的内容。通过 [C : Category]、[S : Subcategory C] 和 [full : Full C S]：
   - [ClosedUnderLimits S : Type]，假设：对于每个形状 [J]、图 [K : J ⟶ Sub C S] 以及在 [C] 中极限的锥 [N] 在 [Incl C S ◯ K] 上，顶点 [vertex_obj[N] 满足 [sobj S]。不需要关于边的条款：[S] 是满的，所以 [C] 中 [S] 对象之间的每个箭头都是 [S] 箭头。
   - [sub_lift N HN : Cone K]，被提升的锥——相同的顶点和相同的边，与闭包和满性的证明一起打包；两者在 [eq_refl]（[sub_lift_apex], [sub_lift_leg]）中重新读取。
   - [sub_cone_iso N HN : ConeIso (FCone (Incl C S) (sub_lift N HN)) N]，比对，是恒等同构。-  [sub_ReflectsLimitCone K : ReflectsLimitCone K (Incl C S)]，来自 Theory/Equivalence/Limit.v 的 [ff_reflect_ump] ：该包含是满的 ([Full_Implies_Full_Functor]) 并且是忠实的 ([Incl_Faithful])，且全忠实函子会反映极限——Construction/Reflective/Limit.v 采取了相同的路线。- [sub_CreatesLimit K : CreatesLimit K (Incl C S)]，上述三个字段；[sub_CreatesAllLimits : CreatesAllLimits (Incl C S)]；以及 [sub_Complete : Complete C → Complete (Sub C S)] 通过 Structure/Limit/Creation.v 的 [creates_limits_Complete] （Mac Lane §V.4 定理 2，后半部分）。

   假设已使用。[full] 进入提升的腿和反射；[closed] 仅进入提升的顶点。没有任何内容被登记为 [Instance]，根据 Structure/Limit/Creation.v 的规定，创建的证据是显式传递的。宇宙，测量覆盖所有 9 个常数的绑定器和块。零  
   词界定 [Set]。[ClosedUnderLimits@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9} :  
   ∀ {C : Category@{u u0 u0}}, Subcategory@{u u0 u1 u2} C → Type@{u4}] 不包含任何方程，[sub_CreatesAllLimits] 和 [sub_Complete] 也不包含。[sub_lift]、[sub_lift_apex]、[sub_lift_leg]、[sub_cone_iso] 和 [sub_CreatesLimit] 每个都包含五个块方程：[u0 = u11] 将环境同类宇宙与形状的 — Structure/Limit/Preservation.v 的 [IsLimitCone] 引脚（继承的）以及 [u0 = u13] 与 [Sub] 的关系，受 [Compose] 在 [Incl C S ◯ K] 中施加（[Compose] 在一个同类宇宙中对三类进行类型化；一次审计使用两个探针隔离两个原因），以及 [u5 = u12]、[u6 = u14]、[u9 = u10] 标识闭包假设的量化形状和 [Sub] 等级与图表的对应，因此假设在图表自身的宇宙实例中被消耗；[sub_ReflectsLimitCone] 仅承载前两个。[sub_CreatesLimit@{u … u17} : ∀ {C : Category@{u u0 u0}} (S : Subcategory@{u u0 u1 u2} C), Full C S → ClosedUnderLimits S → ∀ {J : Category@{u10 u11 u11}} (K : J ⟶ Sub C S), CreatesLimit@{u6 u7 u u15 u8 u10 u11 u12} K (Incl C S)].计数。9/9 个常量（7 个 [Definition]，2 个 [Example]）在全局上下文下关闭，零 [Axioms:] 行，全在 [make print-assumptions] 门中完全限定；没有 [Program]。两个 [Defined] 终结的证明：[sub_lift] 翻转到 [Qed] 使该文件在其自身回读处断裂 [sub_lift_apex]（承重）；[sub_cone_iso] 翻转后，该文件 Instance/Top/CompHaus.v 和 Test/ProbeCompHaus413.v 仍为绿色，并由数据约定保持 [Defined]。封闭 35 个模块（不包括自身）—— Theory/Equivalence/Limit.v 边际成本为 10，Structure/Limit/Creation.v 为 3，Construction/Subcategory.v 为 1，其余八个 [Category.*] [Require] 各为 0（共十一，每个单独丢弃）。9 个名称上零碰撞。由 Test/ProbeCompHaus413.v 在 [eq_refl] 固定并回读：升降机的顶点和支腿。未送达。非完整情况（一个  [Subcategory]  其  [shom]  并非全部：升降机的腿将需要一个  [shom]  证人，闭合假设并未提供）；逆命题（即一个完全子范畴，其包含产生极限是封闭的——根据  [creates_lift]  为真，但未声明）；严格创建（[StrictlyCreatesLimit]）；余极限对偶；在具体子范畴中  [ClosedUnderLimits]  的任何证人（Instance/Top/CompHaus.v 将引理作为条件性应用，[Top] 除终对象外没有极限可以封闭；更正 (#410)：[Top] 现在至少还有一个，Instance/Top/Solenoid.v 的 [solenoid_limit]，一系列圆构成的塔在 [Omega^op] 上的极限；更正 (#461)：树的第一个证人是 Instance/Top/Hausdorff.v 的 [PSep_closed] 和 [PT3_closed]，在 Prop 值空间 Z 上）ZW79WZZ ); 以及与反射性的任何关系（反射子类在极限下是闭合的，但这里未证明该推论）。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(*
   * * A full subcategory closed under limits is created into by its inclusion 

   --------
   * * 一个在极限下封闭的完整子范畴被它的包含创造
*)

Section SubcategoryCreation.

Context {C : Category} (S : Subcategory C) (full : Full C S).

(*
 Closure under limits: the apex of any limiting cone in [C] over a diagram
 of [S]-objects is again an [S]-object.  The legs need no clause because
 [S] is full. 

 --------
 极限下的闭合性：在 [C] 上关于 [S] 对象图的任何极限锥的顶点再次是一个 [S] 对象。因为 [S] 是满的，所以腿不需要条款。
*)
Definition ClosedUnderLimits : Type :=
  ∀ (J : Category) (K : J ⟶ Sub C S) (N : Cone (Incl C S ◯ K)),
    IsLimitCone N → sobj C S (vertex_obj[N]).

Context (closed : ClosedUnderLimits).

Section AtDiagram.
Context {J : Category} (K : J ⟶ Sub C S).

(*
 The lift: the same apex and the same legs, now inside [Sub C S]. 

 --------
 电梯：相同的顶点和相同的腿，现在在 [Sub C S] 内。
*)
Definition sub_lift (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N) : Cone K.
Proof using C J K S closed full.
  unshelve refine
    (@Build_Cone J (Sub C S) K (vertex_obj[N]; closed J K N HN)
       (@Build_ACone J (Sub C S) (vertex_obj[N]; closed J K N HN) K
          (fun x => (cone_leg N x; full _ _ _ _ (cone_leg N x))) _)).
  intros x y f; simpl.
  exact (@cone_coherence J C (vertex_obj[N]) (Incl C S ◯ K) coneFrom x y f).
Defined.

Example sub_lift_apex (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N) :
  (`1 vertex_obj[sub_lift N HN]) = vertex_obj[N] := eq_refl.

Example sub_lift_leg (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N) (x : J) :
  (`1 (cone_leg (sub_lift N HN) x)) = cone_leg N x := eq_refl.

(*
 The image of the lift is [N] itself, up to the identity isomorphism. 

 --------
 提升的像是 [N] 自身，到恒等同构为止。
*)
Definition sub_cone_iso (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N) :
  ConeIso (FCone (Incl C S) (sub_lift N HN)) N.
Proof using C J K S closed full.
  exists iso_id.
  intro x; simpl. now rewrite id_right.
Defined.

(*
 Reflection: [Incl C S] is full and faithful.
 CORRECTION (#481): the body wrote out [@ff_reflect_ump (Sub C S) C
 (Incl C S) (Full_Implies_Full_Functor C S full) (Incl_Faithful C S) J K
 M (limitcone_isalimit H) (fun x => reflexivity _)], which is
 Theory/Equivalence/Limit.v's [ff_ReflectsLimitCone] at the inclusion's
 fullness and faithfulness: the two read back as one at [eq_refl]
 (measured).  The body now calls that constant, eta-expanded, and the
 [About] blocks of this file's nine constants are unchanged, the two
 equations of this one's among them (compared by script against the
 earlier body). 

 --------
 反射：[Incl C S] 是满射且忠实的。
 修正 (#481)：主体写出了 [@ff_reflect_ump (Sub C S) C (Incl C S) (Full_Implies_Full_Functor C S full) (Incl_Faithful C S) J K M (limitcone_isalimit H) (fun x => reflexivity _)]，它是 Theory/Equivalence/Limit.v 中 [ff_ReflectsLimitCone] 在包含的满射性和忠实性上的表示：在 [eq_refl]（已度量）处两者被读取为一个。主体现在称其为常量、η-展开，而本文件的 [About] 块的九个常量保持不变，其中一者的两个方程也包含在内（通过脚本与先前主体进行比较）。
*)
Definition sub_ReflectsLimitCone : ReflectsLimitCone K (Incl C S) :=
  fun M H =>
    @ff_ReflectsLimitCone (Sub C S) C (Incl C S)
      (Full_Implies_Full_Functor C S full) (Incl_Faithful C S) J K M H.

Definition sub_CreatesLimit : CreatesLimit K (Incl C S) :=
  {| creates_lift      := sub_lift
   ; creates_lift_over := sub_cone_iso
   ; creates_reflect   := sub_ReflectsLimitCone |}.

End AtDiagram.

Definition sub_CreatesAllLimits : CreatesAllLimits (Incl C S) :=
  fun J K => sub_CreatesLimit K.

(*
 Mac Lane §V.4 Theorem 2, second half, at a full subcategory closed under
 limits: the subcategory inherits completeness. 

 --------
 Mac Lane §V.4 定理 2，下半部分，在一个对极限封闭的满子范畴中：该子范畴继承完全性。
*)
Definition sub_Complete (HC : @Complete C) : @Complete (Sub C S) :=
  creates_limits_Complete (Incl C S) HC sub_CreatesAllLimits.

End SubcategoryCreation.
