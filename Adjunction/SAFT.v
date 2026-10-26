Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.GAFT.

Set Universe Polymorphism.

Generalizable All Variables.

(** * The Special Adjoint Functor Theorem (SAFT)  / * 特殊伴随定理 (SAFT)*)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   The Special Adjoint Functor Theorem (SAFT; Freyd, Mac Lane CWM V.8) refines
   Freyd's General Adjoint Functor Theorem (GAFT, [Adjunction/GAFT.v]) by
   *manufacturing* the solution set from three classical smallness conditions on
   the domain [C]:

     - [C] is complete;
     - [C] is *well-powered* — the subobjects of any object form a small set;
     - [C] has a *cogenerating family* [{G_j}] — a family separating parallel
       arrows through the representable functors [C(-, G_j)].

   Together with the preservation hypothesis on [U] these produce, at every
   [d : D], a solution set, and [GAFT] then yields the left adjoint [F ⊣ U].

   HYPOTHESES AS DATA (honest reading; stated explicitly per the campaign
   discipline).  The classical SAFT proof has TWO halves, and only one of them
   can be internalized in this library.

   (1) SEPARATION ⇒ MONIC — internalized, in full.  The genuine content of a
   cogenerating family is that the canonical map of any [c : C] into a power of
   the family is a monomorphism.  This is proved below as
   [cogenerator_canonical_monic], and it genuinely CONSUMES [cog_separates]:
   forming the hom-indexed power [cogen_power] of the cogenerating family — one
   factor [cog_obj G j] per arrow [k : c ~> cog_obj G j], built via [Complete] —
   the mediator [cogen_canonical] whose [(j, k)]-component is [k] itself is
   left-cancellable precisely because [G] separates parallel arrows: two arrows
   equalized by [cogen_canonical] agree after every such [k] (read off the
   matching projection), hence are equal by [cog_separates].  So [cog_separates]
   is NOT inert — it is the operative hypothesis of that lemma, and deleting the
   field breaks the file.

   (2) SMALL SOLUTION SET — packaged as DATA, of necessity.  (CORRECTION,
   #453: not of necessity; see THE BOOK'S HYPOTHESES, WITHOUT THE DATUM,
   the header's closing paragraph.)  The other half of
   the classical proof is a SIZE argument: well-poweredness makes the family of
   subobjects of the cogenerator product a *set*, and the image factorization of
   a given [h : d ~> U c] through one of those subobjects places the resulting
   member inside that set.  This library carries NO size / smallness machinery
   and NO image-factorization system on a general base, so neither “the
   subobjects form a set” nor “take the image of [h]” can be constructed
   internally — there is nothing to quantify smallness against.  (CORRECTION,
   #451: the sentence no longer holds of “the subobjects form a set”.  “The
   subobjects of every object form a small set” is now STATED, as Structure/
   WellPowered.v's [WellPowered] -- a small index for the subobjects of each
   object, pinned at or below the hom universe, with maps both ways and the
   exhaustiveness clause [wp_to_from] -- and the satellite Adjunction/SAFT/
   WellPowered.v's [WellPowered_SubobjectIndex] feeds it to this file's
   [SAFT].  What well-poweredness still does not supply is the covering
   datum; see the header's paragraph THE COVERING DATUM IS REFUTABLE AT
   THE IDENTITY OF [Sets].)  The honest
   reading — the one the plan sanctioned — is therefore to package this half as
   DATA, in exactly the shape the classical argument delivers (CORRECTION,
   #451: it is not that shape; the corrections to both bullets below say
   where it departs):

     - [SubobjectIndex x] supplies well-poweredness object-by-object, as a small
       [Type] [sub_index] of subobjects of [x], each NAMED by a monomorphism
       [sub_mono] into [x] (a subobject of [x] IS a mono into [x], per
       Theory/Morphisms.v).  The smallness content lives in the [Type]
       [sub_index] itself; the field [sub_monic] is a subobject-naming
       annotation, witnessing that each [sub_dom i] genuinely names a subobject
       of the cogenerator product [cogen_prod].  The existence proof does not
       consume [sub_monic] — smallness is supplied here as data, not derived, so
       nothing in the reduction inspects the monic witness — and [sub_monic] is
       emphatically NOT claimed to drive any factorization.
       CORRECTION (#451): an earlier revision of this bullet read
       [SubobjectIndex] as well-poweredness itself.  It is strictly weaker.
       Nothing in the record says that its family reaches EVERY subobject of
       [x], and the empty family inhabits it at every object
       ([empty_SubobjectIndex]; [SubobjectIndex_not_exhaustive] shows that
       no map from the subobjects of [x] into that index exists).
       Well-poweredness with its exhaustiveness clause is Structure/
       WellPowered.v's [WellPowered], and Adjunction/SAFT/WellPowered.v's
       [SubobjectIndex_of_WellPoweredAt] forgets it to this record, keeping
       the index universe.

     - the covering datum [cover] of [SAFT] states precisely the CONCLUSION of
       the classical image-factorization step: every [h : d ~> U c] factors,
       through a well-powered subobject [i] of [cogen_prod], as a [d]-arrow
       [s : d ~> U (sub_dom i)] followed by a [C]-arrow [t : sub_dom i ~> c].
       This is exactly one member of a solution set at [d].
       CORRECTION (#451): “precisely the CONCLUSION of the classical step” is
       false.  The classical step factors through a subobject of a product
       that DEPENDS ON [d]; [cogen_prod] does not, and the datum as stated is
       refutable where the classical hypotheses hold (the header's
       paragraph THE COVERING DATUM IS REFUTABLE AT THE IDENTITY OF
       [Sets]).  “A well-powered subobject [i]” is likewise a
       subobject NAMED by the index [WP], which need not be well-powered
       (the previous bullet's correction).  “One member of a solution set
       at [d]” stands.

   Packaging half (2) as data is a leaner-but-honest *hypothesis* form; it never
   weakens the CONCLUSION, which remains a genuine left adjoint
   [{ F : D ⟶ C & F ⊣ U }].  The completeness [comp] and cone-level preservation
   [cont] hypotheses are consumed unchanged and fed straight to [GAFT] — see the
   [Adjunction/GAFT.v] header for why the operative preservation notion is the
   cone-level [PreservesImageLimit] rather than the apex-only class.  The
   mathematical content proven here is thus twofold: the separation⇒monic lemma
   [cogenerator_canonical_monic] (half 1, fully internal and consuming
   [cog_separates]), and the reduction assembling the packaged classical data
   into a [SolutionSet] at every [d] and invoking [GAFT] (half 2, over the
   packaged smallness datum).

   THE COVERING DATUM IS REFUTABLE AT THE IDENTITY OF [Sets] (#451).
   Adjunction/SAFT/Sets.v's [SubobjectCover_Id_Sets_absurd] proves, closed
   under the global context, that [SubobjectCover (@Id Sets) comp G WP] is
   EMPTY for every completeness witness [comp], every cogenerating family
   [G] and every subobject index [WP], at every universe instance [SAFT]
   asks for at [Sets@{h cobj}] with [Set < h] (that file's UNIVERSES
   paragraph and its control [SubobjectCover_Id_Sets_absurd_at_SAFT]).
   The mechanism is [SubobjectCover_Id_retract] below: at [U := Id], the
   datum at [d := c] and [h := id] makes every object [c] a retract
   [t ∘ s ≈ id] of the domain of one indexed mono into the SINGLE object
   [cogen_prod comp G]; taking [c] to be the setoid of [Prop]-valued
   predicates on that object's carrier, Cantor's diagonal refutes it (the
   mono is injective by Instance/Sets.v's [injectivity_is_monic]).
   Classically [Sets] is complete, well-powered and cogenerated by a
   two-element set, and [Id] preserves limits, so the classical
   hypotheses hold where the datum does not: the datum is not their
   consequence.  The reason is that [cogen_prod] is the product of the
   cogenerating family and does not depend on [d].  The classical proof
   works in the comma category: nLab (adjoint functor theorem) takes “the
   set of all objects of the form d→Rc_α” as the cogenerating set of d↓R
   and builds the initial object as “the intersection = pullback of all
   subobjects of ∏_s k_s”, a product over arrows OUT OF [d].  The
   comparison with the classical hypotheses is a meta-argument, not an
   in-tree theorem.  (CORRECTION, #452: only in part.  Under one [U :
   Untruncate] every premise of [SAFT] at [Id[Sets]] but [cover] is
   inhabited in tree: [SAFT] applied to [Sets_Complete],
   [Sets_Id_PreservesImageLimit], Instance/Sets/Cogenerator.v's
   [Sets_Cogenerator_untruncate U] and [WellPowered_SubobjectIndex
   (Sets_WellPowered_untruncate U)] is accepted in a scratch file at
   [Sets@{h cobj}] with [Set < h], at the instance [SAFT]'s signature
   asks for ([Complete@{h h h cobj}], [Cogenerator@{h cobj h}],
   [SubobjectIndex@{h cobj h}]), and Adjunction/SAFT/Sets.v's
   [SubobjectCover_Id_Sets_absurd_at_SAFT] refutes [cover] for that very
   tuple, both closed under the global context.  What stays a
   meta-argument is the unconditional classical reading, the tree
   inhabiting neither [Untruncate] nor [IEM]; “cogenerated by a
   two-element set” is itself in tree under [IEM], as
   Instance/Sets/Cogenerator.v's [Sets_Cogenerator_IEM] into
   [BoolSetoid].)  In tree, at [Id[Sets]]: completeness and
   preservation are inhabited (Instance/Sets/Complete.v's [Sets_Complete],
   Adjunction/GAFT/Sets.v's [Sets_Id_PreservesImageLimit]);
   well-poweredness only under [Untruncate] (Instance/Sets/WellPowered.v's
   [Sets_WellPowered_untruncate]); and a SMALL [Cogenerator] at [Sets],
   its index at [Sets_Complete]'s shape universe where [cogen_prod]
   needs it, likewise only under [Untruncate] or [IEM]
   (Instance/Sets/Cogenerator.v's [Sets_Cogenerator_untruncate] and
   [Sets_Cogenerator_IEM]).  (CORRECTION, #452: an earlier revision said
   that no [Cogenerator] is built at [Sets] anywhere, a grep for the word
   [Cogenerator] over the .v files outside Test/ finding twelve files
   and none constructing one at [Sets]; the same grep now finds sixteen,
   the twelve and #452's four new files.  Instance/Sets/Cogenerator.v
   builds the two conditional small ones above and an unconditional
   LARGE one, [Sets_Cogenerator_large], indexed by all objects, which
   [cogen_prod] at [Sets_Complete] refuses on universes; its header also
   records the measured refusal of the [Type]-valued route to an
   unconditional small one.  Adjunction/SAFT/InitialObject/Examples.v
   builds unconditional ones at the thin categories [Subsets X] and
   [Indiscrete], and Instance/Sets/SpecialInitial.v's [setsop_cog] is one
   at [Sets^op].)
   Consequently no well-poweredness result can discharge [cover]:
   Adjunction/SAFT/WellPowered.v's [WellPowered_SubobjectIndex] supplies
   [WP], [cover] remains, and at [Id[Sets]] it is refuted whatever [WP]
   is.  [SAFT] itself is not re-shaped here; its statement, and those of
   [SAFT_solution_set] and Adjunction/Representability/Sets.v's
   [saft_representable], are unchanged.

   THE SPECIAL INITIAL-OBJECT THEOREM (#452).  Mac Lane's §V.8 Theorem 1
   -- a complete category with small hom-sets, a small cogenerating set
   and intersections of subobjects has an initial object, the
   intersection of all subobjects of the product of the cogenerating
   set -- is Adjunction/SAFT/InitialObject.v's [special_initial_object],
   built on this file's [Cogenerator], [cogen_prod], [cogen_power] and
   [cogenerator_canonical_monic].  Its witnesses are
   Adjunction/SAFT/InitialObject/Examples.v (the thin [Subsets X] and
   [Indiscrete]) and Instance/Sets/SpecialInitial.v ([Sets^op]
   unconditionally, [Sets] under [Untruncate] or [IEM]).  Mac Lane's
   proof of the special adjoint functor theorem applies it in the comma
   category d↓U, whose cogenerating family is indexed by the arrows out
   of d; that route is #453's, and [SAFT] is not re-shaped by #452.

   THE BOOK'S HYPOTHESES, WITHOUT THE DATUM (CORRECTION, #453).  The
   covering datum is superseded, not derived.
   Adjunction/SAFT/Characterization.v's [SAFT_wellpowered] builds the
   left adjoint from the classical list alone -- [Complete C], the
   cone-level continuity [PreservesImageLimit U], this file's
   [Cogenerator] and Structure/WellPowered.v's [WellPowered] -- by Mac
   Lane's comma route: #452's special initial-object theorem in each
   comma [=(d) ↓ U], whose cogenerating family is indexed by the arrows
   out of [d] ([comma_cogenerator]) and whose well-poweredness comes from
   C's through the monos lemma ([comma_WellPoweredAt]).  There
   [SAFT_wellpowered_iff] is Mac Lane's Corollary as a biconditional, and
   [SAFT_iff] is his Theorem 2, over wide pullbacks of subobjects in
   place of well-poweredness.  At one [Un : Untruncate],
   Adjunction/SAFT/Characterization/Examples.v's [sets_id_saft Un] is
   [SAFT_wellpowered] applied to [Sets_Complete],
   [Sets_Id_PreservesImageLimit], [Sets_Cogenerator_untruncate Un] and
   [Sets_WellPowered_untruncate Un], a left adjoint of [Id[Sets]], and
   its [sets_id_old_cover_refuted Un] is Adjunction/SAFT/Sets.v's
   [SubobjectCover_Id_Sets_absurd] applied to [Sets_Complete],
   [Sets_Cogenerator_untruncate Un] and [WellPowered_SubobjectIndex
   (Sets_WellPowered_untruncate Un)], refuting [cover]; both are closed
   under the global context.  [SAFT] is therefore an independent GAFT
   instance whose extra premise is refuted at [Id[Sets]], where under
   [Untruncate] the classical hypotheses hold, not a corollary of the new
   theorem, and it is kept unchanged, as are [SubobjectCover],
   [SAFT_solution_set] and their satellites.  Half (2)'s “of necessity”
   no longer stands: the comma route takes no solution set, and the
   covering datum over the product of the arrows out of [d], the one the
   classical argument uses, is a theorem in
   Adjunction/SAFT/Characterization/Cover.v. *)

(** ** Cogenerating families  / ** 热电联产家庭*)

(*
A cogenerating family for [C]: a small [Type] of indices [cog_index] with
   objects [cog_obj j : C], such that parallel arrows [f, g : x ~> y] are equal
   as soon as they agree after every arrow [k : y ~> cog_obj j] into a member of
   the family.  Equivalently the representables [C(-, cog_obj j)] are jointly
   faithful, proved both ways in Structure/Generator/Dual.v (issue #447). 

--------
[C] 的联生系列：索引 [cog_index] 的小型 [Type]
 对象 [cog_obj j : C]，使得平行箭头 [f, g : x ~> y] 相等
 一旦他们同意，每次箭头 [k : y ~> cog_obj j] 成为成员后
 家人。 等价地，可表示的 [C(-, cog_obj j)] 是联合的
 忠实的，在 Structure/Generator/Dual.v (issue #447) 中证明了这两种方式。 
*)
Record Cogenerator {C : Category} := {
  cog_index : Type;
  cog_obj : cog_index -> C;
  cog_separates : forall (x y : C) (f g : x ~> y),
    (forall (j : cog_index) (k : y ~> cog_obj j), k ∘ f ≈ k ∘ g) -> f ≈ g
}.

Arguments Cogenerator : clear implicits.
Arguments cog_index {C} _.
Arguments cog_obj {C} _ _.
Arguments cog_separates {C} _ {x y} f g _.

(** ** Well-powered indexing of subobjects  / ** 强大的子对象索引*)

(*
A chosen small indexing of the subobjects of [x] : a [Type] [sub_index] of
   indices, an object [sub_dom i : C] for each, and a monomorphism
   [sub_mono i : sub_dom i ~> x] witnessing that [sub_dom i] genuinely names a
   subobject of [x] (a subobject of [x] IS a mono into [x], per Theory/
   Morphisms.v).  Well-poweredness of [C] is then [forall x, SubobjectIndex x]:
   the subobjects of every object are supplied as a small family of data.
   CORRECTION (#451): that sentence is false.  [forall x, SubobjectIndex x]
   has no exhaustiveness clause and is inhabited in EVERY category by the
   empty family ([empty_SubobjectIndex] below), so it is strictly weaker than
   well-poweredness, which is Structure/WellPowered.v's [WellPowered]; the
   bridge [WellPowered_SubobjectIndex] (Adjunction/SAFT/WellPowered.v) goes
   one way only. 

--------
[x] 子对象的选定小索引：[Type] [sub_index]
 索引，每个索引都有一个对象 [sub_dom i : C]，以及单态性
 [sub_mono i : sub_dom i ~> x] 见证 [sub_dom i] 真正命名
 [x] 的子对象（[x] 的子对象是 [x] 的单声道，根据理论/
 态射.v)。 [C] 的强大功能是 [forall x, SubobjectIndex x]：
 每个对象的子对象都作为一个小数据族提供。 
更正（#451）：这句话是错误的。 保护11X
 没有详尽的子句，并且在每个类别中都存在
 空族（[empty_SubobjectIndex] 下面），所以它严格弱于
 well-poweredness，即 Structure/WellPowered.v 的 [WellPowered]； 的
 桥 [WellPowered_SubobjectIndex] (Adjunction/SAFT/WellPowered.v) 运行
 只有一种方式。 
*)
Record SubobjectIndex {C : Category} (x : C) := {
  sub_index : Type;
  sub_dom : sub_index -> C;
  sub_mono : forall i, sub_dom i ~> x;
  sub_monic : forall i, Monic (sub_mono i)
}.

Arguments sub_index {C x} _.
Arguments sub_dom {C x} _ _.
Arguments sub_mono {C x} _ _.
Arguments sub_monic {C x} _ _.

(** ** [SubobjectIndex] does not give well-poweredness  / ** [SubobjectIndex] 无法提供强大的功能*)

(*
The bridge the other way (#451), from Structure/WellPowered.v's
   [WellPowered] to this record, is the satellite Adjunction/SAFT/
   WellPowered.v, so that this file requires only Theory/Subobject.v for
   [SubObj] and not the well-poweredness development.  Theory/Subobject.v
   declares projections [sub_dom] and [sub_mono] of its own; they are
   written qualified below, since the unqualified names in this file are
   this file's.

   The converse is false: the empty family is a [SubobjectIndex] of every
   object of every category.  At the level of categories,
   Structure/WellPowered/Counterexample.v's [AntichainTop] carries that
   empty [SubobjectIndex] at every object and is not well-powered
   ([AntichainTop_not_WellPowered]). 

--------
另一种方式的桥 (#451)，来自 Structure/WellPowered.v's
 [WellPowered] 创下此纪录，是卫星 Adjunction/SAFT/
 WellPowered.v，因此该文件仅需要 Theory/Subobject.v
 [SubObj] 而不是强大的开发。 理论/子对象.v
 声明其自己的投影 [sub_dom] 和 [sub_mono]； 他们是
 下面写为限定名称，因为该文件中的非限定名称是
 这个文件的.

 反之亦然：空族是每个族的 [SubobjectIndex]
 每个类别的对象。 在品类层面，
 Structure/WellPowered/Counterexample.v 的 [AntichainTop] 承载了这一点
 [SubobjectIndex] 在每个物体上都是空的，并且动力不足
 ([AntichainTop_not_WellPowered])。 
*)
Definition empty_SubobjectIndex {C : Category} (x : C) : SubobjectIndex x :=
  {| sub_index := False ;
     sub_dom   := fun i => match i with end ;
     sub_mono  := fun i => match i with end ;
     sub_monic := fun i => match i with end |}.

(*
... and it cannot be completed to a well-powered index: there is no map
   from the subobjects of [x] into it, since [x] itself, along the identity,
   is a subobject. 

--------
...并且它无法完成为功能强大的索引：没有地图
 从 [x] 的子对象进入它，因为 [x] 本身，沿着恒等式，
 是一个子对象。 
*)
Lemma SubobjectIndex_not_exhaustive {C : Category} (x : C) :
  (SubObj x -> sub_index (empty_SubobjectIndex x)) -> False.
Proof.
  intros f.
  exact (f {| Subobject.sub_dom := x ;
              Subobject.sub_mono := id ;
              Subobject.sub_is_monic := id_monic x |}).
Qed.

(** ** The product of the cogenerating family  / ** 热电联产系列产品*)

(*
The product [∏_{j} cog_obj j] of the whole cogenerating family, a single
   object of [C], independent of any [d : D].  It is built as the limit of the
   discrete diagram on the family via completeness.

   These are top-level polymorphic definitions rather than section-local ones on
   purpose.  [Complete] forces the diagram category's hom universe to coincide
   with C's hom universe (see the printed signature of [Complete]), while
   [DiscreteCat_Functor] emits a diagram whose hom universe is [Set]; reconciling
   the two requires C's hom universe to absorb [Set], which a polymorphic
   definition records as a universe constraint but a rigid section variable
   cannot.  This is the universe-level shadow of the same “no size machinery”
   note in the header. 

--------
整个热电联产系列的产品 [∏_{j} cog_obj j]，单个
 [C] 的对象，独立于任何 [d : D]。 它是作为极限而构建的
 通过完整性对家庭进行离散图。 

这些是顶级多态定义，而不是局部节定义
 目的。 [Complete] 强制图表类别的 hom 宇宙重合
 与 C 的 hom 宇宙（参见 [Complete] 的打印签名），而
 [DiscreteCat_Functor] 发出一个图，其本位宇宙为 [Set]； 调和
 两者都需要C的hom宇宙来吸收[Set]，这是一种多态性
 定义记录为全域约束但为刚性截面变量
 不能。 这就是同一个“无大小机械”的宇宙级影子
 在标题中注明。 
*)
Definition cogen_prod_limit {C : Category} (comp : @Complete C)
  (G : Cogenerator C) := comp _ (DiscreteCat_Functor (cog_obj G)).

Definition cogen_prod {C : Category} (comp : @Complete C)
  (G : Cogenerator C) : C :=
  iprod (cog_obj G) (cogen_prod_limit comp G).

(** ** The canonical map into a power of the cogenerating family  / ** 联产家庭力量的规范图*)

(*
The genuine separation content of a cogenerating family, delivered and
   consumed here (so [cog_separates] is NOT inert).  Fix [c : C].  Index the
   arrows out of [c] into the family by the hom-indexed Σ-type

     [cogen_power_index G c := { j : cog_index G & c ~> cog_obj G j }],

   and form the product [cogen_power] of the family whose [(j, k)]-component is
   [cog_obj G j] — a *power* of the cogenerating family, with one factor per
   arrow [k : c ~> cog_obj G j].  The canonical map [cogen_canonical] is the
   unique mediator whose [(j, k)]-component is [k] itself; it is monic
   ([cogenerator_canonical_monic]) precisely because [G] separates, which is the
   classical “the unit into the cogenerator power is monic” step, internalized
   in full.

   The Σ-index is hom-indexed, so this product is taken against [Complete]
   exactly as [cogen_prod] is (via [cogen_power_limit], mirroring
   [cogen_prod_limit]), and it carries the same universe constraint recorded on
   [cogen_prod_limit]; every definition here is top-level polymorphic for that
   reason. 

--------
一个同生家庭的真正的分离内容，交付和
 此处消耗（因此 [cog_separates] 不是惰性的）。 修复 [c : C]。 索引
 通过 hom 索引 Σ 类型将 [c] 中的箭头引入该系列

[cogen_power_index G c := { j : cog_index G & c ~> cog_obj G j }]，

并形成该系列的产品 [cogen_power]，其 [(j, k)] 组件为
 [cog_obj G j] — 热电联产系列的*功率*，每组有一个因子
 箭头 [k : c ~> cog_obj G j]。 规范映射 [cogen_canonical] 是
 独特的中介体，其 [(j, k)] 组件是 [k] 本身； 这是莫尼克
 （[cogenerator_canonical_monic]）正是因为[G]分离，这就是
 经典的“将机组转化为热电联产功率是莫尼克”的步骤，内化
 完整。

Σ-index 是 hom-indexed，因此该产品针对 [Complete]
 与 [cogen_prod] 完全相同（通过 [cogen_power_limit]，镜像
 [cogen_prod_limit]），并且它具有与记录在上的相同的宇宙约束
 [cogen_prod_limit]； 这里的每个定义都是顶级多态的
 原因。 
*)

(* The hom-indexed Σ-index of arrows out of [c] into the cogenerating family.  / 从 [c] 进入联生系列的箭头的 hom 索引 Σ 索引。*)
Definition cogen_power_index {C : Category} (G : Cogenerator C) (c : C) : Type :=
  { j : cog_index G & c ~> cog_obj G j }.

(* The family whose [(j, k)]-component is [cog_obj G j].  / 该系列的 [(j, k)] 组件是 [cog_obj G j]。*)
Definition cogen_power_fam {C : Category} (G : Cogenerator C) (c : C) :
  cogen_power_index G c -> C :=
  fun p => cog_obj G (projT1 p).

(* Its product, drawn from completeness exactly as [cogen_prod_limit].  / 其产品的完整性与 [cogen_prod_limit] 完全相同。*)
Definition cogen_power_limit {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) :=
  comp _ (DiscreteCat_Functor (cogen_power_fam G c)).

Definition cogen_power {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) : C :=
  iprod (cogen_power_fam G c) (cogen_power_limit comp G c).

(* The family of legs [c ~> cog_obj G j] whose [(j, k)]-component is [k].  / [c ~> cog_obj G j] 腿系列，其 [(j, k)] 组件是 [k]。*)
Definition cogen_canonical_legs {C : Category} (G : Cogenerator C) (c : C) :
  forall p : cogen_power_index G c, c ~> cogen_power_fam G c p :=
  fun p => projT2 p.

(* The canonical map [c ~> cogen_power], the unique mediator of those legs.  / 规范映射 [c ~> cogen_power]，这些腿的独特中介。*)
Definition cogen_canonical {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) : c ~> cogen_power comp G c :=
  unique_obj (iprod_ump (cogen_power_fam G c) (cogen_power_limit comp G c)
                        c (cogen_canonical_legs G c)).

(*
The [(j, k)]-component of the canonical map is [k]: the projection at index
   [(j, k)] post-composed with [cogen_canonical] recovers [k].  This is exactly
   the mediator's commuting property from [iprod_ump]. 

--------
规范映射的 [(j, k)] 组件是 [k]：索引处的投影
 [(j, k)] 与 [cogen_canonical] 后合成可恢复 [k]。 这正是
 来自 [iprod_ump] 的中介者的通勤属性。 
*)
Lemma cogen_canonical_commutes {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) (j : cog_index G) (k : c ~> cog_obj G j) :
  iprod_proj (cogen_power_fam G c) (cogen_power_limit comp G c)
    (existT _ j k) ∘ cogen_canonical comp G c ≈ k.
Proof.
  exact (unique_property
           (iprod_ump (cogen_power_fam G c) (cogen_power_limit comp G c)
                      c (cogen_canonical_legs G c))
           (existT _ j k)).
Qed.

(*
SEPARATION ⇒ MONIC (the genuine content consuming [cog_separates]).  The
   canonical map of [c] into the power of the cogenerating family is monic.
   Given [g1, g2 : z ~> c] equalized by [cogen_canonical], post-composing with
   the projection at each index [(j, k)] and using [cogen_canonical_commutes]
   shows [k ∘ g1 ≈ k ∘ g2] for every [j] and every [k : c ~> cog_obj G j];
   [cog_separates] then forces [g1 ≈ g2]. 

--------
SEPARATION ⇒ MONIC（消耗 XPTECT0X 的正版内容）。 的
 [c] 到联产家族功率的规范图是 monic。 
鉴于 [g1, g2 : z ~> c] 由 [cogen_canonical] 均衡，后合成为
 每个索引 [(j, k)] 处的投影并使用 [cogen_canonical_commutes]
 显示每个 [j] 和每个 [k : c ~> cog_obj G j] 的 [k ∘ g1 ≈ k ∘ g2]；
 [cog_separates] 然后强制 [g1 ≈ g2]。 
*)
Lemma cogenerator_canonical_monic {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) : Monic (cogen_canonical comp G c).
Proof.
  constructor; intros z g1 g2 H.
  apply (cog_separates G g1 g2); intros j k.
  rewrite <- (cogen_canonical_commutes comp G c j k).
  rewrite <- !comp_assoc.
  now rewrite H.
Qed.

(** ** The covering datum and the solution set  / ** 覆盖数据和解集*)

(*
The covering datum (the packaged conclusion of the classical factorization
   step) at [d]: every [h : d ~> U c] factors through a well-powered subobject of
   the product of the cogenerating family — there is a subobject index [i], a
   [d]-arrow [s : d ~> U (sub_dom i)], and a [C]-arrow [t : sub_dom i ~> c] with
   [fmap[U] t ∘ s ≈ h].  This is exactly a member of a solution set at [d].
   CORRECTION (#451): “the packaged conclusion of the classical factorization
   step” overstates it.  The product here is independent of [d], and the datum
   is refutable at the identity of [Sets] (the header's paragraph THE
   COVERING DATUM IS REFUTABLE;
   [SubobjectCover_Id_retract] below is the first step of that refutation).
   “A well-powered subobject” is a subobject named by the index [WP], which
   need not be well-powered ([SubobjectIndex]'s correction above). 

--------
覆盖数据（经典因式分解的打包结论
 步骤）在 [d] 处：每个 [h : d ~> U c] 都通过一个功能良好的子对象进行分解
 联产系列的产品 - 有一个子对象索引 [i]，
 [d]-箭头 [s : d ~> U (sub_dom i)] 和 [C]-箭头 [t : sub_dom i ~> c]
 [fmap[U] t ∘ s ≈ h]。 这正是 [d] 解决方案集的成员。 
更正（#451）：“经典因式分解的打包结论
 步骤”夸大了它。 这里的产品独立于[d]，并且数据
 可以反驳 [Sets] 的身份（标题的段落 THE
 覆盖数据是可以反驳的；
 下面的 [SubobjectCover_Id_retract] 是反驳的第一步）。 
“功能良好的子对象”是由索引 [WP] 命名的子对象，其中
 不需要动力充足（上面 [SubobjectIndex] 的修正）。 
*)
Definition SubobjectCover {C D : Category} (U : C ⟶ D)
  (comp : @Complete C) (G : Cogenerator C)
  (WP : forall x : C, SubobjectIndex x) : Type :=
  forall (d : D) (c : C) (h : d ~> U c),
    { i : sub_index (WP (cogen_prod comp G)) &
      { s : d ~> U (sub_dom (WP (cogen_prod comp G)) i) &
        { t : sub_dom (WP (cogen_prod comp G)) i ~> c &
          fmap[U] t ∘ s ≈ h } } }.

(*
What the datum says at [U := Id] (#451): EVERY object of [C] is a retract
   of the domain of one indexed mono into the one object [cogen_prod comp G].
   It is the datum itself at [d := c] and [h := id]. 

--------
[U := Id] (#451) 中的数据说明了什么：[C] 的每个对象都是一个撤消
 将一个索引单声道的域放入一个对象 [cogen_prod comp G] 中。 
它是 [d := c] 和 [h := id] 上的数据本身。 
*)
Definition SubobjectCover_Id_retract {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (WP : forall x : C, SubobjectIndex x)
  (cover : SubobjectCover (@Id C) comp G WP) (c : C) :
  { i : sub_index (WP (cogen_prod comp G)) &
    { s : c ~> sub_dom (WP (cogen_prod comp G)) i &
      { t : sub_dom (WP (cogen_prod comp G)) i ~> c & t ∘ s ≈ id } } } :=
  cover c c id.

(*
The solution set at [d]: its members are the pairs [(i, s)] of a well-powered
   subobject [i] of the cogenerator product together with a [d]-arrow
   [s : d ~> U (sub_dom i)].  The covering property is delivered by [cover].
   (CORRECTION, #451: “well-powered subobject” here means a subobject named
   by the index [WP], which need not be well-powered; see [SubobjectIndex].) 

--------
[d] 的解决方案集：其成员是功能良好的 [(i, s)] 对
 热电联产产品的子对象 [i] 以及 [d] 箭头
 [s : d ~> U (sub_dom i)]。 覆盖性能由 [cover] 提供。 
（更正，＃451：“功能良好的子对象”在这里是指名为的子对象
 通过索引[WP]，不需要动力充足； 请参阅 [SubobjectIndex]。） 
*)
(* THE INDEX UNIVERSE [i] IS FREE HERE.  The index built below is a sigma
   over [sub_index (WP (cogen_prod comp G))] and a [d]-arrow, and nothing
   in this definition relates its level to the ambient hom universe [h].
   The [Complete] taken here is likewise unrestricted -- its shape-object
   universe stays free.  [SAFT] below is where both are pinned, by handing
   them to [GAFT].  Measured:

     SAFT_solution_set@{i cobj dobj h u u0 u1 u2 u3} :
     ∀ {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
       (comp : Complete@{u3 u1 h cobj}) (G : Cogenerator@{u1 cobj h} C)
       (WP : ∀ x : obj[C], SubobjectIndex@{u0 cobj h} x),
       SubobjectCover@{u u0 u1 u2 u3 dobj cobj h} U comp G WP
       → ∀ d : obj[D], SolutionSet@{i dobj cobj h} U d
     (* i cobj dobj h u u0 u1 u2 u3 |= h < u2 / u1 <= u3 *)

   -- [i] unrelated to anything, and [Complete]'s shape-object slot [u1]
   likewise. *)
Definition SAFT_solution_set@{i cobj dobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete C) (G : Cogenerator C)
  (WP : forall x : C, SubobjectIndex x)
  (cover : SubobjectCover U comp G WP) (d : D)
  : SolutionSet@{i dobj cobj h} U d.
Proof.
  unshelve refine
    {| sol_index := { i : sub_index (WP (cogen_prod comp G))
                      & d ~> U (sub_dom (WP (cogen_prod comp G)) i) }
     ; sol_obj := fun p => sub_dom (WP (cogen_prod comp G)) (projT1 p)
     ; sol_arr := fun p => projT2 p |}.
  intros c h.
  destruct (cover d c h) as [i [s [t e]]].
  exists (existT _ i s); simpl.
  exists t.
  exact e.
Defined.

(** ** The Special Adjoint Functor Theorem  / ** 特殊伴随定理*)

(*
SAFT.  The packaged well-powered / cogenerator data assemble a solution set at
   every [d]; completeness and cone-level preservation are handed to [GAFT],
   which returns the left adjoint [F ⊣ U].  (CORRECTION, #451: the packaged
   data are the subobject index [WP], which is not well-poweredness, the
   cogenerating family and the covering datum; “the WELL-POWEREDNESS datum”
   in the next comment is [WP] in the same sense.) 

--------
SAFT。 打包的动力良好/热电联产数据组装了一个解决方案集
 每个 [d]； 完整性和锥体级保存交给 [GAFT]，
 返回左伴随 [F ⊣ U]。 （更正，#451：打包的
 data 是子对象索引 [WP]，其功能不强大，
 联产族和覆盖数据； “动力充足数据”
 下一条评论中的 [WP] 具有相同的意义。） 
*)
(* THE TWO IDENTIFICATIONS ARRIVE HERE, from [GAFT], and the binders say
   so: [@Complete@{h h h cobj} C] puts [Complete]'s shape-object universe
   at the ambient hom universe [h], and passing [SAFT_solution_set] to
   [GAFT] forces its free index universe [i] to [h] as well.  Read
   concretely, that is a size condition on the WELL-POWEREDNESS datum: the
   sigma of [sub_index (WP (cogen_prod comp G))] with a [d]-arrow must sit
   at the hom universe, not above it.  The measured readback says it in
   one constraint -- [SubobjectIndex]'s own index universe is bounded by
   [h]:

     SAFT@{cobj dobj h u u0 u1 u2 u3} :
     ∀ {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
       (comp : Complete@{h h h cobj}),
       PreservesImageLimit@{cobj h dobj h u1 h u h}
       → ∀ (G : Cogenerator@{h cobj h} C)
           (WP : ∀ x : obj[C], SubobjectIndex@{u3 cobj h} x),
         SubobjectCover@{u2 u3 h u h dobj cobj h} U comp G WP
         → ∃ F : D ⟶ C, Adjunction@{cobj h h dobj h h h h u h u0} F U
     (* cobj dobj h u u0 u1 u2 u3 |= h < u / u3 <= h *)

   Compare [SAFT_solution_set] above, which takes [Complete@{u3 u1 h cobj}]
   with its shape-object universe [u1] FREE and leaves [i] free too: the
   whole identification is [GAFT]'s, arriving at this one line.

   Nothing here is a [Set] pin -- an earlier revision of [GAFT] printed
   one, inherited from Instance/Discrete.v's unannotated
   [DiscreteCat_Functor], and it is gone (PR “algebraic carriers are
   sets”, 2026-09-17). *)
Definition SAFT@{cobj dobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h cobj} C) (cont : @PreservesImageLimit C D U)
  (G : Cogenerator C) (WP : forall x : C, SubobjectIndex x)
  (cover : SubobjectCover U comp G WP) : { F : D ⟶ C & F ⊣ U } :=
  GAFT U comp cont (SAFT_solution_set U comp G WP cover).
