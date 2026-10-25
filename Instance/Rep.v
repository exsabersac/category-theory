(* * * Rep_K(G): K-linear representations of a group / * * Rep_K(G)：群的 K-线性表示 *)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Thin.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.GL.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Order.
Require Import Category.Instance.Grp.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
 ed., §II.4, printed p. 41 (PDF 51) —
 maclane:II.4:construction3
 Book:      Awodey, "Category Theory", 2nd ed., §7.1, printed p. 153 —
 awodey:7.1:construction-linear-representation
 nLab:      https://ncatlab.org/nlab/show/representation
 nLab:      https://ncatlab.org/nlab/show/group+representation
 Wikipedia: https://en.wikipedia.org/wiki/Group_representation

 Mac Lane's third construction in §II.4: for a commutative ring K and
 a group G, a K-linear representation of G is a K-module V together
 with a homomorphism from G into the group of automorphisms of V, an
 intertwiner between two such is a module map commuting with the two
 actions, and the resulting category is the functor category
 [B G, K-Mod].  Awodey states the same identification in §7.1 and
 immediately draws the degenerate consequence: a functor from a group
 into a poset carries every element to an identity, so there are no
 interesting representations of a group in an order.

 This file is Instance/Fun/Action.v's structural twin one door down.
 That file is Mac Lane's construction 2 — actions on SETS, the
 category [MSet M] of M-actions and equivariant maps, and the
 equivalence [MSet_Fun_equiv : [Deloop M, Sets] ≅[Cat] MSet M].  Here
 [Sets] is replaced by [RMod K] and "action by functions" by "action
 by module automorphisms"; the architecture, including how naturality
 over one object collapses to a single commuting square and how the
 functor-side round trip is rebuilt with a transparent component
 family, is that file's and is followed rather than re-invented.

 - [grp_mon]: the monoid underlying a group object, the converter
 that lets Instance/Grp.v's [GrpObject] be delooped
 - [RepObject K G]: a K-module with a homomorphism from G into the
 units of its endomorphism monoid — the issue-literal
 automorphism form
 - [rep_act], [rep_act_unit], [rep_act_mul], [rep_act_iso]: the
 action read off that homomorphism, its two laws, and each
 element acting as an isomorphism of [RMod K]
 - [monhom_of_rep] / [rep_of_monhom]: the passage between the
 automorphism-valued and the endomorphism-valued (working) forms,
 with both round trips definitional
 - [Intertwiner], [Rep K G]: module maps commuting with the actions,
 and the category they form
 - [Rep_Fun_equiv]: the headline —
 [[Deloop (grp_mon G), RMod K] ≅[Cat] Rep K G]
 - [thin_functor_endo_trivial], [thin_group_functor_trivial],
 [proset_group_functor_trivial]: Awodey's degeneracy
 - [trivial_rep], [sign_rep]: the two witnesses

 Design:

 1. THE TWO [GrpObject] RECORDS.  The tree carries two records of that
 name.  Construction/Deloop.v's extends [MonObject] by a two-sided
 inverse and is what [Deloop] and Structure/Groupoid.v's [MonHom]
 machinery consume; Instance/Grp.v's is the object of the official
 category [Grp] (carrier setoid, unit, multiplication, inversion,
 with only the LEFT unit and inverse laws as fields), and is what
 Instance/Matr/GL.v's [UnitsOf] produces.  Since the issue-literal
 statement of a representation names the group of automorphisms —
 i.e. [UnitsOf] — the primitive here is Instance/Grp.v's record,
 imported LAST so that the bare names [GrpObject], [grp_inv],
 [grp_mul], [grp_unit] all refer to it.  [grp_mon] is the one-line
 converter into [MonObject]: carrier, unit and multiplication
 unchanged, associativity flipped (Deloop's [mon_op_assoc] is
 stated in [comp_assoc]'s orientation) and the right unit law taken
 from Instance/Grp.v's derived [grp_mul_unit_r].  Delooping is
 therefore always [Deloop (grp_mon G)].

 2. THE AUTOMORPHISM FORM IS PRIMITIVE, AND THE PASSAGE COSTS
 NOTHING.  [RepObject] carries [rep_hom : GrpHom G (UnitsOf
 (hom_monoid (RMod K) rep_mod) (rmod_hom_monoid_prop K rep_mod))] —
 literally "a homomorphism from G into the automorphisms of V".
 (An earlier revision of this line omitted the second argument of
 [UnitsOf].  Since the PR "algebraic carriers are sets" (2026-09-17)
 [UnitsOf] asks the monoid's carrier setoid for a [Prop] equality, and
 [rmod_hom_monoid_prop] supplies it from [RMod_LocallyPropositional]
 with nothing to prove; no statement in this file gained a
 hypothesis.)
 The working form the [Deloop] spine consumes is
 [MonHom (grp_mon G) (hom_monoid (RMod K) V)], an action by bare
 endomorphisms, and the two are interchangeable:

 - [monhom_of_rep] forgets the invertibility witness, its
 [mon_map] being [rep_act] — the FIRST projection of the unit
 datum, so no proof is discarded, only ignored;
 - [rep_of_monhom] supplies it, the inverse of the action of g
 being the action of g⁻¹, by the group laws pushed through the
 homomorphism (this is the automatic-invertibility pattern of
 Construction/Deloop/Functors.v's
 [perm_rep_acts_by_bijections], reached here through
 [UnitsOf] rather than through [fobj_iso]).

 BOTH ROUND TRIPS ARE DEFINITIONAL: [monhom_rep_round] and
 [rep_monhom_round] are [reflexivity], because [UnitsOf]'s
 hom-setoid compares unit data by the underlying element and
 [rep_act] is exactly that projection.  So the choice of primitive
 is one of statement fidelity only, and the equivalence below is
 proved in whichever form is convenient at each step.

 3. NOTHING BELOW USES COMMUTATIVITY OF K.  Mac Lane says commutative
 ring; the parameter here is [RingObject] — defined in
 Theory/Algebra/Rig.v and the object type of Instance/Rng.v's
 [Rng] — because no step consumes commutativity (structurally so:
 the record has no commutativity field) — [RMod K] is a category
 for any
 ring, and every argument is about the endomorphism monoid of one
 of its objects.  Specializing to a commutative K (or to a field,
 once issue #244 supplies one) is instantiation, not a change of
 statement.

 4. THE DEGENERACY IS PROVED IN ITS GENERAL FORM.  Awodey's remark is
 about groups and posets, but neither hypothesis is used: in a thin
 category ANY functor carries ANY endomorphism to an identity
 ([thin_functor_endo_trivial]), since [fmap] of it is parallel to
 [id].  The group statement and the [Proset] instantiation are
 the SAME statement at two instantiations, not further theorems —
 and at [Proset] the conclusion degenerates outright: [Proset]'s
 hom-≈ is the trivial relation ([proset_thin]'s proof is [exact
 I]), so [proset_group_functor_trivial]'s conclusion is inhabited
 by [I] and carries typing content only (the Instance/Proset/
 Limit.v degeneration, disclosed there too).  The instantiation
 is stated at [Proset], not at posets: Instance/Poset.v's [Poset]
 is DEFINED as [Proset P] and discards antisymmetry (the erratum
 recorded in Instance/Proset/Galois.v) — and the coverage is not
 thereby narrowed, since Instance/Pos.v's genuine category of
 posets enters through [PosetAsCategory P := Proset
 (pos_preorder P)], so the corollary covers real posets as well;
 [proset_thin] is the honest donor and is cited, not re-proved.

 5. WHAT IS NOT BUILT.  No category of representations over varying
 K or varying G, and no character theory.  The matrix-valued
 cousin of [RepObject] is Construction/Deloop/Functors.v's
 [MatrixRep] (a dimension plus a homomorphism into the matrix
 monoid, the same spine at [Matr R]); the finite-dimensional
 vector-space reading belongs with issue #237's [FdVect] and is
 deferred to it.  Instance/Fun/Action.v's [MSet_hom_iso] — the
 transformation setoid presented literally as the setoid of
 equivariant maps — has no counterpart here; the hom-level content
 is already carried by [Rep_Fun_equiv]. 

 --------
 书籍：      Mac Lane，《为在职数学家准备的范畴论》，第2版，§II.4，印刷页41（PDF 51）——
 maclane:II.4:construction3
 书籍：      Awodey，《范畴论》，第2版，§7.1，印刷页153——
 awodey:7.1:construction-linear-representation
 nLab：       https://ncatlab.org/nlab/show/representation
 nLab：       https://ncatlab.org/nlab/show/group+representation
 维基百科：  https://en.wikipedia.org/wiki/Group_representation麦克·莱恩在 §II.4 中的第三种构造：对于一个交换环 K 和一个群 G，G 的 K 线性表示是一个 K-模 V，外加一个从 G 到 V 自同构群的同态映射，两个这样的表示之间的缠结映射是一个模映射，它与两个作用交换，由此得到的范畴是函子范畴 [B G, K-Mod]。阿沃迪在 §7.1 中给出了相同的识别，并立即得出退化的结果：从一个群到一个偏序集的函子将每个元素映射为恒等映射，因此在序中没有有趣的群表示。该文件是 Instance/Fun/Action.v 的结构双胞胎，位于下一扇门的文件夹里。那个文件是 Mac Lane 的构造 2 — 在集合上的作用，M-作用和等变映射的范畴 [MSet M]，以及等价 [MSet_Fun_equiv : [Deloop M, Sets] ≅ [Cat] MSet M]。这里 [Sets] 被 [RMod K] 替代，“函数作用”被替换为“模自同构作用”；其架构，包括在一个对象上的自然性如何归结为一个交换方形，以及函子端的往返如何通过一个透明的组件族重建，都是那个文件的内容，并且是遵循而非重新发明的。- [grp_mon]：群对象所依赖的幺半群，一个转换器，使 Instance/Grp.v 的 [GrpObject] 能够进行退环处理  
 - [RepObject K G]：带有从 G 到其自同态幺半群单位的同态的 K-模——问题-字面上的自同构形式  
 - [rep_act], [rep_act_unit], [rep_act_mul], [rep_act_iso]：从该同态中读取的作用、它的两个律，以及每个元素作为 [RMod K] 的同构进行作用  
 - [monhom_of_rep] / [rep_of_monhom]：在自同构值和自同态值（工作）形式之间的转换，两次回转都是定义性的  
 - [Intertwiner], [Rep K G]：与作用交换的模映射，以及它们形成的范畴  
 - [Rep_Fun_equiv]：标题—— [[Deloop (grp_mon G), RMod K] ≅ [Cat] Rep K G  
 - [thin_functor_endo_trivial], [thin_group_functor_trivial], [proset_group_functor_trivial]：Awodey 的堕落
 - [trivial_rep]，[sign_rep]：两位见证人设计：1. 两个 [GrpObject] 记录。该树包含两个同名记录。Construction/Deloop.v 的 v 扩展了 [MonObject]，通过一个双边逆，它是 [Deloop] 和 Structure/Groupoid.v 的 [MonHom] 机制所使用的；Instance/Grp.v 的是官方范畴 [Grp]（承载集合、单位、乘法、逆运算，仅将左单位和逆律作为字段）的对象，并且是 Instance/Matr/GL.v 的 [UnitsOf] 所产生的。由于表示的字面语句命名了自同构群——即 [UnitsOf]——这里的原始对象是 Instance/Grp.v 的记录，最后导入，以便裸名称 [GrpObject]、[grp_inv]、[grp_mul]、[grp_unit] 全部引用它。[grp_mon] 是将其转换为 [MonObject] 的单行转换器：运算元、单位和乘法保持不变，结合性翻转（Deloop 的 [mon_op_assoc] 在 [comp_assoc] 的方向中陈述），且右单位律取自 Instance/Grp.v 中推导出的 [grp_mul_unit_r]。因此去环总是 [Deloop (grp_mon G)]。2. 自同构形式是原始的，并且通路不花费任何东西。[RepObject] 携带 [rep_hom : GrpHom G (UnitsOf (hom_monoid (RMod K) rep_mod) (rmod_hom_monoid_prop K rep_mod))]——字面意思是“从 G 到 V 的自同构的同态”。（这行的早期版本省略了 [UnitsOf] 的第二个参数。由于 PR “代数载体是集合”（2026-09-17）[UnitsOf] 向幺半群的载体集合请求 [Prop] 等式，并且 [rmod_hom_monoid_prop] 从 [RMod_LocallyPropositional] 提供它而无需证明；此文件中的任何语句都没有增加假设。）[Deloop] 主脊使用的工作形式是 [MonHom (grp_mon G) (hom_monoid (RMod K) V)]，即由裸端同态的作用，并且两者可以互换：- [monhom_of_rep] 忘记了可逆性证明，其 [mon_map] 是 [rep_act] ——单位元的第一个投影，因此没有证明被丢弃，仅仅是被忽略；
 - [rep_of_monhom] 提供了它，g 的作用的逆就是 g⁻¹ 的作用，通过群同态法则传递（这是 Construction/Deloop/Functors.v 中 [perm_rep_acts_by_bijections] 的自动可逆性模式，这里通过 [UnitsOf] 而不是 [fobj_iso] 达到）。两个往返转换都是定义性的：[monhom_rep_round] 和 [rep_monhom_round] 都是 [reflexivity]，因为 [UnitsOf] 的同构集合通过底层元素比较单位数据，而 [rep_act] 正是那个投影。因此，原始选择只涉及陈述的准确性，下面的等价性可以在每一步以方便的形式证明。3. 以下内容均未使用 K 的交换性。Mac Lane 说到交换环；这里的参数是 [RingObject] — 定义在 Theory/Algebra/Rig.v 中，以及 Instance/Rng.v 的 [Rng] 的对象类型 — 因为没有步骤消耗交换性（结构上如此：记录中没有交换性字段）— [RMod K] 是任何环的一个范畴，并且每个论点都关于其某个对象的自同态幺半群。专门化到交换的 K（或者当问题 #244 提供一个域时），只是实例化，而不是改变陈述。4. 这种退化在其一般形式中得到了证明。Awodey 的评论是关于群和偏序集的，但并没有使用这些假设：在一个稀疏范畴中，任何函子都将任何自同态映射为恒等态（[thin_functor_endo_trivial]），因为它的 [fmap] 与 [id] 平行。群的陈述和 [Proset] 的实例化是在两个实例上的相同陈述，而不是进一步的定理——并且在 [Proset] 上结论完全退化：[Proset] 的 hom-≈ 是平凡关系（[proset_thin] 的证明是[精确 I]），所以 [proset_group_functor_trivial] 的结论由 [I] 占据，并且仅承载类型内容（Instance/Proset/Limit.v 的退化，在那里也被揭示）。实例化是在 [Proset] 处陈述的，而不是在 posets: Instance/Poset.v 的 [Poset] 处定义的；[Poset] 被定义为 [Proset P]，并且放弃了反对称性（该勘误记录在 Instance/Proset/Galois.v 中）——并且因此覆盖范围并未缩小，因为 Instance/Pos.v 的真正的偏序集合类别是通过 [PosetAsCategory P := Proset (pos_preorder P)] 引入的，因此推论也涵盖了真实的偏序集合；[proset_thin] 是可靠的提供者并被引用，而不是重新证明。5. 尚未构建的部分。没有关于变化的 K 或变化的 G 的表示类别，也没有特征理论。[RepObject] 的矩阵值对应物是 Construction/Deloop/Functors.v 中的 [MatrixRep]（一个维度加上到矩阵半群的同态，在 [Matr R] 处具有相同的主干）；有限维向量空间的解读属于 #237 问题的 [FdVect]，并被推迟到该问题。Instance/Fun/Action.v 中的 [MSet_hom_iso] —— 以等变映射的集合体字面呈现的变换集合体 —— 在这里没有对应物；同层内容已经由 [Rep_Fun_equiv] 承载。
*)

(* * ** From a group object to a monoid object / * ** 从群对象到幺半群对象 *)

(*
 Instance/Grp.v's [GrpObject] read as a [MonObject], so that it can be
 delooped.  Carrier, unit and multiplication are the originals; only
 two law fields need any work, and neither is a proof:
 [mon_op_assoc] is stated in the mirrored orientation (Deloop.v
 matches [comp_assoc], Instance/Grp.v matches the usual left-to-right
 reading), and [mon_op_unit_r] is Instance/Grp.v's derived
 [grp_mul_unit_r] rather than a field. 

 --------
 Instance/Grp.v 的 [GrpObject] 被读作 [MonObject]，以便可以去环。载体、单元和乘法都是原本的；只有两个定律域需要处理，并且都不是证明：[mon_op_assoc] 被声明为镜像方向（Deloop.v 与 [comp_assoc] 匹配，Instance/Grp.v 与通常的从左到右阅读匹配），并且 [mon_op_unit_r] 是 Instance/Grp.v 的派生 [grp_mul_unit_r] 而不是一个域。
*)
Program Definition grp_mon (G : GrpObject) : MonObject := {|
  mon_setoid := grp_setoid G;
  mon_unit   := grp_unit G;
  mon_op     := grp_mul G;

  mon_op_respects := grp_mul_respects G
|}.
Next Obligation.
  intros G a b c; symmetry; apply grp_mul_assoc.
Qed.
Next Obligation.
  intros G a; apply grp_mul_unit_l.
Qed.
Next Obligation.
  intros G a; apply grp_mul_unit_r.
Qed.

(* The three data fields are the originals, on the nose. / 这三个数据字段是原件，正中目标。 *)
Example grp_mon_carrier (G : GrpObject) :
  carrier (grp_mon G) = carrier (grp_setoid G) := eq_refl.

Example grp_mon_unit (G : GrpObject) :
  @mon_unit (grp_mon G) = grp_unit G := eq_refl.

Example grp_mon_op (G : GrpObject) :
  @mon_op (grp_mon G) = grp_mul G := eq_refl.

(*
 [UnitsOf]'s hom-setoid compares unit data by the underlying element
 alone, so an equation between units is an equation between the
 elements they are built on — the invertibility witnesses are free to
 differ.  Stating that once, as a conversion, keeps every obligation
 below at the level of morphisms of [RMod K]; without it a bare
 [reflexivity] would try to unify the witnesses too. 

 --------
 [UnitsOf] 的同态集（hom-setoid）仅通过底层元素比较单位数据，因此单位之间的方程就是它们所构建元素之间的方程——可逆性证明可以自由不同。作为一次转换来声明它，可以保持下面每个义务在 [RMod K] 的态射层级；没有它，一个单独的 [reflexivity] 也会尝试统一证明。
*)
(*
 Since the PR "algebraic carriers are sets" (2026-09-17) [UnitsOf] also
 takes the monoid carrier's [PropEquiv]; the statement is otherwise
 unchanged, and every use below supplies [rmod_hom_monoid_prop]. 

 --------
 由于 PR “代数载体是集合”（2026-09-17）[UnitsOf] 还使用了幺半群载体的 [PropEquiv]；陈述没有其他更改，下方的每个使用都提供了 [rmod_hom_monoid_prop]。
*)
Lemma units_equiv {M : MonObject}
  {PM : PropEquiv (is_setoid (mon_setoid M))}
  (x y : carrier (grp_setoid (UnitsOf M PM))) : `1 x ≈ `1 y → x ≈ y.
Proof. intro H; exact H. Qed.

(*
 The witness [UnitsOf] asks for at an endomorphism monoid of [RMod K]:
 [RMod K] is locally propositional (Instance/Mod.v), so the hom-setoid
 carries the [PropEquiv] with nothing further to prove. 

 --------
 证人 [UnitsOf] 请求在 [RMod K] 的一个自同态幺半群上：[RMod K] 是局部命题的（Instance/Mod.v），所以同态集族携带 [PropEquiv]，无需进一步证明。
*)
Definition rmod_hom_monoid_prop (K : RingObject) (V : RModObject K) :
  PropEquiv (is_setoid (mon_setoid (hom_monoid (RMod K) V))) :=
  @locally_prop (RMod K) (RMod_LocallyPropositional K) V V.

(** ** Representations / ** 表示 *)

(*
 A K-linear representation of G: a K-module together with a
 homomorphism from G into the group of automorphisms of that module.
 The automorphism group is Instance/Matr/GL.v's [UnitsOf] taken at
 Construction/Deloop.v's endomorphism monoid [hom_monoid (RMod K) V]
 — the same composite that reads GL_n off the matrix monoid there. 

 --------
 G 的 K 线性表示：一个 K 模，同时有一个从 G 到该模的自同构群的同态。自同构群是 Instance/Matr/GL.v 中的 [UnitsOf]，在 Construction/Deloop.v 的自同态幺半群 [hom_monoid (RMod K) V] 上取的——与从矩阵幺半群中读取 GL_n 的复合方式相同。
*)
Record RepObject (K : RingObject) (G : GrpObject) := {
  rep_mod :> RModObject K;

  rep_hom : GrpHom G (UnitsOf (hom_monoid (RMod K) rep_mod) (rmod_hom_monoid_prop K rep_mod))
}.

Arguments rep_mod {K G} _.
Arguments rep_hom {K G} _.

(*
 The action of a group element, as an endomorphism of the module: the
 underlying element of the unit datum.  Every law below is the
 corresponding homomorphism law read through this projection, which is
 why each of them holds by [exact] with no rewriting. 

 --------
 一个群元素的作用，作为模的一个自同态：单位数据的基础元素。下面的每一条定律都是通过这个投影读取的相应同态定律，这就是为什么每一条定律都可以通过 [exact] 成立而无需重写。
*)
Definition rep_act {K : RingObject} {G : GrpObject} (V : RepObject K G)
  (g : carrier G) : rep_mod V ~{RMod K}~> rep_mod V :=
  `1 (grp_map (rep_hom V) g).

Lemma rep_act_respects {K : RingObject} {G : GrpObject}
  (V : RepObject K G) : Proper (equiv ==> equiv) (rep_act V).
Proof.
  intros g h Hgh.
  exact (proper_morphism (grp_map (rep_hom V)) g h Hgh).
Qed.

Lemma rep_act_unit {K : RingObject} {G : GrpObject} (V : RepObject K G) :
  rep_act V (grp_unit G) ≈ id.
Proof. exact (grp_map_unit (rep_hom V)). Qed.

Lemma rep_act_mul {K : RingObject} {G : GrpObject} (V : RepObject K G)
  (g h : carrier G) :
  rep_act V (grp_mul G g h) ≈ rep_act V g ∘ rep_act V h.
Proof. exact (grp_map_mul (rep_hom V) g h). Qed.

(*
 Each element acts invertibly, the inverse being the action of the
 inverse element.  This is a consequence of the two laws above, not a
 reading of the unit datum's own witness: the witness stored in
 [rep_hom] is some two-sided inverse, and what is proved here is that
 [rep_act V (grp_inv G g)] is one. 

 --------
 每个元素都是可逆的，其逆元素的作用就是它的逆。这是上述两个定律的结果，而不是对单位数据自身见证的解读：存储在 [rep_hom] 中的见证是某个双边逆，而这里所证明的是 [rep_act V (grp_inv G g)] 是一元的。
*)
Program Definition rep_act_iso {K : RingObject} {G : GrpObject}
  (V : RepObject K G) (g : carrier G) :
  rep_mod V ≅[RMod K] rep_mod V := {|
  to   := rep_act V g;
  from := rep_act V (grp_inv G g)
|}.
Next Obligation.
  intros K G V g.
  transitivity (rep_act V (grp_unit G)).
  - rewrite <- rep_act_mul.
    apply rep_act_respects.
    apply grp_mul_inv_r.
  - apply rep_act_unit.
Qed.
Next Obligation.
  intros K G V g.
  transitivity (rep_act V (grp_unit G)).
  - rewrite <- rep_act_mul.
    apply rep_act_respects.
    apply grp_mul_inv_l.
  - apply rep_act_unit.
Qed.

(* * ** The two forms of the action datum / * ** 行动数据的两种形式 *)

(*
 Forgetting the invertibility witness: the working form the [Deloop]
 spine consumes.  Its [mon_map] IS [rep_act]. 

 --------
 遗忘可逆性证明：[Deloop] 脊柱消耗的工作形式。它的 [mon_map] 是 [rep_act]。
*)
Program Definition monhom_of_rep {K : RingObject} {G : GrpObject}
  (V : RepObject K G) :
  MonHom (grp_mon G) (hom_monoid (RMod K) (rep_mod V)) := {|
  mon_map := rep_act V
|}.
Next Obligation. intros K G V; exact (rep_act_respects V). Qed.
Next Obligation. intros K G V; exact (rep_act_unit V). Qed.
Next Obligation. intros K G V a b; exact (rep_act_mul V a b). Qed.

(*
 Supplying it back: over a GROUP the invertibility is automatic, the
 inverse of the action of g being the action of g⁻¹.  The two
 obligations are the group's own inverse laws pushed through the
 homomorphism. 

 --------
 返回提供它：在一个群上，可逆性是自动的，g 的作用的逆就是 g⁻¹ 的作用。这两个要求就是群自身的逆元定律通过同态映射传递过来的。
*)
Program Definition rep_of_monhom {K : RingObject} {G : GrpObject}
  (V : RModObject K) (h : MonHom (grp_mon G) (hom_monoid (RMod K) V)) :
  GrpHom G (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V)) := {|
  grp_map := {| morphism := fun g : carrier G =>
    (mon_map h g; (mon_map h (grp_inv G g); (_, _))) |}
|}.
Next Obligation.
  intros K G V h g.
  transitivity (mon_map h (grp_unit G)).
  - rewrite <- (mon_map_op h g (grp_inv G g)).
    apply (mon_map_respects h).
    apply grp_mul_inv_r.
  - apply (mon_map_unit h).
Qed.
Next Obligation.
  intros K G V h g.
  transitivity (mon_map h (grp_unit G)).
  - rewrite <- (mon_map_op h (grp_inv G g) g).
    apply (mon_map_respects h).
    apply grp_mul_inv_l.
  - apply (mon_map_unit h).
Qed.
Next Obligation.
  intros K G V h g g' Hgg'.
  exact (mon_map_respects h g g' Hgg').
Qed.
Next Obligation.
  intros K G V h; exact (mon_map_unit h).
Qed.
Next Obligation.
  intros K G V h a b; exact (mon_map_op h a b).
Qed.

(* The packaged representation. / 打包表示。 *)
Definition RepOfMonHom {K : RingObject} {G : GrpObject}
  (V : RModObject K) (h : MonHom (grp_mon G) (hom_monoid (RMod K) V)) :
  RepObject K G :=
  {| rep_mod := V; rep_hom := rep_of_monhom V h |}.

(*
 Both round trips are DEFINITIONAL.  Going out and back through the
 invertibility witness recovers the same map because [UnitsOf]'s
 hom-setoid compares unit data by the underlying element, which is
 precisely what [rep_act] projects. 

 --------
 两次往返都是定义性的。通过可逆性证据的出发和回返恢复相同的映射，因为 [UnitsOf] 的同类集通过底层元素比较单位数据，这正是 [rep_act] 投影的内容。
*)
Lemma monhom_rep_round {K : RingObject} {G : GrpObject}
  (V : RModObject K) (h : MonHom (grp_mon G) (hom_monoid (RMod K) V))
  (g : carrier G) :
  mon_map (monhom_of_rep (RepOfMonHom V h)) g ≈ mon_map h g.
Proof. reflexivity. Qed.

Lemma rep_monhom_round {K : RingObject} {G : GrpObject}
  (V : RepObject K G) (g : carrier G) :
  rep_act (RepOfMonHom (rep_mod V) (monhom_of_rep V)) g ≈ rep_act V g.
Proof. reflexivity. Qed.

(*
 Stated on the unit datum itself, which is the same equation: the
 round trip is written through [rep_act] because [UnitsOf]'s
 hom-setoid equivalence is that projection, and a bare [reflexivity]
 at the sigma type would have to unify the invertibility witnesses,
 which the two forms are under no obligation to share. 

 --------
 在单元数据自身上陈述，它是相同的方程：往返通过 [rep_act] 表示，因为 [UnitsOf] 的同态集合等价是那个投影，而在西格玛类型上的一个裸 [reflexivity] 必须统一可逆性证人，而这两种形式没有义务共享这些证人。
*)
Lemma rep_monhom_round_elt {K : RingObject} {G : GrpObject}
  (V : RepObject K G) (g : carrier G) :
  `1 (grp_map (rep_of_monhom (rep_mod V) (monhom_of_rep V)) g)
    ≈ `1 (grp_map (rep_hom V) g).
Proof. reflexivity. Qed.

(** ** Intertwiners / ** 交织器 *)

(*
 A morphism of representations: a module map commuting with the two
 actions.  The composition is spelled at [RMod K], the actions being
 endomorphisms of the underlying modules. 

 --------
 表示的态射：一个与两个作用相交换的模映射。组合记作 [RMod K]，作用是底层模的自同态。
*)
Record Intertwiner {K : RingObject} {G : GrpObject}
       (V W : RepObject K G) := {
  itw_map :> rep_mod V ~{RMod K}~> rep_mod W;

  itw_equivar : ∀ g : carrier G,
    itw_map ∘ rep_act V g ≈ rep_act W g ∘ itw_map
}.

Arguments itw_map {K G V W} _.
Arguments itw_equivar {K G V W} _ _.

(* * ** The category of representations / * ** 表示的类别 *)

Program Definition Rep (K : RingObject) (G : GrpObject) : Category := {|
  obj := RepObject K G;
  hom := fun V W => Intertwiner V W;
  homset := fun V W =>
    {| equiv := fun f g => itw_map f ≈ itw_map g |};
  id := fun V => {| itw_map := id |};
  compose := fun U V W f g => {| itw_map := itw_map f ∘ itw_map g |}
|}.
Next Obligation.
  intros K G V W; constructor.
  - intros f; reflexivity.
  - intros f g Hfg; symmetry; exact Hfg.
  - intros f g h H1 H2; transitivity (itw_map g); assumption.
Qed.
Next Obligation.
  intros K G V g.
  rewrite id_left, id_right; reflexivity.
Qed.
Next Obligation.
  intros K G U V W f g gr.
  rewrite <- comp_assoc.
  rewrite (itw_equivar g gr).
  rewrite comp_assoc.
  rewrite (itw_equivar f gr).
  rewrite <- comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  intros K G U V W f f' Hf g g' Hg.
  exact (@compose_respects (RMod K) (rep_mod U) (rep_mod V) (rep_mod W)
           _ _ Hf _ _ Hg).
Qed.
Next Obligation. intros K G V W f; exact (id_left (itw_map f)). Qed.
Next Obligation. intros K G V W f; exact (id_right (itw_map f)). Qed.
Next Obligation.
  intros K G U V W X f g h.
  exact (comp_assoc (itw_map f) (itw_map g) (itw_map h)).
Qed.
Next Obligation.
  intros K G U V W X f g h.
  exact (comp_assoc_sym (itw_map f) (itw_map g) (itw_map h)).
Qed.

(** ** The comparison functors / ** 比较函数对象 *)

(*
 A functor out of the delooping IS a representation: its value at the
 single object is the module, and its action on arrows is the spine
 homomorphism, made invertible by [rep_of_monhom]. 

 --------
 来自去环化的函子是一个表示：它在单个对象上的值是模，且它对箭头的作用是脊同态，由 [rep_of_monhom] 使其可逆。
*)
Definition rep_of_functor {K : RingObject} {G : GrpObject}
  (F : Deloop (grp_mon G) ⟶ RMod K) : RepObject K G :=
  RepOfMonHom (G := G) (F ttt : RModObject K)
    (hom_monoid_of_functor (C := RMod K) F).

(* ...and conversely, through Construction/Deloop/Functors.v's spine. / ...相反，通过 Construction/Deloop/Functors.v 的主干。 *)
Definition functor_of_rep {K : RingObject} {G : GrpObject}
  (V : RepObject K G) : Deloop (grp_mon G) ⟶ RMod K :=
  functor_of_hom_monoid (C := RMod K) (rep_mod V) (monhom_of_rep V).

(*
 The action of the representation read off a functor is that functor's
 [fmap], definitionally — the fact every obligation below leans on. 

 --------
 从函子读出的表示的作用是该函子的 [fmap]，本质上——每个下面的义务都依赖于这一点。
*)
Lemma rep_of_functor_act {K : RingObject} {G : GrpObject}
  (F : Deloop (grp_mon G) ⟶ RMod K) (g : carrier G) :
  rep_act (rep_of_functor F) g ≈ fmap[F] g.
Proof. reflexivity. Qed.

Lemma functor_of_rep_fmap {K : RingObject} {G : GrpObject}
  (V : RepObject K G) (g : carrier G) :
  @fmap _ _ (functor_of_rep V) ttt ttt g ≈ rep_act V g.
Proof. reflexivity. Qed.

(*
 Reading a representation and its intertwiners off a functor: the
 morphism action takes a transformation to its single component,
 whose naturality at g IS the intertwining square. 

 --------
 从函子读出一个表示及其交织子：态射作用将一个变换取到它的单个分量，其在 g 处的自然性就是交织方格。
*)
Program Definition Rep_to (K : RingObject) (G : GrpObject) :
  [Deloop (grp_mon G), RMod K] ⟶ Rep K G := {|
  fobj := fun F => rep_of_functor F;
  fmap := fun F F' η => {| itw_map := transform[η] ttt |}
|}.
Next Obligation.
  intros K G F F' η g.
  exact (@naturality_sym _ _ F F' η ttt ttt g).
Qed.
Next Obligation.
  intros K G F F' η θ Hηθ; exact (Hηθ ttt).
Qed.
Next Obligation.
  intros K G F; exact (@fmap_id _ _ F ttt).
Qed.
Next Obligation.
  intros K G F F' F'' η θ; simpl; reflexivity.
Qed.

(*
 Materializing an intertwiner as the constant transformation family;
 naturality is the intertwining square. 

 --------
 将一个交织器具体化为常数变换族；自然性就是交织方形。
*)
Program Definition Rep_from (K : RingObject) (G : GrpObject) :
  Rep K G ⟶ [Deloop (grp_mon G), RMod K] := {|
  fobj := fun V => functor_of_rep V;
  fmap := fun V W h => {| transform := fun _ => itw_map h |}
|}.
Next Obligation.
  intros K G V W h [] [] g.
  symmetry; exact (itw_equivar h g).
Qed.
Next Obligation.
  intros K G V W h [] [] g.
  exact (itw_equivar h g).
Qed.
Next Obligation.
  intros K G V W h h' Hh []; exact Hh.
Qed.
Next Obligation.
  intros K G V [].
  symmetry; exact (rep_act_unit V).
Qed.
Next Obligation.
  intros K G U V W f g []; simpl; reflexivity.
Qed.

(** ** The equivalence / ** 等价 *)

(*
 The representation-side round trip: the two representations have the
 same module and the same action, so the identity module map is an
 intertwiner in both directions. 

 --------
 表示侧的往返：这两个表示具有相同的模和相同的作用，因此恒等模映射在两个方向上都是一个交织算子。
*)
Program Definition Rep_action_round_iso {K : RingObject} {G : GrpObject}
  (V : RepObject K G) :
  @Isomorphism (Rep K G) (rep_of_functor (functor_of_rep V)) V := {|
  to   := {| itw_map := id |};
  from := {| itw_map := id |}
|}.
Next Obligation.
  intros K G V g; rewrite id_left, id_right; reflexivity.
Qed.
Next Obligation.
  intros K G V g; rewrite id_left, id_right; reflexivity.
Qed.
Next Obligation. intros K G V; exact (id_left (@id (RMod K) _)). Qed.
Next Obligation. intros K G V; exact (id_left (@id (RMod K) _)). Qed.

(*
 The functor-side round trip, with a transparent component family: the
 equivalence below has to compute with the components, so the
 in-tree opaque [functor_round] cannot serve (Instance/Fun/Action.v's
 [MSet_round_iso] makes the same move). 

 --------
 函子端的往返，带有透明的组件族：下面的等价必须与组件一起计算，所以树内的不透明 [functor_round] 无法使用（Instance/Fun/Action.v 的 [MSet_round_iso] 做了相同的操作）。
*)
Program Definition Rep_round_iso {K : RingObject} {G : GrpObject}
  (F : Deloop (grp_mon G) ⟶ RMod K) :
  @Isomorphism ([Deloop (grp_mon G), RMod K])
    (functor_of_rep (rep_of_functor F)) F := {|
  to   := {| transform := fun x =>
    match x return
      (functor_of_rep (rep_of_functor F) x ~{RMod K}~> F x)
    with ttt => id end |};
  from := {| transform := fun x =>
    match x return
      (F x ~{RMod K}~> functor_of_rep (rep_of_functor F) x)
    with ttt => id end |}
|}.
Next Obligation.
  intros K G F [] [] g.
  transitivity (@fmap _ _ F ttt ttt g).
  - exact (id_right (@fmap _ _ F ttt ttt g)).
  - symmetry; exact (id_left (@fmap _ _ F ttt ttt g)).
Qed.
Next Obligation.
  intros K G F [] [] g.
  transitivity (@fmap _ _ F ttt ttt g).
  - exact (id_right (@fmap _ _ F ttt ttt g)).
  - symmetry; exact (id_left (@fmap _ _ F ttt ttt g)).
Qed.
Next Obligation.
  intros K G F [] [] g.
  transitivity (@fmap _ _ F ttt ttt g).
  - exact (id_right (@fmap _ _ F ttt ttt g)).
  - symmetry; exact (id_left (@fmap _ _ F ttt ttt g)).
Qed.
Next Obligation.
  intros K G F [] [] g.
  transitivity (@fmap _ _ F ttt ttt g).
  - exact (id_right (@fmap _ _ F ttt ttt g)).
  - symmetry; exact (id_left (@fmap _ _ F ttt ttt g)).
Qed.
Next Obligation.
  intros K G F [].
  transitivity (@id (RMod K) (F ttt)).
  - exact (id_left (@id (RMod K) (F ttt))).
  - symmetry; apply fmap_id.
Qed.
Next Obligation.
  intros K G F [].
  transitivity (@id (RMod K) (F ttt)).
  - exact (id_left (@id (RMod K) (F ttt))).
  - symmetry.
    exact (@fmap_id _ _ (functor_of_rep (rep_of_functor F)) ttt).
Qed.

(*
 Mac Lane's construction 3 at category strength: the category of
 K-linear representations of G IS the functor category out of the
 delooping of G, an isomorphism in Cat and hence — Cat's hom-setoid
 being natural isomorphism (Instance/Cat.v) — an EQUIVALENCE of
 categories.  The orientation is Instance/Fun/Action.v's, with the
 functor category on the left. 

 --------
 Mac Lane 在范畴强度下的构造 3：G 的 K 线性表示的范畴就是从 G 的去环绕（delooping）出发的函子范畴，这是 Cat 中的一个同构，因此——由于 Cat 的同集合是自然同构（Instance/Cat.v）——这是范畴的一个等价。方向是 Instance/Fun/Action.v 的方向，函子范畴在左边。
*)
Program Definition Rep_Fun_equiv (K : RingObject) (G : GrpObject) :
  [Deloop (grp_mon G), RMod K] ≅[Cat] Rep K G := {|
  to   := Rep_to K G;
  from := Rep_from K G
|}.
Next Obligation.
  (* Rep_to ◯ Rep_from ≈ Id, through the representation-side round trip / Rep_to ◯ Rep_from ≈ Id，通过表示端的往返 *)
  intros K G.
  exists (fun V => Rep_action_round_iso V).
  intros V W h a; simpl; reflexivity.
Qed.
Next Obligation.
  (* Rep_from ◯ Rep_to ≈ Id, through the transparent functor-side one / 通过透明函子一侧，Rep_from ◯ Rep_to ≈ Id *)
  intros K G.
  exists (fun F => Rep_round_iso F).
  intros F F' η [] a; simpl; reflexivity.
Qed.

(** ** Awodey's degeneracy / ** 阿沃迪的堕落 *)

(*
 In a thin category any functor carries any ENDOmorphism to an
 identity: its image is parallel to [id], and thinness identifies
 parallel morphisms.  Neither the group hypothesis nor the one-object
 hypothesis plays any part. 

 --------
 在一个稀薄范畴中，任何函子都会将任何自同态映射为一个恒等态：它的像与 [id] 平行，而稀薄性会识别平行的态射。无论群假设还是单对象假设都不起作用。
*)
Lemma thin_functor_endo_trivial {B C : Category} (T : Thin C)
  (F : B ⟶ C) {x : B} (f : x ~> x) : fmap[F] f ≈ id.
Proof. exact (T (F x) (F x) (fmap[F] f) id). Qed.

(*
 Awodey's statement: a representation of a group in a thin category
 is trivial — every group element acts as the identity. 

 --------
 Awodey 的陈述：在薄范畴中群的一个表示是平凡的——每个群元素都作用为恒等映射。
*)
Theorem thin_group_functor_trivial {G : GrpObject} {C : Category}
  (T : Thin C) (F : Deloop (grp_mon G) ⟶ C) (g : carrier G) :
  @fmap _ _ F ttt ttt g ≈ id.
Proof. exact (thin_functor_endo_trivial T F g). Qed.

(*
 Instantiated at a preorder.  The statement is about [Proset], not
 about posets: Instance/Poset.v's [Poset] is DEFINED as [Proset P] and
 drops antisymmetry, so nothing here would be strengthened by naming
 it.  [proset_thin] is Instance/Proset/Order.v's, cited. 

 --------
 在一个预序下实例化。该陈述关于 [Proset]，而不是关于偏序集：Instance/Poset.v 的 [Poset] 被定义为 [Proset P]，并且放弃了反对称性，因此通过命名它这里不会有任何加强作用。[proset_thin] 是 Instance/Proset/Order.v 的，被引用。
*)
Corollary proset_group_functor_trivial {G : GrpObject} {A : Type}
  {R : relation A} (P : RelationClasses.PreOrder R)
  (F : Deloop (grp_mon G) ⟶ Proset P) (g : carrier G) :
  @fmap _ _ F ttt ttt g ≈ id.
Proof. exact (thin_group_functor_trivial (proset_thin P) F g). Qed.

(** ** Witnesses / ** 证人 *)

(*
 Double negation in an abelian group, the one fact Instance/Ab.v
 leaves unstated among its negation lemmas. 

 --------
 阿贝尔群中的双重否定，在其否定引理中留下未说明的一个事实 Instance/Ab.v。
*)
Lemma ab_neg_neg (A : AbObject) (a : carrier (cmon_setoid A)) :
  ab_neg A (ab_neg A a) ≈ a.
Proof. symmetry; apply ab_neg_unique; apply ab_neg_right. Qed.

(*
 The trivial representation of any group on any module: every element
 acts as the identity.  Available at every K and G, so [RepObject] is
 never empty. 

 --------
 任意群在任意模上的平凡表示：每个元素都作为恒等映射作用。在每个 K 和 G 上都可用，所以 [RepObject] 从不为空。
*)
Program Definition rep_id_unit {K : RingObject} (V : RModObject K) :
  carrier (grp_setoid (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V))) :=
  (id; (id; (_, _))).
Next Obligation. intros K V; exact (id_left (@id (RMod K) V)). Qed.
Next Obligation. intros K V; exact (id_left (@id (RMod K) V)). Qed.

Lemma rep_id_unit_respects {K : RingObject} {G : GrpObject}
  (V : RModObject K) :
  Proper (equiv ==> equiv) (fun _ : carrier G => rep_id_unit V).
Proof. intros g g' Hgg'; apply units_equiv; reflexivity. Qed.

Lemma rep_id_unit_is_unit {K : RingObject} (V : RModObject K) :
  rep_id_unit V ≈ grp_unit (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V)).
Proof. apply units_equiv; reflexivity. Qed.

Lemma rep_id_unit_mul {K : RingObject} (V : RModObject K) :
  rep_id_unit V
    ≈ grp_mul (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V))
        (rep_id_unit V) (rep_id_unit V).
Proof.
  apply units_equiv; symmetry; exact (id_left (@id (RMod K) V)).
Qed.

(*
 Spelled as a term for the reason given at [rmod_neg_hom]: the
 obligation numbering is not the field numbering, and every field
 here is already a lemma. 

 --------
 在 [rmod_neg_hom] 上作为给出的原因拼写：义务编号不是字段编号，这里的每个字段已经是一个词条。
*)
Definition trivial_rep {K : RingObject} {G : GrpObject}
  (V : RModObject K) : RepObject K G :=
  {| rep_mod := V
   ; rep_hom :=
       {| grp_map := {| morphism := fun _ : carrier G => rep_id_unit V
                      ; proper_morphism := rep_id_unit_respects V |}
        ; grp_map_unit := rep_id_unit_is_unit V
        ; grp_map_mul := fun a b => rep_id_unit_mul V |} |}.

(*
 Negation is a module endomorphism: additive because negation
 distributes over addition in an abelian group, K-linear because
 r·(−m) ≈ −(r·m) ([rm_smul_neg_r]). 

 --------
 否定是一个模的自同态：加法性因为否定在阿贝尔群中的加法下分配，K-线性因为 r·(−m) ≈ −(r·m) ([rm_smul_neg_r])。
*)
Lemma ab_neg_hom_smul {K : RingObject} (V : RModObject K)
  (r : carrier (rig_setoid (ring_rig K)))
  (m : carrier (cmon_setoid V)) :
  ab_neg V (rm_smul V r m) ≈ rm_smul V r (ab_neg V m).
Proof. symmetry; apply rm_smul_neg_r. Qed.

(*
 Written as an explicit record literal rather than through [Program]:
 every field is an existing lemma, so there is nothing to defer, and
 Instance/Ab.v's exported [ab_neg_respects] instance would otherwise
 silently discharge one hole and shift the obligation numbering. 

 --------
 以显式记录字面量的形式编写，而不是通过 [Program] ：每个字段都是现有的引理，因此没有什么可以推迟，并且 Instance/Ab.v 导出的 [ab_neg_respects] 实例否则会悄悄地填补一个空缺并调整义务编号。
*)
Definition rmod_neg_hom {K : RingObject} (V : RModObject K) :
  V ~{RMod K}~> V :=
  {| rm_hom :=
       {| cmon_map := {| morphism        := ab_neg V
                       ; proper_morphism := ab_neg_respects V |}
        ; cmon_map_zero := ab_neg_zero V
        ; cmon_map_plus := ab_neg_plus V |}
   ; rm_map_smul := ab_neg_hom_smul V |}.

(* The sign action of Z/2 on any module: the non-unit element acts by negation, which is its own inverse. / Z/2 在任何模上的符号作用：非单位元素通过取反作用，这是它自身的逆元。 *)
Definition sign_act {K : RingObject} (V : RModObject K) (b : bool) :
  V ~{RMod K}~> V :=
  if b then rmod_neg_hom V else id.

Lemma sign_act_involutive {K : RingObject} (V : RModObject K)
  (b : bool) : sign_act V b ∘ sign_act V b ≈ id.
Proof.
  destruct b.
  - intro a; simpl; apply ab_neg_neg.
  - exact (id_left (@id (RMod K) V)).
Qed.

(*
 The sign representation.  Instance/Grp.v's [Z2] is (bool, xor,
 false), so [grp_mul Z2] is [xorb] and [grp_unit Z2] is [false]; the
 multiplication law is the four-case check that xor of the signs is
 the composite of the two actions. 

 --------
 符号表示。实例/组.v 的 [Z2] 是 (bool, xor, false)，因此 [grp_mul Z2] 是 [xorb]，而 [grp_unit Z2] 是 [false]；乘法法则是对符号的异或进行四种情况的检查，它是两个作用的复合。
*)
Definition sign_unit {K : RingObject} (V : RModObject K)
  (b : carrier Z2) :
  carrier (grp_setoid (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V))) :=
  (sign_act V b;
   (sign_act V b;
    (sign_act_involutive V b, sign_act_involutive V b))).

Lemma sign_unit_respects {K : RingObject} (V : RModObject K) :
  Proper (equiv ==> equiv) (sign_unit V).
Proof.
  intros b b' Hbb'; simpl in Hbb'; subst; reflexivity.
Qed.

Lemma sign_unit_is_unit {K : RingObject} (V : RModObject K) :
  sign_unit V (grp_unit Z2)
    ≈ grp_unit (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V)).
Proof. apply units_equiv; reflexivity. Qed.

Lemma sign_unit_mul {K : RingObject} (V : RModObject K)
  (a b : carrier Z2) :
  sign_unit V (grp_mul Z2 a b)
    ≈ grp_mul (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V))
        (sign_unit V a) (sign_unit V b).
Proof.
  apply units_equiv; symmetry.
  destruct a, b.
  - exact (sign_act_involutive V true).
  - exact (id_right (rmod_neg_hom V)).
  - exact (id_left (rmod_neg_hom V)).
  - exact (id_left (@id (RMod K) V)).
Qed.

Definition sign_rep {K : RingObject} (V : RModObject K) :
  RepObject K Z2 :=
  {| rep_mod := V
   ; rep_hom :=
       {| grp_map := {| morphism := sign_unit V
                      ; proper_morphism := sign_unit_respects V |}
        ; grp_map_unit := sign_unit_is_unit V
        ; grp_map_mul := sign_unit_mul V |} |}.

(*
 Non-vacuity, over the integers as a module over themselves: the
 non-unit element of Z/2 acts by an endomorphism that genuinely moves
 a point, so the sign representation is not the trivial one.  (The
 [≈] of [Int_Ring]'s carrier is Leibniz equality on Z, whence
 [discriminate].) 

 --------
 非空性，作为自身上的模的整数：Z/2 的非单位元素作用于一个端同态，它真正地移动一个点，因此符号表示不是平凡表示。（[≈] 的 [Int_Ring] 的载体是 Z 上的莱布尼茨等式，因此 [discriminate]。）
*)
Lemma sign_rep_moves_one :
  cmon_map (rm_hom (rep_act (sign_rep Int_RMod) true)) 1%Z ≈ (-1)%Z.
Proof. reflexivity. Qed.

Lemma sign_rep_nontrivial :
  rep_act (sign_rep Int_RMod) true ≈ rep_act (sign_rep Int_RMod) false
    → False.
Proof.
  intro H.
  pose proof (H 1%Z) as H1.
  simpl in H1.
  discriminate H1.
Qed.

(*
 The identity module map is not an intertwiner between the two
 witnesses: their actions differ pointwise. 

 --------
 恒等模映射不是两个见证者之间的互纺映射：它们的作用在每一点上都不同。
*)
Lemma sign_rep_not_trivial_rep :
  (∀ g : carrier Z2,
     rep_act (sign_rep Int_RMod) g ≈ rep_act (trivial_rep Int_RMod) g)
    → False.
Proof.
  intro H.
  pose proof (H true 1%Z) as H1.
  simpl in H1.
  discriminate H1.
Qed.

(*
 And the two really are DIFFERENT REPRESENTATIONS in the sense a
 category theorist reads: not merely unequal, but non-isomorphic
 objects of [Rep Int_Ring Z2].  Any intertwiner from the sign
 representation to the trivial one is forced to vanish (equivariance
 at [true] says f(−n) ≈ f(n), additivity says f(−n) ≈ −f(n), so
 2·f(n) = 0 over ℤ), and a vanishing map cannot be half of an
 isomorphism — its round trip at 1 would read 0 = 1. 

 --------
 这两者确实是不同的表示，从范畴论者理解的意义上来看：不仅仅是不相等，而是 [Rep Int_Ring Z2] 的非同构对象。任何从符号表示到平凡表示的交错算子都必然消失（在 [true] 的等变性意味着 f(−n) ≈ f(n)，可加性意味着 f(−n) ≈ −f(n)，所以在 ℤ 上 2·f(n) = 0），而一个消失的映射不可能是同构的一半——其在 1 处的往返将读取为 0 = 1。
*)
Lemma sign_not_iso_trivial :
  @Isomorphism (Rep Int_Ring Z2) (sign_rep Int_RMod) (trivial_rep Int_RMod)
    → False.
Proof.
  intro iso.
  assert (Hzero : ∀ n : Z, cmon_map (rm_hom (itw_map (to iso))) n = 0%Z).
  { intro n.
    assert (Hf : cmon_map (rm_hom (itw_map (to iso))) (Z.opp n)
                   = cmon_map (rm_hom (itw_map (to iso))) n)
      by exact (itw_equivar (to iso) true n).
    assert (Hn : cmon_map (rm_hom (itw_map (to iso))) (Z.opp n)
                   = Z.opp (cmon_map (rm_hom (itw_map (to iso))) n))
      by exact (ab_map_neg (rm_hom (itw_map (to iso))) n).
    lia. }
  assert (H1 : cmon_map (rm_hom (itw_map (to iso)))
                 (cmon_map (rm_hom (itw_map (from iso))) 1%Z) = 1%Z)
    by exact (iso_to_from iso 1%Z).
  rewrite (Hzero _) in H1.
  discriminate H1.
Qed.
