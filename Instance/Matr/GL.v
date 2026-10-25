(** * GL_n and the units functor / * GL_n 和单位函子 *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Matr.
Require Import Category.Instance.Matr.Determinant.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §I.3, printed p. 14 (PDF 24), and §I.4, printed p. 16
 (PDF 26) — maclane:I.3:construction2 (with
 maclane:I.4:construction1 completed by
 Instance/Matr/Determinant.v)
 nLab:      https://ncatlab.org/nlab/show/general+linear+group
 Wikipedia: https://en.wikipedia.org/wiki/General_linear_group

 Mac Lane's §I.3 example: for each n, sending a commutative ring K
 to the group GL_n(K) of invertible n × n matrices is a functor
 CRng ⟶ Grp, and so is sending K to its group of units K^*.  Both
 are instances of ONE construction — the group of units of a
 monoid, taken at the multiplicative monoid of K and at the matrix
 monoid (the endomorphism monoid of n in Matr K) — and a ring
 homomorphism acts entrywise.  The determinant connecting them is
 Instance/Matr/Determinant.v's, and the natural transformation
 det : GL_n ⟹ (−)^* is assembled where the two meet.

 - [UnitsOf]: the group of units of a [MonObject] whose carrier setoid
 is propositional — carrier the two-sided-invertible elements
 compared by their underlying element, inverse by swapping the
 witness — with [UnitsOf_map]: monoid homomorphisms restrict to unit
 groups.  (An earlier revision said "of any [MonObject]".  Since the
 PR "algebraic carriers are sets" (2026-09-17) an [Instance/Grp.v]
 group carries [grp_prop] and a [MonObject] does not, so the witness
 is a hypothesis; see the note at [UnitsOf] below, and note that all
 three consumer families in tree discharge it.)
 - [Ring_mul_mon]: the multiplicative monoid of a ring
 - [Units_Functor]: (−)^* : CRng ⟶ Grp
 - [mat_mon]: the n × n matrix monoid over a ring, as the
 endomorphism monoid of n in [Matr] (Construction/Deloop.v's
 [hom_monoid] — cited, not rebuilt)
 - [mat_map_hom]: a ring homomorphism acts entrywise as a monoid
 homomorphism of matrix monoids
 - [GL_n]: the general linear group functor CRng ⟶ Grp

 Design:

 1. UNITS OF A MONOID, ONCE.  A unit carries its two-sided inverse
 as DATA together with both cancellation laws; two units are
 identified when their underlying elements are — the inverse is
 determined up to ≈ (Construction/Deloop.v's
 [mon_inverse_unique]), so comparing first components is the
 right setoid, and it is what makes every group law reduce to
 monoid algebra on underlying elements.  [GrpObject] here is
 Instance/Grp.v's record (minimal axioms, left laws only), not
 Construction/Deloop.v's.

 2. GL_n IS UNITS OF THE ENDOMORPHISM MONOID.  The n × n matrices
 over K form exactly [hom_monoid (Matr (ring_rig K)) n], so
 invertible matrices are [UnitsOf] of it, and functoriality in K
 is [UnitsOf_map] applied to the entrywise homomorphism — whose
 monoid laws are precisely "ring maps commute with the matrix
 product", [fin_sum] naturality plus preservation of the
 Kronecker delta.

 3. COMMUTATIVITY IS NOT USED HERE.  Both functors below are
 defined on CRng because that is where Mac Lane states them and
 where the determinant lives; nothing in THIS file consumes the
 commutativity witness (matrix multiplication over any ring has
 units).  The witness is consumed by Determinant.v. 

 --------
 书籍：Mac Lane，《为在职数学家设立的范畴》，第2版，§I.3，第14页（PDF第24页），以及§I.4，第16页（PDF第26页）—— maclane:I.3:construction2 （与 maclane:I.4:construction1 由 Instance/Matr/Determinant.v 完成）
 nLab：https://ncatlab.org/nlab/show/general+linear+group
 维基百科：https://en.wikipedia.org/wiki/General_linear_groupMac Lane 的 §I.3 例子：对于每个 n，将一个交换环 K 映射到可逆 n × n 矩阵群 GL_n(K) 是一个函子 CRng ⟶ Grp，同样地，将 K 映射到它的单位群 K^* 也是如此。两者都是一个构造的实例——在 K 的乘法单子和矩阵单子（Matr K 中 n 的自同态单子）上取单子单位群——而环同态则按元素作用。将它们连接起来的行列式是 Instance/Matr/Determinant.v 中的，且自然变换 det : GL_n ⟹ (−)^* 就在两者相交处组装起来。-  [UnitsOf]：[MonObject] 的单位群，其载体集是命题性的——载体是可双边可逆的元素，通过其底层元素比较，逆通过交换见证 —— 与 [UnitsOf_map]：半群同态限制到单位群。（早期的版本写成“任意 [MonObject] 的”。自从PR“代数承载体是集合”（2026-09-17）以来，一个[Instance/Grp.v]群承载[grp_prop]而[MonObject]不承载，因此该见证是一个假设；参见下面[UnitsOf]的注释，并注意树中所有三个消费者族都满足它。
 - [Ring_mul_mon]：一个环的乘法幺半群
 - [Units_Functor]：(-)^* : CRng ⟶ Grp
 - [mat_mon]：环上的n × n矩阵幺半群，作为[Matr]中n的自同构幺半群（Construction/Deloop.v的[hom_monoid]——引用，而非重建）
 - [mat_map_hom]：环同态按元素作用，作为矩阵幺半群的幺半群同态
 - [GL_n]：一般线性群函子 CRng ⟶ Grp

 设计：1. 单元的幺半群，一次。一个单元携带它的双边逆元作为数据，同时满足两种消去律；当两个单元的底层元素相同时，它们被视为相同——逆元在 ≈ 下是确定的（Construction/Deloop.v 的 [mon_inverse_unique]），所以比较首要成分是正确的集合，同样也使得每个群律可归约为底层元素上的幺半群代数。这里的 [GrpObject] 是 Instance/Grp.v 的记录（最小公理，仅左律），而不是 Construction/Deloop.v 的。2. GL_n 是自同态半群的单位元。n × n 的 K 上矩阵恰好构成 [hom_monoid (Matr (ring_rig K)) n]，因此可逆矩阵是其中的 [UnitsOf]，并且在 K 上的函子性是 [UnitsOf_map] 作用于逐元素同态——其半群律正是“环映射与矩阵乘法交换”，[fin_sum] 的自然性加上克罗内克 δ 的保持。

 3. 此处未使用交换性。下面的两个函子都定义在 CRng 上，因为 Mac Lane 在那里陈述它们，并且行列式也存在于那里；此文件中的任何内容都未使用交换性证据（任意环上的矩阵乘法都有单位元素）。该证据在 Determinant.v 中被使用。
*)

(* * ** The group of units of a monoid / * ** 单元群（幺半群的单位） *)

Definition unit_carrier (M : MonObject) : Type :=
  { u : carrier M
  & { v : carrier M
    & (mon_op u v ≈ mon_unit) * (mon_op v u ≈ mon_unit) } }.

(*
 RECORDED STRENGTH CHANGE.  Before the PR "algebraic carriers are sets"
 (2026-09-17) this read [UnitsOf (M : MonObject) : GrpObject].  An
 [Instance/Grp.v] group now carries [grp_prop] and a [MonObject] does not
 (internal algebra keeps the ambient category's equality and carries no
 field, by design), so turning an internal monoid into a concrete group
 asks for the carrier's [PropEquiv] as a hypothesis.  All three consumer
 families in tree discharge it: [hom_monoid (RMod K) V] by
 [RMod_LocallyPropositional], [Ring_mul_mon R] by [rig_prop], and
 [mat_mon R n] by [Matr_LocallyPropositional] below.  Nothing in tree
 became conditional in substance.

 The carrier setoid stays INLINE and [grp_prop] is supplied as a TRAILING
 OBLIGATION rather than as a field.  An intermediate revision named the
 setoid -- a [Program] record literal cannot carry a [PropEquiv] FIELD
 naming a setoid written inline in the same literal -- but naming it puts
 one more unfolding step between the expected type of each sigma below and
 the sigma it builds, and Coq 8.19/8.20 then infer a CONSTANT predicate and
 refuse the term ("has type ∃ _ : …, … while it is expected to have type
 carrier …"; Instance/Rng/Zp.v's header records the trap, and
 Instance/Grp/Center.v records the same one for [mk_central]).  Rocq 9.1
 accepts either.  The obligation route keeps every term below exactly as the
 released toolchains already compiled it. 

 --------
 记录的强度变化。在PR之前，“代数承载体是集合”（2026-09-17），这写作[UnitsOf (M : MonObject) : GrpObject]。一个[Instance/Grp.v]群现在承载[grp_prop]，而一个[MonObject]不承载（内部代数保持环境类别的相等性，并且按设计不承载任何域），因此将一个内部幺半群转化为具体群需要将承载体的[PropEquiv]作为假设。树中的所有三个使用者族都满足它：[hom_monoid (RMod K) V]通过[RMod_LocallyPropositional]，[Ring_mul_mon R]通过[rig_prop]，以及[mat_mon R n]通过下面的[Matr_LocallyPropositional]。树中的实质内容没有变为有条件的。载体集合保持 INLINE，[grp_prop] 被作为尾随义务（TRAILING OBLIGATION）而不是作为字段提供。一个中间修订称其为集合——[Program] 记录字面量不能携带一个 [PropEquiv] 字段来命名在同一字面量中内联写入的集合——但是命名它会在下面每个 sigma 的预期类型和它构建的 sigma 之间增加一步展开，而 Coq 8.19/8.20 随后会推断出一个常量谓词并拒绝该项（“类型为 ∃ _ : …, …，而预期类型为 carrier …”；Instance/Rng/Zp.v 的头部记录了这个陷阱，Instance/Grp/Center.v 对 [mk_central] 也记录了同样的情况）。Rocq 9.1 接受任何一种方法。采用义务路径可以保持下面的每个项完全按照已发布的工具链所编译的方式。
*)
Program Definition UnitsOf (M : MonObject)
  (PM : PropEquiv (is_setoid (mon_setoid M))) : GrpObject := {|
  grp_setoid :=
    {| carrier := unit_carrier M;
       is_setoid := {| equiv := fun x y => `1 x ≈ `1 y |} |};
  grp_unit := (mon_unit; (mon_unit; (_, _)));
  grp_mul := fun x y =>
    (mon_op (`1 x) (`1 y); (mon_op (`1 (`2 y)) (`1 (`2 x)); (_, _)));
  grp_inv := fun x => (`1 (`2 x); (`1 x; (snd (`2 (`2 x)), fst (`2 (`2 x)))))
|}.
Next Obligation.
  intros M PM; equivalence.
Qed.
Next Obligation.
  intros M PM; apply mon_op_unit_l.
Qed.
Next Obligation.
  intros M PM; apply mon_op_unit_l.
Qed.
Next Obligation.
  (* (u·u')·(v'·v) ≈ 1 *)
  intros M PM [u [v [pl pr]]] [u' [v' [pl' pr']]]; simpl.
  rewrite <- mon_op_assoc.
  rewrite (mon_op_assoc u' v' v).
  rewrite pl'.
  rewrite mon_op_unit_l.
  exact pl.
Qed.
Next Obligation.
  (* (v'·v)·(u·u') ≈ 1 *)
  intros M PM [u [v [pl pr]]] [u' [v' [pl' pr']]]; simpl.
  rewrite <- mon_op_assoc.
  rewrite (mon_op_assoc v u u').
  rewrite pr.
  rewrite mon_op_unit_l.
  exact pr'.
Qed.
Next Obligation.
  intros M PM x y Hxy x' y' Hxy'; simpl.
  apply mon_op_respects; [ exact Hxy | exact Hxy' ].
Qed.
Next Obligation.
  intros M PM x y z; simpl.
  symmetry; apply mon_op_assoc.
Qed.
Next Obligation.
  intros M PM x; simpl.
  apply mon_op_unit_l.
Qed.
Next Obligation.
  intros M PM [u [v [pl pr]]]; simpl.
  exact pr.
Qed.
Next Obligation.
  (*
 G6.  The unit group's `≈` compares first projections in [M], so it is
 propositional exactly when [M]'s carrier `≈` is; the membership data --
 the inverse and the two equations -- is a [Type] and is never inspected,
 which is what [sigma_first_PropEquiv] formalises.  Applied in the TACTIC
 form, the one the term form is refused in. 

 --------
 G6.  单元组的 `≈` 比较 [M] 中的第一个投影，因此当 [M] 的承载 `≈` 是命题时，它也是命题；成员数据——逆和两个方程——是 [Type]，并且从未被检查，这正是 [sigma_first_PropEquiv] 所形式化的。在 TACTIC 形式中应用时，术语形式会被拒绝。
*)
  intros M PM.
  unshelve refine (sigma_first_PropEquiv _ _ _ PM).
  - intros p q Hpq; exact Hpq.
  - intros p q Hpq; exact Hpq.
Defined.

(* Monoid homomorphisms restrict to the unit groups: the image of a two-sided inverse is a two-sided inverse of the image. / 幺半群同态限制到幺元群：双边逆元的像是其像的双边逆元。 *)
Program Definition UnitsOf_map {M N : MonObject}
  {PM : PropEquiv (is_setoid (mon_setoid M))}
  {PN : PropEquiv (is_setoid (mon_setoid N))} (h : MonHom M N) :
  GrpHom (UnitsOf M PM) (UnitsOf N PN) := {|
  grp_map :=
    {| morphism := fun x =>
         (h (`1 x); (h (`1 (`2 x)); (_, _))) |}
|}.
Next Obligation.
  intros M N PM PN h [u [v [pl pr]]]; simpl.
  rewrite <- mon_map_op.
  rewrite pl.
  apply mon_map_unit.
Qed.
Next Obligation.
  intros M N PM PN h [u [v [pl pr]]]; simpl.
  rewrite <- mon_map_op.
  rewrite pr.
  apply mon_map_unit.
Qed.
Next Obligation.
  intros M N PM PN h x y Hxy; simpl.
  apply mon_map_respects; exact Hxy.
Qed.
Next Obligation.
  intros M N PM PN h; simpl.
  apply mon_map_unit.
Qed.
Next Obligation.
  intros M N PM PN h x y; simpl.
  apply mon_map_op.
Qed.

(* * ** The units functor on commutative rings / * ** 交换环上的幺元函子 *)

(* The multiplicative monoid of a ring. / 环的乘法幺半群。 *)
Program Definition Ring_mul_mon (K : RingObject) : MonObject := {|
  mon_setoid := rig_setoid (ring_rig K);
  mon_unit := rig_one (ring_rig K);
  mon_op := rig_mul (ring_rig K);
  mon_op_respects := rig_mul_respects (ring_rig K);
  mon_op_unit_l := rig_mul_one_l (ring_rig K);
  mon_op_unit_r := rig_mul_one_r (ring_rig K)
|}.
Next Obligation.
  intros K a b c; symmetry; apply rig_mul_assoc.
Qed.

(*
 A rig homomorphism is a monoid homomorphism of the multiplicative
 monoids. 

 --------
 一个环同态是乘法幺半群的幺半群同态。
*)
Program Definition mul_MonHom {K K' : RingObject}
        (h : RigHom (ring_rig K) (ring_rig K')) :
  MonHom (Ring_mul_mon K) (Ring_mul_mon K') := {|
  mon_map := fun a => rig_map h a;
  mon_map_respects := proper_morphism (rig_map h)
|}.
Next Obligation.
  intros K K' h; apply rig_map_one.
Qed.
Next Obligation.
  intros K K' h a b; apply rig_map_mul.
Qed.

(*
 The witness [UnitsOf] asks for at a ring's multiplicative monoid: the
 monoid's carrier setoid IS the rig's, so it is [rig_prop]. 

 --------
 证人 [UnitsOf] 询问一个环的乘法幺半群：该幺半群的承载集的集合论等价类就是环的，所以它是 [rig_prop] 。
*)
Definition ring_mul_mon_prop (K : RingObject) :
  PropEquiv (is_setoid (mon_setoid (Ring_mul_mon K))) :=
  rig_prop (ring_rig K).

(*
 (−)^* : CRng ⟶ Grp — the group of units, functorially.  A CRng
 morphism is a Subcategory hom: the underlying RigHom carrying a
 (trivial) membership witness. 

 --------
 (−)^* : CRng ⟶ Grp — 单位群，函子化的。一个 CRng
 同态是一个子范畴同态：底层的 RigHom 携带一个（平凡的）成员资格证明。
*)
Program Definition Units_Functor : CRng ⟶ Grp := {|
  fobj := fun K => UnitsOf (Ring_mul_mon (`1 K)) (ring_mul_mon_prop (`1 K));
  fmap := fun K K' h => UnitsOf_map (mul_MonHom (`1 h))
|}.
Next Obligation.
  intros K K' f g Hfg [u [v p]]; simpl.
  exact (Hfg u).
Qed.
Next Obligation.
  intros K [u [v p]]; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros K K' K'' f g [u [v p]]; simpl.
  reflexivity.
Qed.

(* * ** The general linear group functor / * ** 一般线性群函子 *)

(*
 The n × n matrix monoid over a ring: the endomorphism monoid of the
 object n of Matr. 

 --------
 环上的 n × n 矩阵幺半群：Matr 中对象 n 的自同态幺半群。
*)
Definition mat_mon (K : RingObject) (n : nat) : MonObject :=
  hom_monoid (Matr (ring_rig K)) n.

(*
 [Matr R]'s hom-setoid is entrywise `≈` in [R], so it is propositional
 whenever [R] is -- which it always is, [rig_prop] being a field.  Stated
 here rather than in Instance/Matr.v to keep the change local; it is the
 witness [UnitsOf] asks for at [mat_mon]. 

 --------
 [Matr R] 的同态集合是 [R] 中按条目为 `≈` 的，因此每当 [R] 是命题时，它也是命题——ZWW3WZZ 是一个域时，它总是命题。在这里说明而不是在 Instance/Matr.v 中说明以保持修改的局部性；这是 [UnitsOf] 在 [mat_mon] 处所要求的见证。
*)
Definition Matr_LocallyPropositional (R : RigObject) :
  LocallyPropositional (Matr R) :=
  LocallyPropositional_of_relation (Matr R)
    (fun n m A B => forall i j, @pequiv _ _ (rig_prop R) (A i j) (B i j))
    (fun n m A B H i j => pequiv_to _ _ (H i j))
    (fun n m A B H i j => pequiv_from _ _ (H i j)).

(* The witness [UnitsOf] asks for at the matrix monoid. / 证人 [UnitsOf] 在矩阵幺半群中提出要求。 *)
Definition mat_mon_prop (K : RingObject) (n : nat) :
  PropEquiv (is_setoid (mon_setoid (mat_mon K n))) :=
  @locally_prop (Matr (ring_rig K)) (Matr_LocallyPropositional (ring_rig K))
    n n.

(*
 Ring maps commute with finite sums: Determinant.v's
 [rig_map_fin_sum] (consumed, not rebuilt). 

 --------
 环映射与有限和交换：Determinant.v 的 [rig_map_fin_sum]（已消耗，未重建）。
*)

(* Ring maps preserve the Kronecker delta. / 环映射保持克罗内克 δ。 *)
Lemma rig_map_delta {K K' : RigObject} (h : RigHom K K')
      {n : nat} (i j : Fin.t n) :
  rig_map h (delta K i j) ≈ delta K' i j.
Proof.
  unfold delta.
  destruct (Fin.eq_dec i j).
  - apply rig_map_one.
  - apply rig_map_zero.
Qed.

(*
 A ring homomorphism acts entrywise on matrices, as a homomorphism
 of the matrix monoids: preservation of the identity is preservation
 of delta, and preservation of the product is fin_sum naturality
 plus preservation of + and ·. 

 --------
 环同态在矩阵上逐项作用，作为矩阵幺半群的同态：恒等元的保持就是Δ的保持，乘积的保持是有限和的自然性加上加法和乘法的保持。
*)
Program Definition mat_map_hom {K K' : RingObject}
        (h : RigHom (ring_rig K) (ring_rig K')) (n : nat) :
  MonHom (mat_mon K n) (mat_mon K' n) := {|
  mon_map := fun A => (fun i j => rig_map h (A i j))
             : @Matrix (ring_rig K') n n
|}.
Next Obligation.
  intros K K' h n A B HAB i j; simpl.
  apply (proper_morphism (rig_map h)); exact (HAB i j).
Qed.
Next Obligation.
  intros K K' h n i j; simpl.
  apply rig_map_delta.
Qed.
Next Obligation.
  intros K K' h n A B i j; simpl.
  rewrite (rig_map_fin_sum K K' h).
  apply fin_sum_respects; intro l.
  apply rig_map_mul.
Qed.

(* GL_n : CRng ⟶ Grp — invertible n × n matrices, functorially. / GL_n : CRng ⟶ Grp — 可逆的 n × n 矩阵，函子化的。 *)
Program Definition GL_n (n : nat) : CRng ⟶ Grp := {|
  fobj := fun K => UnitsOf (mat_mon (`1 K) n) (mat_mon_prop (`1 K) n);
  fmap := fun K K' h => UnitsOf_map (mat_map_hom (`1 h) n)
|}.
Next Obligation.
  intros n K K' f g Hfg [A [B p]] i j; simpl.
  exact (Hfg (A i j)).
Qed.
Next Obligation.
  intros n K [A [B p]] i j; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros n K K' K'' f g [A [B p]] i j; simpl.
  reflexivity.
Qed.

(* * ** The determinant as a natural transformation / * ** 行列式作为一种自然变换 *)

(*
 det restricted to the unit groups: an invertible matrix has a unit
 determinant — the inverse matrix's determinant inverts it, by
 multiplicativity and det of the identity. 

 --------
 行列式限制在单位群上：可逆矩阵具有单位行列式——通过乘法性和单位矩阵的行列式，逆矩阵的行列式是其倒数。
*)
Program Definition det_GrpHom (n : nat) (K : obj[CRng]) :
  GrpHom (UnitsOf (mat_mon (`1 K) n) (mat_mon_prop (`1 K) n))
         (UnitsOf (Ring_mul_mon (`1 K)) (ring_mul_mon_prop (`1 K))) := {|
  grp_map := {| morphism := fun x =>
    (det (`1 K) (`1 x);
     (det (`1 K) (`1 (`2 x)); (_, _))) |}
|}.
Next Obligation.
  intros n K [A [B [pl pr]]]; simpl.
  rewrite <- (det_compose (`1 K) (`2 K) A B).
  etransitivity; [ apply (det_respects (`1 K)); exact pl | apply det_id ].
Qed.
Next Obligation.
  intros n K [A [B [pl pr]]]; simpl.
  rewrite <- (det_compose (`1 K) (`2 K) B A).
  etransitivity; [ apply (det_respects (`1 K)); exact pr | apply det_id ].
Qed.
Next Obligation.
  intros n K x y Hxy; simpl.
  apply (det_respects (`1 K)); exact Hxy.
Qed.
Next Obligation.
  intros n K; simpl.
  apply det_id.
Qed.
Next Obligation.
  intros n K x y; simpl.
  apply (det_compose (`1 K) (`2 K)).
Qed.

(*
 Mac Lane's §I.4 flagship: the determinant is a natural
 transformation det : GL_n ⟹ (−)^*.  Naturality in the ring is the
 reviewer's square det_{K'} ∘ GL_n f ≈ f^* ∘ det_K — the polynomial
 formula commutes with every ring homomorphism ([det_map]). 

 --------
 Mac Lane §I.4 的旗舰内容：行列式是一个自然变换 det : GL_n ⟹ (−)^*。在环上的自然性是审阅者的方形 det_{K'} ∘ GL_n f ≈ f^* ∘ det_K ——多项式公式与每个环同态交换 ([det_map])。
*)
Program Definition det_Transform (n : nat) :
  GL_n n ⟹ Units_Functor := {|
  transform := fun K => det_GrpHom n K
|}.
Next Obligation.
  intros n K K' h [A [B p]]; simpl.
  apply (det_map (`1 K) (`1 K') (`1 h) A).
Qed.
Next Obligation.
  intros n K K' h [A [B p]]; simpl.
  symmetry.
  apply (det_map (`1 K) (`1 K') (`1 h) A).
Qed.
