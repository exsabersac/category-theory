(* * * Products of categories subsume the classical products / * * 范畴的积包含经典的积 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Cat.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §II.3 Exercise 1, printed p. 39 (PDF p. 49) — maclane:II.3:ex1
 nLab:      https://ncatlab.org/nlab/show/product+category

 Mac Lane's exercise: the product of categories restricts, along the
 standard full embeddings, to the familiar products of algebraic
 structures — a note carried here in prose, as the exercise states it:
 no Mon ⟶ Cat or Set ⟶ Cat embedding functor exists in-tree yet, and
 the three isomorphisms below are their object-level content —
 delooped monoids (and groups) multiply componentwise, and discrete
 categories multiply as sets.  Three specializations, each an
 isomorphism in [Cat] (up to the natural isomorphisms of
 [Functor_Setoid], the library's hom-equivalence there — in this
 library the strength of an equivalence of categories, per
 Instance/Cat.v's header; the issue's StrictCat alternative is not
 taken, though the discrete case is morally strict, because strict
 functor equality would need the transport machinery of
 Functor_StrictEq, out of proportion for this exercise):

 - [Deloop_prod_iso]   : Deloop (M × N) ≅ Deloop M ∏ Deloop N
 - [Deloop_grp_prod]   : the same statement read at product groups —
 the monoid part of [GrpObject_prod] IS
 [MonObject_prod] definitionally, so the
 isomorphism is literally the same term
 - [Discrete_Product]  : DiscreteCat (A * B) ≅ DiscreteCat A ∏
 DiscreteCat B

 Design:

 1. THE HOM-SIDES ARE DEFINITIONALLY EQUAL.  A hom of
 [Deloop (MonObject_prod M N)] is an element of [carrier M * carrier N],
 and a hom of [Deloop M ∏ Deloop N] is exactly the same pair type; both
 functors of [Deloop_prod_iso] are the identity on arrows, and the
 whole isomorphism is object-side bookkeeping about [poly_unit]
 (whose two-component tuples are collapsed by unit-morphism
 conjugation, not by eta).  Likewise [Discrete_Product]'s object
 types agree on the nose — [A * B] both times — and only the
 MORPHISM encodings differ: one equality of pairs versus a pair of
 equalities, converted by [f_equal] projections one way and the
 local transparent [pair_eta]/[pair_equal] kit the other — local
 because the stdlib's [surjective_pairing] and [f_equal2] are
 opaque, and an arrow action built on them would be stuck,
 sinking every functor law.

 2. NO UIP.  [DiscreteCat]'s hom-setoid is strict equality of equality
 proofs, so the functor laws and round trips are equations between
 proof terms; each is closed by destructing the objects (exposing
 the pairs) and then the morphisms (collapsing to [eq_refl]),
 never by an axiom.  [Print Assumptions] on every artifact here is
 closed under the global context.

 3. THE GROUP CASE IS A RESTRICTION, NOT A SECOND PROOF.  [Deloop]
 consumes only the monoid part, and [GrpObject_prod] is built so
 its [grp_monoid] projection is [MonObject_prod] of the parts by
 [eq_refl]; Mac Lane's "the same statement restricted to groups"
 is therefore delivered by applying [Deloop_prod_iso] at the
 underlying monoids, with the componentwise inverse supplied only
 to close the group structure itself.

 4. NAMESPACE NOTE.  [MonObject]/[GrpObject] here are
 Construction/Deloop.v's setoid records; Instance/Grp.v defines a
 DIFFERENT record also named [GrpObject] (with carrier-level
 fields) and already carries its own componentwise [Grp_product]
 with projections and [Grp_Cartesian].  The two products live at
 different layers and neither subsumes the other; this file's is
 the one the delooping dictionary consumes. 

 --------
 书籍：      Mac Lane，《工作数学家的范畴》，第2版，
 §II.3 习题 1，印刷页 39（PDF 页 49） — maclane:II.3:ex1
 nLab：       https://ncatlab.org/nlab/show/product+categoryMac Lane 的练习：范畴的积沿着标准的满嵌入，约束为熟悉的代数结构积 —— 如练习所说明，这里以散文形式记录：目前尚不存在 Mon ⟶ Cat 或 Set ⟶ Cat 的树内嵌入函子，而且下面的三个同构是它们在对象层面的内容 —— 去环化的单元（和群）按分量相乘，离散范畴按集合相乘。三个特化，每一个都是 [Cat] 中的同构（在 [Functor_Setoid] 的自然同构下 —— 即该库中的 Hom 等价性 —— 在本库中是范畴等价的强度，根据 Instance/Cat.v 的标题；问题中的 StrictCat 替代方案未被采用，尽管离散情况在道义上是严格的，因为严格函子相等需要 Functor_StrictEq 的传输机制，对于此练习而言是不成比例的）：-  [Deloop_prod_iso]    : Deloop (M × N) ≅ Deloop M ∏ Deloop N
 -  [Deloop_grp_prod]    : 在乘积群上读取的相同陈述 —
 [GrpObject_prod] 的幺半群部分在定义上是 [MonObject_prod]，因此
 同构在字面上是相同的项
 -  [Discrete_Product]   : DiscreteCat (A * B) ≅ DiscreteCat A ∏
 DiscreteCat B

 设计：1. 同侧在定义上是相等的。[Deloop (MonObject_prod M N)] 的同态是 [carrier M * carrier N] 的一个元素，[Deloop M ∏ Deloop N] 的同态完全是相同的对类型；[Deloop_prod_iso] 的两个函子在箭头上都是恒等的，而整个同构是关于 [poly_unit] 的对象侧记录（其两分量元组通过单位同态共轭被折叠，而不是通过 η）。同样，[Discrete_Product] 的对象类型完全一致——[A * B] 两次——只有 MORPHISM 编码不同：一个是成对的等式与一对等式，通过 [f_equal] 投影一种方法转换，另一种通过本地透明的 [pair_eta] / [pair_equal] 工具包转换——之所以称为本地，是因为 stdlib 的 [surjective_pairing] 和 [f_equal2] 是不透明的，基于它们构建的箭头操作会被卡住，从而破坏每个函子律。

 2. 无 UIP。[DiscreteCat] 的同构集是等式证明的严格相等，因此函子律和循环往返是证明项之间的等式；每个通过解构对象（暴露成对的元素）然后解构态射（收缩为 [eq_refl]）完成，从未通过公理完成。这里每个工件上的 [Print Assumptions] 都在全局上下文下闭合。3. 群情况是一种限制，而不是第二种证明。[Deloop] 只使用了幺半群部分，而 [GrpObject_prod] 的构建方式是使其 [grp_monoid] 投影成为通过 [eq_refl] 获得部分的 [MonObject_prod]；因此，Mac Lane 所说的“相同命题限制到群上”的结果，是通过在基础幺半群上应用 [Deloop_prod_iso] 得到的，而逐分量的逆仅用于闭合群结构本身。4. 命名空间注释。[MonObject] / [GrpObject] 这里是 Construction/Deloop.v 的集合记录；Instance/Grp.v 定义了一个同样名为 [GrpObject]（具有承载层字段）的不同记录，并且已经拥有其自身的逐分量 [Grp_product]，带有投影和 [Grp_Cartesian]。这两个积在不同层次上存在，且互不包含；本文件的记录是解环字典使用的那个。
*)


(* * ** The product monoid, and the product group / * ** 积幺半群，和积群 *)

(*
 The product setoid is Lib/Datatypes.v's [prod_setoid], the same idiom
 Instance/Grp.v's [Grp_product] uses — reusing it keeps the registered
 [Proper] instances ([pair_respects], [fst_respects], [snd_respects])
 applicable to the product carrier. 

 --------
 积类型 setoid 是 Lib/Datatypes.v 的 [prod_setoid]，Instance/Grp.v 的 [Grp_product] 使用了相同的习惯用语 —— 重新使用它可以保持已注册的 [Proper] 实例（[pair_respects]、[fst_respects]、[snd_respects]）适用于积类型载体。
*)
Definition prod_SetoidObject (M N : MonObject) : SetoidObject := {|
  carrier := carrier M * carrier N;
  is_setoid := @prod_setoid _ _ (is_setoid M) (is_setoid N)
|}.

Program Definition MonObject_prod (M N : MonObject) : MonObject := {|
  mon_setoid := prod_SetoidObject M N;
  mon_unit := (mon_unit, mon_unit);
  mon_op := fun p q => (mon_op (fst p) (fst q), mon_op (snd p) (snd q))
|}.
Next Obligation.
  intros M N p p' [Hp1 Hp2] q q' [Hq1 Hq2]; split; simpl.
  - exact (mon_op_respects M _ _ Hp1 _ _ Hq1).
  - exact (mon_op_respects N _ _ Hp2 _ _ Hq2).
Qed.
Next Obligation.
  intros M N a b c; split; simpl; apply mon_op_assoc.
Qed.
Next Obligation.
  intros M N a; split; simpl; apply mon_op_unit_l.
Qed.
Next Obligation.
  intros M N a; split; simpl; apply mon_op_unit_r.
Qed.

Program Definition GrpObject_prod (G H : GrpObject) : GrpObject := {|
  grp_monoid := MonObject_prod G H;
  grp_inv := fun p => (grp_inv (fst p), grp_inv (snd p))
|}.
Next Obligation.
  intros G H a; split; simpl; apply grp_inv_l.
Qed.
Next Obligation.
  intros G H a; split; simpl; apply grp_inv_r.
Qed.

Example GrpObject_prod_monoid (G H : GrpObject) :
  grp_monoid (GrpObject_prod G H) = MonObject_prod G H := eq_refl.

(** ** Delooping preserves products / ** 退环保持乘积 *)

(*
 Both functors are the identity on arrows (design note 1); only the
 single objects need shuttling. 

 --------
 两个函子在箭头上都是恒等的（设计说明 1）；只有单个对象需要传递。
*)
Program Definition Deloop_prod_to (M N : MonObject) :
  Deloop (MonObject_prod M N) ⟶ Deloop M ∏ Deloop N := {|
  fobj := fun _ => (ttt, ttt);
  fmap := fun _ _ p => p
|}.
Next Obligation.
  intros M N x y p q Hpq; exact Hpq.
Qed.
Next Obligation.
  intros M N x; simpl; split; reflexivity.
Qed.
Next Obligation.
  intros M N x y z p q; simpl; split; reflexivity.
Qed.

Program Definition Deloop_prod_from (M N : MonObject) :
  Deloop M ∏ Deloop N ⟶ Deloop (MonObject_prod M N) := {|
  fobj := fun _ => ttt;
  fmap := fun _ _ p => p
|}.
Next Obligation.
  intros M N x y p q Hpq; exact Hpq.
Qed.
Next Obligation.
  intros M N x; simpl; split; reflexivity.
Qed.
Next Obligation.
  intros M N x y z p q; simpl; split; reflexivity.
Qed.

(*
 The isomorphism in Cat: the composites are the identity on arrows, and
 the object round trips are closed by unit-morphism conjugation. 

 --------
 Cat 中的同构：复合映射在箭头上是恒等映射，并且对象的往返通过单位态射共轭闭合。
*)
Program Definition Deloop_prod_iso (M N : MonObject) :
  Deloop (MonObject_prod M N) ≅[Cat] Deloop M ∏ Deloop N := {|
  to   := Deloop_prod_to M N;
  from := Deloop_prod_from M N
|}.
Next Obligation.
  intros M N; unshelve eexists.
  - intros [a b].
    unshelve refine
      (@Build_Isomorphism (Deloop M ∏ Deloop N) (ttt, ttt) (a, b)
         (mon_unit, mon_unit) (mon_unit, mon_unit) _ _).
    + split; simpl; apply mon_op_unit_l.
    + split; simpl; apply mon_op_unit_l.
  - intros [a b] [c d] [f g]; simpl; split;
    exact (symmetry
             (transitivity (mon_op_unit_r _) (mon_op_unit_l _))).
Qed.
Next Obligation.
  intros M N; unshelve eexists.
  - intros x.
    unshelve refine
      (@Build_Isomorphism (Deloop (MonObject_prod M N)) ttt x
         (mon_unit, mon_unit) (mon_unit, mon_unit) _ _).
    + split; simpl; apply mon_op_unit_l.
    + split; simpl; apply mon_op_unit_l.
  - intros x y p; simpl; split;
    exact (symmetry
             (transitivity (mon_op_unit_r _) (mon_op_unit_l _))).
Qed.

(*
 Mac Lane's "the group case is the same statement restricted to groups":
 the isomorphism at product groups is the monoid isomorphism verbatim,
 because [Deloop] consumes only the monoid part (design note 3). 

 --------
 Mac Lane 的“群的情况是限制在群上的相同陈述”：
 在乘积群上的同构就是单模同构的逐字对应，
 因为 [Deloop] 只消耗单模部分（设计说明 3）。
*)
Definition Deloop_grp_prod (G H : GrpObject) :
  Deloop (GrpObject_prod G H) ≅[Cat] Deloop G ∏ Deloop H :=
  Deloop_prod_iso G H.

(* * ** Discrete categories multiply as sets / * ** 离散类别作为集合相乘 *)

Program Definition Discrete_Product_to (A B : Type) :
  DiscreteCat (A * B) ⟶ DiscreteCat A ∏ DiscreteCat B := {|
  fobj := fun p => p;
  fmap := fun x y e => (f_equal fst e, f_equal snd e)
|}.
Next Obligation.
  intros A B x; simpl; split; reflexivity.
Qed.
Next Obligation.
  intros A B x y z e e'; simpl.
  destruct e, e'; simpl; split; reflexivity.
Qed.

(*
 Transparent equality kit for pairs: the stdlib's [surjective_pairing]
 and [f_equal2] are opaque, which would leave the arrow action stuck
 and sink every functor law; these compute. 

 --------
 用于对的透明等式工具包：stdlib 的 [surjective_pairing] 和 [f_equal2] 是不透明的，这会导致箭头操作被卡住，并破坏每个函子定律；这些可以计算。
*)
Definition pair_eta {A B : Type} (p : A * B) : p = (fst p, snd p) :=
  match p with (a, b) => eq_refl end.

Definition pair_equal {A B : Type} {a c : A} {b d : B}
  (e1 : a = c) (e2 : b = d) : (a, b) = (c, d) :=
  match e1 in _ = c', e2 in _ = d' return (a, b) = (c', d') with
  | eq_refl, eq_refl => eq_refl
  end.

Program Definition Discrete_Product_from (A B : Type) :
  DiscreteCat A ∏ DiscreteCat B ⟶ DiscreteCat (A * B) := {|
  fobj := fun p => p;
  fmap := fun x y e =>
    eq_trans (pair_eta x)
      (eq_trans (pair_equal (fst e) (snd e))
         (eq_sym (pair_eta y)))
|}.
Next Obligation.
  intros A B x y e e' He; simpl in *.
  destruct He as [He1 He2]; simpl in *.
  rewrite He1, He2; reflexivity.
Qed.
Next Obligation.
  intros A B [a b]; simpl; reflexivity.
Qed.
Next Obligation.
  intros A B [a b] [c d] [e f] p q; simpl.
  destruct p as [p1 p2], q as [q1 q2]; simpl in *.
  destruct p1, p2, q1, q2; simpl; reflexivity.
Qed.

Program Definition Discrete_Product (A B : Type) :
  DiscreteCat (A * B) ≅[Cat] DiscreteCat A ∏ DiscreteCat B := {|
  to   := Discrete_Product_to A B;
  from := Discrete_Product_from A B
|}.
Next Obligation.
  intros A B; exists (fun p => iso_id).
  intros [a b] [c d] [e1 e2]; simpl in *.
  destruct e1, e2; simpl; split; reflexivity.
Qed.
Next Obligation.
  intros A B; exists (fun x => iso_id).
  intros x y e; simpl.
  destruct e; simpl.
  destruct x; simpl; reflexivity.
Qed.

(** ** Witnesses / ** 证人 *)

(*
 The product monoid computes at Construction/Deloop.v's inhabitants,
 and the discrete comparison is the identity on a concrete pair. 

 --------
 乘积幺半群在 Construction/Deloop.v 的元素上进行计算，离散比较在具体对上是恒等映射。
*)
Example MonObject_prod_computes :
  @mon_op (MonObject_prod Nat_Plus Bool_Xor) (3%nat, true) (2%nat, true)
    = (5%nat, false) := eq_refl.

Example Discrete_Product_computes :
  fobj[to (Discrete_Product bool nat)] (true, 7%nat)
    = (true, 7%nat) := eq_refl.
