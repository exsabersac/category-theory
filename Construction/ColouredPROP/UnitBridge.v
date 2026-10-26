Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Instance.
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.PROP.Universal.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Universal.

From Coq Require Import Arith.
From Coq Require Import Lists.List.
From Coq Require Import Eqdep_dec.
Import ListNotations.

Generalizable All Variables.

(*
   * * The unit-colour bridge: PROPs are one-colour coloured PROPs 

   --------
   * * 单色桥梁：PROP是单色的PROP
*)

(*
 nLab:      https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 [Construction/ColouredPROP.v] closes with a discussion (its section
 “Discussion: relationship to plain PROPs”) observing that a [PROP]
 is the one-colour special case of [ColouredPROP unit] — the
 wire-list [list unit] is in bijection with [nat] via [length], with
 [cprop_of_list (repeat tt n)] corresponding to [prop_of_nat n] and
 concatenation to addition — and defers the formal bridge to a
 downstream construction.  This file is that construction.

 It has three layers:

 1. CLASS-LEVEL TRANSPORTS.  [PROP_to_ColouredPROP] equips the
 category underlying any [PROP] with a [ColouredPROP unit]
 structure ([cprop_of_list := length]-indexed naming), and
 [ColouredPROP_unit_to_PROP] converts back
 ([prop_of_nat := repeat tt]-indexed naming).  Both reuse the
 SAME strict/symmetric structures and the SAME coherence proof,
 so the underlying category, both [Monoidal] paths, and the
 coherence field are preserved on the nose (machine-checked
 [Example]s).  Only the object-naming function changes, riding
 [len_app] respectively [repeat_app].

 2. FREE-LEVEL BRIDGE FUNCTORS.  For a one-sorted signature [S],
 the unit-coloured signature [USig S] reads a generator's arity
 off the lengths of its colour words.  The two universal
 properties then hand us strict symmetric monoidal functors in
 both directions with NO fresh induction over terms:

 [LengthFunctor : CFreeCat (USig S) ⟶ FreeCat S]
 is [CInterpF] at the coloured-PROP-transported free PROP
 ([LengthPROP := PROP_to_ColouredPROP (FreePROP S)]);
 [RepeatFunctor : FreeCat S ⟶ CFreeCat (USig S)]
 is [InterpF] at the PROP-transported free coloured PROP
 ([RepeatPROP := ColouredPROP_unit_to_PROP
 (FreeColouredPROP (USig S) unit_dec)]).

 Their strict monoidal packagings are the [CInterpF_Strict] /
 [InterpF_Strict] instances at those targets; the strict object
 comparisons are the transported class fields, i.e. the
 [len_app]- respectively [repeat_app]-shaped equalities of
 layer 1.

 3. ROUND-TRIP LAWS.  On objects the two composites are
 [length (repeat tt n) = n] ([repeat_length]) and
 [repeat tt (length l) = l] ([unit_list_eta], which needs
 eta for [unit] and is exactly where “one colour” enters).  On
 morphisms, both round trips are the identity up to [hom_cast]
 conjugation along those object equalities:

 [LengthRepeat_roundtrip] :
 hom_cast ∘ fmap[LengthFunctor ◯ RepeatFunctor] ≈ id
 [RepeatLength_roundtrip] :
 hom_cast ∘ fmap[RepeatFunctor ◯ LengthFunctor] ≈ id

 Each is closed by the corresponding uniqueness theorem
 ([interp_unique2] / [cinterp_unique2]) applied to the composite
 and to the identity functor, both packaged strictly
 ([Compose_StrictMonoidalFunctor] / [Id_StrictMonoidalFunctor])
 and with braid-compatibility squares proved by the [id_cast]
 calculus of [Construction/Quotient.v] — the composite square
 collapses because every strict braiding in sight is
 definitionally the free braid constructor ([Example]s
 [strict_braid_FreePROP_eq] etc. pin this).

 On-the-nose functoriality of the round trips is unattainable:
 [repeat_length] and [unit_list_eta] are propositional, not
 definitional, so the conjugated [hom_cast] form is the honest
 statement — the same hom_cast-conjugation discipline as the
 base-change laws (see the Discussion at the foot of
 [Construction/ColouredPROP/BaseChange/Laws.v]).  In
 this precise sense coloured PROPs are a strict generalisation of
 PROPs: the one-colour free coloured PROP and the free PROP are
 equivalent through strict symmetric monoidal functors that are
 mutually inverse up to the canonical strictness casts. 

 --------
 nLab：       https://ncatlab.org/nlab/show/PROP 
 维基百科：  https://en.wikipedia.org/wiki/PROP_(category_theory) 

 [Construction/ColouredPROP.v]  在一节“讨论：与普通 PROPs 的关系”中以讨论结尾，观察到一个 [PROP] 
 是 [ColouredPROP unit] 的单色特例——
 线列表 [list unit] 通过 [length] 与 [nat] 形成一一对应，
 [cprop_of_list (repeat tt n)] 对应 [prop_of_nat n]，
 串联对应加法——并将正式的桥接推迟到下游构造。这个文件就是那个构造。

 它有三层：1. 类级传输。[PROP_to_ColouredPROP] 为任何 [PROP] 配备了一个 [ColouredPROP unit] 结构（[cprop_of_list := length] 索引命名），并且 [ColouredPROP_unit_to_PROP] 可以转换回（[prop_of_nat := repeat tt] 索引命名）。两者都复用了相同的严格/对称结构和相同的相干性证明，因此基础范畴、[Monoidal] 路径以及相干性域在类型上保持不变（机器检查的 [Example]）。唯一改变的是对象命名函数，分别使用 [len_app] 和 [repeat_app]。2. 自由层桥函子。对于一元签名 [S]，单位着色签名 [USig S] 通过颜色词的长度读取生成元的元数。这两个泛性质随后为我们提供了两个方向上严格的对称单体函子，无需对项进行新的归纳：

 ZW22WZZ 是在着色-PROP-传递自由 PROP (ZW24WZZ) 上的 [CInterpF]；
 ZW25WZZ 是在 PROP-传递自由着色 PROP ([RepeatPROP := ColouredPROP_unit_to_PROP (FreeColouredPROP (USig S) unit_dec)]) 上的 [InterpF]。它们的严格单体包装是在那些目标上的 [CInterpF_Strict] / [InterpF_Strict] 实例；严格的对象比较是传输的类字段，即 [len_app] - 分别是 [repeat_app] - 形式的第1层等式。

 3. 往返律。在对象上，两个组合是 [length (repeat tt n) = n] ([repeat_length]) 和 [repeat tt (length l) = l] ([unit_list_eta], 需要对 [unit] 使用 eta，并且正是在这里“单色”出现)。在态射上，两次往返都是沿那些对象等式的 [hom_cast] 共轭下的恒等式：

 [LengthRepeat_roundtrip] :
 hom_cast ∘ fmap [LengthFunctor ◯ RepeatFunctor] ≈ id
 [RepeatLength_roundtrip] :
 hom_cast ∘ fmap [RepeatFunctor ◯ LengthFunctor] ≈ id每个都由相应的唯一性定理（[interp_unique2] / [cinterp_unique2]）应用到复合函子和恒等函子上来闭合，二者都严格封装（[Compose_StrictMonoidalFunctor] / [Id_StrictMonoidalFunctor]），并且通过[Construction/Quotient.v]的[id_cast]演算证明了与编织兼容的方形——复合方形坍缩，因为眼前的每个严格编织在定义上都是自由编织构造器（[Example] s [strict_braid_FreePROP_eq] 等固定了这一点）。循环往返的直接函子性是无法实现的：
 [repeat_length] 和 [unit_list_eta] 是命题性的，而非定义性的，因此共轭的 [hom_cast] 形式才是准确的陈述——与基变换定律相同的 hom_cast 共轭规范（见 [Construction/ColouredPROP/BaseChange/Laws.v] 底部的讨论）。
 从这个精确的意义上讲，有色 PROP 是 PROP 的严格广义：一个单色自由有色 PROP 与自由 PROP 通过严格的对称幺半群函子是等价的，这些函子互为逆映，直至标准严格性转换。
*)

(* * ** Layer 0: unit-colour utilities / * ** 第0层：单位颜色工具 *)

(*
   * The canonical decider for the one-point colour type.  Fixed once,
   per the one-canonical-decider discipline of
   [Construction/ColouredPROP/Instance.v] (D2): every [Cdec]-indexed
   record below names exactly this term. 

   --------
   * 单点颜色类型的规范判定器。根据 [Construction/ColouredPROP/Instance.v] (D2) 的单规范判定器原则，每个 [Cdec] 索引的记录下方正好命名了这个项。
*)
Definition unit_dec (u v : unit) : {u = v} + {u <> v} :=
  left (match u return u = v with
        | tt => match v return tt = v with
                | tt => eq_refl
                end
        end).

(*
   * Eta for unit lists: a [list unit] is determined by its length.
   This single lemma is where “one colour” does all its work — for
   any larger colour type the corresponding statement is not even
   well-posed. 

   --------
   * 单位列表的 Eta：一个 [list unit] 由其长度决定。这个单一的引理是“单色”完成其所有工作的地方 — 对于任何更大的颜色类型，相应的陈述甚至都无法准确表述。
*)
Lemma unit_list_eta (l : list unit) : repeat tt (length l) = l.
Proof.
  induction l as [| u l IH]; cbn.
  - reflexivity.
  - destruct u.
    now rewrite IH.
Qed.

(*
   * Closing move for the composite braid squares below: a doubly
   conjugated morphism equals a singly conjugated one whenever the
   conjugating cast chains compose to proofs of the same object
   equalities.  Stated in the exact association the rewrite sequence
   of the braid-square proofs produces; the two non-destructible
   residues ([b1] a domain loop, [k'] parallel to the fused codomain
   chain) are discharged by axiom-free UIP on objects. 

   --------
   * 以下复合编织方格的收尾操作：当共轭的投射链组合为相同对象等式的证明时，双共轭态射等于单共轭态射。严格按照关联方式表述，该编织方格证明的重写序列产生；两个不可破坏的剩余（[b1] 一个域循环，[k'] 与融合到值域链平行）通过对象上的无公理统一性原理（UIP）消解。
*)
Lemma braid_conj_close {C : Category} (OD : @ObjDecEq C)
  {p q t1 t2 t3 s : C}
  (k : p = t1) (a1 : t1 = t2) (b1 : t2 = p)
  (b2 : q = t3) (a2 : t3 = s) (k' : q = s)
  (f : p ~{C}~> q) :
  ((id_cast a2 ∘ ((id_cast b2 ∘ f) ∘ id_cast b1)) ∘ id_cast a1) ∘ id_cast k
    ≈ id_cast k' ∘ f.
Proof.
  destruct k, a1, b2, a2.
  rewrite (@obj_uip C OD _ _ b1 eq_refl).
  rewrite (@obj_uip C OD _ _ k' eq_refl).
  rewrite !id_cast_refl.
  now rewrite !id_left, !id_right.
Qed.

(* * ** Layer 1: the class-level transports / * ** 第1层：类级传输 *)

(*
 [length (xs ++ ys) = length xs + length ys], proven locally: the
 standard-library lemma is named [app_length] in Coq 8.19 and
 [length_app] from 8.20 onward, so the portable route across the
 supported versions is the two-line induction. 

 --------
 [length (xs ++ ys) = length xs + length ys]，本地已验证：标准库引理在 Coq 8.19 中名为 [app_length]，从 8.20 起名为 [length_app]，因此在各个支持版本中可移植的方法是采用两行归纳法。
*)
Lemma len_app {A : Type} (xs ys : list A) :
  length (xs ++ ys) = (length xs + length ys)%nat.
Proof.
  induction xs; simpl; [reflexivity|].
  now rewrite IHxs.
Qed.

(*
   * Any PROP is a [unit]-coloured PROP: keep the category and BOTH
   monoidal paths (hence the coherence proof) verbatim; name objects
   by the length of the colour word.  [length [] ≡ 0] makes the unit
   field the PROP's own, and [len_app] corrects the boundary of
   the tensor field. 

   --------
   * 任何 PROP 都是一个 [unit] 颜色的 PROP：保持类别和两个 monoidal 路径（因此保持相干性证明）原样不动；用颜色词的长度为对象命名。[length [] ≡ 0] 使单位场成为 PROP 自身的，[len_app] 修正张量场的边界。
*)
Definition PROP_to_ColouredPROP (Q : PROP) : ColouredPROP unit :=
  Build_ColouredPROP unit
    (@prop_cat Q)
    (@prop_strict Q)
    (@prop_symmetric Q)
    (@prop_monoidal_coherence Q)
    (fun cs : list unit => @prop_of_nat Q (length cs))
    (@prop_unit_zero Q)
    (fun cs ds : list unit =>
       eq_trans (@prop_tensor_plus Q (length cs) (length ds))
                (f_equal (@prop_of_nat Q) (eq_sym (len_app cs ds)))).

(*
   * Any [unit]-coloured PROP is a PROP: name objects by iterated
   [tt]-wires.  [repeat tt 0 ≡ []] makes the unit field the coloured
   PROP's own, and [repeat_app] corrects the boundary of the tensor
   field. 

   --------
   * 任何 [unit] 颜色的 PROP 都是 PROP：通过迭代的 [tt] 线路为对象命名。[repeat tt 0 ≡ [] ] 使单位场成为该颜色 PROP 自身的，而 [repeat_app] 则修正张量场的边界。
*)
Definition ColouredPROP_unit_to_PROP (Q : ColouredPROP unit) : PROP :=
  Build_PROP
    (@cprop_cat unit Q)
    (@cprop_strict unit Q)
    (@cprop_symmetric unit Q)
    (@cprop_monoidal_coherence unit Q)
    (fun n : nat => @cprop_of_list unit Q (repeat tt n))
    (@cprop_unit_nil unit Q)
    (fun m n : nat =>
       eq_trans (@cprop_tensor_app unit Q (repeat tt m) (repeat tt n))
                (f_equal (@cprop_of_list unit Q) (eq_sym (repeat_app tt m n)))).

(*
   * *** Machine-checked: the transports are structure-preserving on
   the nose.  Each [Example] is [eq_refl]. 

   --------
   * *** 机器检查：传输在鼻子上是保持结构的。每个 [Example] 都是 [eq_refl]。
*)

(** The underlying category is untouched, in both directions. / 基础类别在两个方向上均未被触及。 *)
Example PROP_to_ColouredPROP_cat (Q : PROP) :
  @cprop_cat unit (PROP_to_ColouredPROP Q) = @prop_cat Q := eq_refl.

Example ColouredPROP_unit_to_PROP_cat (Q : ColouredPROP unit) :
  @prop_cat (ColouredPROP_unit_to_PROP Q) = @cprop_cat unit Q := eq_refl.

(*
   * The strict and symmetric structures, and with them the coherence
   proof relating the two [Monoidal] paths, are passed through
   verbatim — no re-proving, no transport. 

   --------
   * 严格且对称的结构，以及与之相关的将两个 [Monoidal] 路径联系起来的连贯性证明，都被逐字通过——不重新证明，也不迁移。
*)
Example PROP_to_ColouredPROP_coherence (Q : PROP) :
  @cprop_monoidal_coherence unit (PROP_to_ColouredPROP Q)
  = @prop_monoidal_coherence Q := eq_refl.

Example ColouredPROP_unit_to_PROP_coherence (Q : ColouredPROP unit) :
  @prop_monoidal_coherence (ColouredPROP_unit_to_PROP Q)
  = @cprop_monoidal_coherence unit Q := eq_refl.

(*
   * The single wire of the transported coloured PROP is the PROP's
   1-object. 

   --------
   * 被传输的彩色PROP的单根导线是该PROP的1-对象。
*)
Example PROP_to_ColouredPROP_wire (Q : PROP) :
  wire (P := PROP_to_ColouredPROP Q) tt = @prop_of_nat Q 1 := eq_refl.

(*
   * Round-trip smoke tests on objects: at closed numerals and closed
   words the two composites compute back to the original naming
   (for a VARIABLE index the agreement is [repeat_length] /
   [unit_list_eta], which is exactly what the layer-3 morphism
   round trips conjugate along). 

   --------
   * 对对象进行往返的冒烟测试：在封闭的数字和封闭的单词上，这两个组合计算回原始命名（对于一个 VARIABLE 索引，一致性是 [repeat_length] / [unit_list_eta]，这正是第 3 层同态沿共轭进行往返的结果）。
*)
Example roundtrip_prop_of_nat_2 (Q : PROP) :
  @prop_of_nat (ColouredPROP_unit_to_PROP (PROP_to_ColouredPROP Q)) 2
  = @prop_of_nat Q 2 := eq_refl.

Example roundtrip_cprop_of_list_pair (Q : ColouredPROP unit) (u v : unit) :
  @cprop_of_list unit (PROP_to_ColouredPROP (ColouredPROP_unit_to_PROP Q))
                 [u; v]
  = @cprop_of_list unit Q [tt; tt] := eq_refl.

(* * ** Layer 2: the free-level bridge / * ** 第二层：免费的桥梁 *)

Section UnitBridge.

Context (S : Signature).

(*
   * The unit-coloured signature of a one-sorted signature: a
   generator with colour-word boundary [(cs, ds)] is a generator of
   arity [(length cs, length ds)]. 

   --------
   * 单排序符号的单元着色签名：具有颜色词边界 [(cs, ds)] 的生成元是一个范畴为 [(length cs, length ds)] 的生成元。
*)
Definition USig : CSignature unit :=
  fun cs ds : list unit => S (length cs) (length ds).

(*
   * Transport of a generator along arity equalities (the one-sorted
   mirror of the boundary transports of [Relabel.v]). 

   --------
   * 沿着元数等式传输生成器（[Relabel.v] 边界传输的一元镜像）。
*)
Definition nsig_cast {m m' n n' : nat} (em : m = m') (en : n = n')
  (g : S m n) : S m' n' :=
  match en in _ = b return S m' b with
  | eq_refl =>
      match em in _ = a return S a n with
      | eq_refl => g
      end
  end.

(*
   * [nsig_cast] is proof-irrelevant, by UIP on [nat] — no axioms. 

   --------
   *  [nsig_cast] 是与证明无关的，通过 [nat] 上的 UIP — 无公理。
*)
Lemma nsig_cast_irr {m m' n n' : nat}
  (e1 e1' : m = m') (e2 e2' : n = n') (g : S m n) :
  nsig_cast e1 e2 g = nsig_cast e1' e2' g.
Proof.
  rewrite (UIP_dec Nat.eq_dec e1 e1'), (UIP_dec Nat.eq_dec e2 e2').
  reflexivity.
Qed.

(*
   * *** The length direction

   The target of the coloured universal property is the free PROP,
   seen as a [unit]-coloured PROP through the layer-1 transport;
   its objects ARE the naturals and [cprop_of_list] IS [length]. 

   --------
   * *** 长度方向

   彩色通用性质的目标是自由PROP，通过第一层传输被视为[unit]-彩色PROP；
   它的对象是自然数，且[cprop_of_list]是[length]。
*)

Definition LengthPROP : ColouredPROP unit :=
  PROP_to_ColouredPROP (FreePROP S).

(*
   * The valuation: a [USig]-generator is by definition an [S]-
   generator at the boundary lengths, so [T_gen] applies on the
   nose. 

   --------
   * 估值：[USig]-发生器在定义上是在边界长度处的[S]-发生器，因此[T_gen]准确适用。
*)
Definition length_val : CValuation LengthPROP USig :=
  fun (cs ds : list unit) (g : USig cs ds) => T_gen g.

(*
   * The bridge functor, by the coloured universal property.  The
   side conditions of [CFreeCat S] hold at [LengthPROP] because its
   category IS [FreeCat S]: hom equivalence reflects into [Prop] by
   [FreeCat_HomEqProp], and objects are [nat] with [Nat.eq_dec]. 

   --------
   * 桥接函子，通过带颜色的泛性质。在 [LengthPROP] 处 [CFreeCat S] 的边条件成立，因为其范畴是 [FreeCat S]：同态等价通过 [FreeCat_HomEqProp] 反映到 [Prop]，且对象是 [nat] 并且具有 [Nat.eq_dec]。
*)
Definition LengthFunctor : CFreeCat USig ⟶ FreeCat S :=
  @CInterpF unit USig LengthPROP
    (FreeCat_HomEqProp S) (FreeCat_ObjDecEq S) length_val.

(*
   * Its strong/strict monoidal packagings, from [Universal.v]. 

   --------
   * 它坚固/严格的单体包装，来自 [Universal.v]。
*)
Definition LengthFunctor_Monoidal :
  @MonoidalFunctor (CFreeCat USig) (FreeCat S)
    (CFreeCat_Monoidal USig unit_dec) (FreeCat_Monoidal S) LengthFunctor :=
  @CInterpF_Monoidal unit USig unit_dec LengthPROP
    (FreeCat_HomEqProp S) (FreeCat_ObjDecEq S) length_val.

Definition LengthFunctor_Strict :
  @StrictMonoidalFunctor (CFreeCat USig) (FreeCat S)
    (CFreeCat_Monoidal USig unit_dec) (FreeCat_Monoidal S) LengthFunctor :=
  @CInterpF_Strict unit USig unit_dec LengthPROP
    (FreeCat_HomEqProp S) (FreeCat_ObjDecEq S) length_val.

Definition LengthFunctor_SymmetricStrict :
  CSymmetricStrict USig unit_dec LengthPROP
    LengthFunctor LengthFunctor_Monoidal :=
  @CInterpF_SymmetricStrict unit USig unit_dec LengthPROP
    (FreeCat_HomEqProp S) (FreeCat_ObjDecEq S) length_val.

(*
   * Machine-checked behaviour: objects go to their lengths, and
   generators are relabelled on the nose. 

   --------
   * 机器检查的行为：对象按其长度移动，生成器精确重标。
*)
Example LengthFunctor_fobj (cs : list unit) :
  fobj[LengthFunctor] cs = length cs := eq_refl.

Example LengthFunctor_gen (cs ds : list unit) (g : USig cs ds) :
  fmap[LengthFunctor] (CT_gen g) = T_gen g := eq_refl.

(*
   * The strict object comparison is the [len_app]-shaped tensor
   field of the layer-1 transport, verbatim. 

   --------
   * 严格的对象比较是层-1 传输的 [len_app] 形张量字段，逐字。
*)
Example LengthFunctor_strict_ap_obj (x y : list unit) :
  @strict_ap_obj _ _ _ _ LengthFunctor LengthFunctor_Strict x y
  = @cprop_tensor_app unit LengthPROP x y := eq_refl.

(*
   * *** The repeat direction

   The target of the one-sorted universal property is the free
   unit-coloured PROP, seen as a PROP through the layer-1 transport;
   its objects ARE the unit words and [prop_of_nat] IS
   [repeat tt]. 

   --------
   * *** 重复方向

   单一类型的普遍性质的目标是自由单位着色 PROP，通过一层传输来看作 PROP；
   它的对象是单位词，并且 [prop_of_nat] 是 [repeat tt]。
*)

Definition RepeatPROP : PROP :=
  ColouredPROP_unit_to_PROP (FreeColouredPROP USig unit_dec).

(*
   * The valuation: an [S]-generator of arity [(m, n)] becomes a
   [USig]-generator at boundary [(repeat tt m, repeat tt n)], with
   the arities corrected by [repeat_length]. 

   --------
   * 估值：一个 [S] 阵列的 [(m, n)] 阵列生成器在边界 [(repeat tt m, repeat tt n)] 处变为 [USig] 生成器，阵列通过 [repeat_length] 进行校正。
*)
Definition repeat_val : Valuation RepeatPROP S :=
  fun (m n : nat) (g : S m n) =>
    CT_gen (nsig_cast (eq_sym (repeat_length tt m))
                      (eq_sym (repeat_length tt n)) g).

(*
   * The bridge functor, by the one-sorted universal property, with
   the side conditions of [CFreeCat USig] supplied by [Instance.v]
   (the object decider is [list_eq_dec unit_dec], passed explicitly
   per the D2 discipline). 

   --------
   * 桥接函子，按照单一范畴的普遍性质，并且附带由 [Instance.v] 提供的 [CFreeCat USig] 的附加条件（对象判定器是 [list_eq_dec unit_dec]，根据 D2 规范显式传递）。
*)
Definition RepeatFunctor : FreeCat S ⟶ CFreeCat USig :=
  @InterpF S RepeatPROP
    (CFreeCat_HomEqProp USig) (CFreeCat_ObjDecEq USig unit_dec) repeat_val.

Definition RepeatFunctor_Monoidal :
  @MonoidalFunctor (FreeCat S) (CFreeCat USig)
    (FreeCat_Monoidal S) (CFreeCat_Monoidal USig unit_dec) RepeatFunctor :=
  @InterpF_Monoidal S RepeatPROP
    (CFreeCat_HomEqProp USig) (CFreeCat_ObjDecEq USig unit_dec) repeat_val.

Definition RepeatFunctor_Strict :
  @StrictMonoidalFunctor (FreeCat S) (CFreeCat USig)
    (FreeCat_Monoidal S) (CFreeCat_Monoidal USig unit_dec) RepeatFunctor :=
  @InterpF_Strict S RepeatPROP
    (CFreeCat_HomEqProp USig) (CFreeCat_ObjDecEq USig unit_dec) repeat_val.

Definition RepeatFunctor_SymmetricStrict :
  SymmetricStrict S RepeatPROP RepeatFunctor RepeatFunctor_Monoidal :=
  @InterpF_SymmetricStrict S RepeatPROP
    (CFreeCat_HomEqProp USig) (CFreeCat_ObjDecEq USig unit_dec) repeat_val.

(** Machine-checked behaviour on objects. / 在对象上的机器检查行为。 *)
Example RepeatFunctor_fobj (n : nat) :
  fobj[RepeatFunctor] n = repeat tt n := eq_refl.

(*
   * The strict object comparison is the [repeat_app]-shaped tensor
   field of the layer-1 transport, verbatim. 

   --------
   * 严格的对象比较是层-1 传输的 [repeat_app] 形张量字段，逐字。
*)
Example RepeatFunctor_strict_ap_obj (x y : nat) :
  @strict_ap_obj _ _ _ _ RepeatFunctor RepeatFunctor_Strict x y
  = @prop_tensor_plus RepeatPROP x y := eq_refl.

(*
   * *** Shared-record wiring, pinned

   Both transported targets project THE shared [Monoidal] records of
   the free instances, and their strict-path braidings are the free
   braid constructors on the nose (the coherence fields are the
   literal [eq_refl], so [transport_braid] evaporates).  These
   [Example]s are what makes the composite braid squares below close
   without ever destructing a coherence proof. 

   --------
   * *** 共享记录接线，固定

   两个传输目标都投影自由实例的共享 [Monoidal] 记录，它们的严格路径编织是精确的自由编织构造器（相干场是字面上的 [eq_refl]，因此 [transport_braid] 消失）。这些 [Example] 正是使下面的复合编织平方闭合而无需破坏相干性证明的原因。
*)

Example MPc_LengthPROP_shared :
  MPc LengthPROP = FreeCat_Monoidal S := eq_refl.

Example MP_RepeatPROP_shared :
  MP RepeatPROP = CFreeCat_Monoidal USig unit_dec := eq_refl.

Example strict_braid_FreePROP_eq (x y : nat) :
  strict_braid (FreePROP S) x y = T_braid x y := eq_refl.

Example cstrict_braid_LengthPROP_eq (x y : nat) :
  cstrict_braid LengthPROP x y = T_braid x y := eq_refl.

Example strict_braid_RepeatPROP_eq (x y : list unit) :
  strict_braid RepeatPROP x y = CT_braid x y := eq_refl.

Example cstrict_braid_FreeCPROP_eq (x y : list unit) :
  cstrict_braid (FreeColouredPROP USig unit_dec) x y = CT_braid x y
  := eq_refl.

(** ** Layer 3: the round-trip laws / ** 第三层：往返法则 *)

(*
   * The tautological valuations of the two free instances: each
   generator names itself. 

   --------
   * 两个自由实例的同义价值评估：每个生成器都命名自己。
*)
Definition taut_val : Valuation (FreePROP S) S :=
  fun (m n : nat) (g : S m n) => T_gen g.

Definition ctaut_val : CValuation (FreeColouredPROP USig unit_dec) USig :=
  fun (cs ds : list unit) (g : USig cs ds) => CT_gen g.

(* * *** Round trip on the one-sorted side / * *** 单一侧往返 *)

(*
   * The composite, packaged strictly by [Compose_StrictMonoidalFunctor]
   (its object comparisons are the [eq_trans]/[f_equal] composites of
   the two legs'). 

   --------
   * 该复合材料严格由 [Compose_StrictMonoidalFunctor] 包装（其对象比较是两个支腿的 [eq_trans] / [f_equal] 复合材料）。
*)
Definition LengthRepeat_Strict :
  @StrictMonoidalFunctor (FreeCat S) (FreeCat S)
    (FreeCat_Monoidal S) (MP (FreePROP S))
    (LengthFunctor ◯ RepeatFunctor) :=
  @Compose_StrictMonoidalFunctor (FreeCat S) (CFreeCat USig) (FreeCat S)
    (FreeCat_Monoidal S) (CFreeCat_Monoidal USig unit_dec) (MP (FreePROP S))
    LengthFunctor RepeatFunctor LengthFunctor_Strict RepeatFunctor_Strict.

(*
   * The braid-compatibility square of the composite.  Both legs send
   the free braid to a cast-conjugated free braid ([prop_braid] /
   [cbraid_hom] compute), and the target braiding is the braid
   constructor definitionally, so after pushing [fmap] through the
   casts ([fmap_id_cast]) the two sides are conjugations of the SAME
   morphism along different proofs of the same object equalities —
   closed by [braid_conj_close]. 

   --------
   * 复合的编辫兼容性方形。两条边将自由辫子送到一个铸造共轭的自由辫子（[prop_braid] / [cbraid_hom] 计算），并且目标的编辫在定义上是辫构造器，因此在将 [fmap] 经过铸造（[fmap_id_cast]）后，双方是沿相同对象等式的不同证明对同一个态射的共轭——由 [braid_conj_close] 封闭。
*)
Lemma LengthRepeat_SymmetricStrict :
  SymmetricStrict S (FreePROP S)
    (LengthFunctor ◯ RepeatFunctor) LengthRepeat_Strict.
Proof.
  intros m n.
  assert (Hap : forall x y : nat,
    to (@ap_iso _ _ _ _ (LengthFunctor ◯ RepeatFunctor)
          (@strict_functor_is_monoidal _ _ _ _
             (LengthFunctor ◯ RepeatFunctor) LengthRepeat_Strict) x y)
      ≈ id_cast (@strict_ap_obj _ _ _ _
                   (LengthFunctor ◯ RepeatFunctor) LengthRepeat_Strict x y)).
  { intros x y.
    exact (@strict_ap_iso_id _ _ _ _
             (LengthFunctor ◯ RepeatFunctor) LengthRepeat_Strict x y). }
  rewrite (Hap m n), (Hap n m).
  assert (Hsb : forall x y : nat,
             strict_braid (FreePROP S) x y = T_braid x y) by reflexivity.
  rewrite Hsb.
  (*
 Both legs compute on the braid: [interp] sends it to [prop_braid]
 and [cinterp] sends the residual [CT_braid] to [cbraid_hom], so
 the ENTIRE expansion below is one definitional equality — only
 the two [fmap]-images of stuck casts stay unreduced. 

 --------
 双腿在编织上进行计算：[interp] 将其发送到 [prop_braid]，[cinterp] 将残余的 [CT_braid] 发送到 [cbraid_hom]，因此下面的整个展开是一个定义上的等式——只有两个 [fmap] 的卡住类型映像保持未简化状态。
*)
  assert (HRL : fmap[LengthFunctor ◯ RepeatFunctor] (T_braid m n)
            = (fmap[LengthFunctor]
                 (id_cast (@prop_tensor_plus RepeatPROP n m))
                 ∘ ((id_cast (@cprop_tensor_app unit LengthPROP
                                (repeat tt n) (repeat tt m))
                       ∘ T_braid (length (repeat tt m))
                                 (length (repeat tt n)))
                      ∘ id_cast (eq_sym (@cprop_tensor_app unit LengthPROP
                                           (repeat tt m) (repeat tt n)))))
                ∘ fmap[LengthFunctor]
                    (id_cast (eq_sym (@prop_tensor_plus RepeatPROP m n))))
    by reflexivity.
  rewrite HRL.
  rewrite !fmap_id_cast.
  apply (braid_conj_close (FreeCat_ObjDecEq S)).
Qed.

(*
   * The identity competitor's braid square: its tensor comparison is
   the identity and the target braiding is the braid constructor. 

   --------
   * 恒等竞争者的编织平方：它的张量比较是恒等，而目标编织是编织构造器。
*)
Lemma Id_SymmetricStrict_free :
  SymmetricStrict S (FreePROP S) Id[FreeCat S]
    (@Id_StrictMonoidalFunctor (FreeCat S) (FreeCat_Monoidal S)).
Proof.
  intros m n.
  assert (Hap : forall x y : nat,
    to (@ap_iso _ _ _ _ Id[FreeCat S]
          (@strict_functor_is_monoidal _ _ _ _ Id[FreeCat S]
             (@Id_StrictMonoidalFunctor (FreeCat S) (FreeCat_Monoidal S)))
          x y)
      ≈ id).
  { intros x y.
    exact (@strict_ap_iso_id _ _ _ _ Id[FreeCat S]
             (@Id_StrictMonoidalFunctor (FreeCat S) (FreeCat_Monoidal S))
             x y). }
  rewrite (Hap m n), (Hap n m).
  assert (Hsb : forall x y : nat,
             strict_braid (FreePROP S) x y = T_braid x y) by reflexivity.
  rewrite Hsb.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(*
   * Generator transport against [hom_cast], in general position: with
   both arity equalities destructed the two casts are the identity. 

   --------
   * 发电机传输对抗 [hom_cast]，一般位置：当两个元数相等被破坏时，这两个强制转换是恒等的。
*)
Lemma T_gen_cast_agree {m a n b : nat} (em : m = a) (en : n = b)
  (g : S m n) :
  (T_gen (nsig_cast em en g) : a ~{FreeCat S}~> b)
    ≈ @hom_cast (FreeCat S) m n a b em en (T_gen g).
Proof.
  destruct em, en.
  reflexivity.
Qed.

(*
   * The composite agrees with the tautological valuation on
   generators: [RepeatFunctor] relabels through [nsig_cast] and
   [LengthFunctor] reads the generator back, so the residue is
   exactly [T_gen_cast_agree] at the [repeat_length] equalities. 

   --------
   * 复合与生成元上的同义评价一致：[RepeatFunctor] 通过 [nsig_cast]  重新标记，[LengthFunctor]  将生成元读回，因此在 [repeat_length]  的等式下残差正好是 [T_gen_cast_agree]。
*)
Lemma LengthRepeat_gen_agree (m n : nat) (g : S m n) :
  fmap[LengthFunctor ◯ RepeatFunctor] (T_gen g)
    ≈ @hom_cast (FreeCat S) _ _ _ _
        (eq_sym (repeat_length tt m)) (eq_sym (repeat_length tt n))
        (taut_val m n g).
Proof.
  exact (T_gen_cast_agree (eq_sym (repeat_length tt m))
                          (eq_sym (repeat_length tt n)) g).
Qed.

(*
   * The identity competitor extends the tautological valuation with
   reflexivity-grade casts. 

   --------
   * 恒等竞争者通过反身等级转换扩展了同义反复的估值。
*)
Lemma Id_gen_agree (m n : nat) (g : S m n) :
  fmap[Id[FreeCat S]] (T_gen g)
    ≈ @hom_cast (FreeCat S) _ _ _ _
        (eq_sym (@eq_refl _ (@prop_of_nat (FreePROP S) m)))
        (eq_sym (@eq_refl _ (@prop_of_nat (FreePROP S) n)))
        (taut_val m n g).
Proof.
  reflexivity.
Qed.

(*
   * THE round-trip law on the one-sorted side: going through unit
   words and back is the identity on every term, up to conjugation
   along [repeat_length].  By [interp_unique2] against the identity
   competitor. 

   --------
   * 单类型一侧的往返律：经过单位词再返回，对于每个项都是恒等律，最多沿着  [repeat_length]  共轭。通过  [interp_unique2]  对抗恒等竞争者。
*)
Theorem LengthRepeat_roundtrip (m n : nat) (t : Term S m n) :
  @hom_cast (FreeCat S) _ _ _ _
    (repeat_length tt m) (repeat_length tt n)
    (fmap[LengthFunctor ◯ RepeatFunctor] t)
    ≈ (t : m ~{FreeCat S}~> n).
Proof.
  exact (@interp_unique2 S (FreePROP S) (FreeCat_ObjDecEq S) taut_val
           (LengthFunctor ◯ RepeatFunctor) LengthRepeat_Strict
           LengthRepeat_SymmetricStrict
           (fun k : nat => repeat_length tt k)
           LengthRepeat_gen_agree
           Id[FreeCat S]
           (@Id_StrictMonoidalFunctor (FreeCat S) (FreeCat_Monoidal S))
           Id_SymmetricStrict_free
           (fun k : nat => eq_refl)
           Id_gen_agree
           m n t).
Qed.

(* * *** Round trip on the coloured side / * *** 彩色面往返 *)

Definition RepeatLength_Strict :
  @StrictMonoidalFunctor (CFreeCat USig) (CFreeCat USig)
    (CFreeCat_Monoidal USig unit_dec)
    (MPc (FreeColouredPROP USig unit_dec))
    (RepeatFunctor ◯ LengthFunctor) :=
  @Compose_StrictMonoidalFunctor (CFreeCat USig) (FreeCat S) (CFreeCat USig)
    (CFreeCat_Monoidal USig unit_dec) (FreeCat_Monoidal S)
    (MPc (FreeColouredPROP USig unit_dec))
    RepeatFunctor LengthFunctor RepeatFunctor_Strict LengthFunctor_Strict.

(** The mirror braid square, by the same cast calculus. / 镜像辫方块，通过相同的投射计算。 *)
Lemma RepeatLength_SymmetricStrict :
  CSymmetricStrict USig unit_dec (FreeColouredPROP USig unit_dec)
    (RepeatFunctor ◯ LengthFunctor) RepeatLength_Strict.
Proof.
  intros cs ds.
  assert (Hap : forall x y : list unit,
    to (@ap_iso _ _ _ _ (RepeatFunctor ◯ LengthFunctor)
          (@strict_functor_is_monoidal _ _ _ _
             (RepeatFunctor ◯ LengthFunctor) RepeatLength_Strict) x y)
      ≈ id_cast (@strict_ap_obj _ _ _ _
                   (RepeatFunctor ◯ LengthFunctor) RepeatLength_Strict x y)).
  { intros x y.
    exact (@strict_ap_iso_id _ _ _ _
             (RepeatFunctor ◯ LengthFunctor) RepeatLength_Strict x y). }
  rewrite (Hap cs ds), (Hap ds cs).
  assert (Hsb : forall x y : list unit,
             cstrict_braid (FreeColouredPROP USig unit_dec) x y
             = CT_braid x y) by reflexivity.
  rewrite Hsb.
  (*
 Mirror expansion: [cinterp] sends the braid to [cbraid_hom] and
 [interp] sends the residual [T_braid] to [prop_braid]; one
 definitional equality, with only the two [fmap]-images of stuck
 casts left standing. 

 --------
 镜像扩展：[cinterp] 将辫子发送到 [cbraid_hom]，[interp] 将残余的 [T_braid] 发送到 [prop_braid]；一个定义性等式，只剩下两个 [fmap] 的卡住类型的映像。
*)
  assert (HLR : fmap[RepeatFunctor ◯ LengthFunctor] (CT_braid cs ds)
            = (fmap[RepeatFunctor]
                 (id_cast (@cprop_tensor_app unit LengthPROP ds cs))
                 ∘ ((id_cast (@prop_tensor_plus RepeatPROP
                                (length ds) (length cs))
                       ∘ CT_braid (repeat tt (length cs))
                                  (repeat tt (length ds)))
                      ∘ id_cast (eq_sym (@prop_tensor_plus RepeatPROP
                                           (length cs) (length ds)))))
                ∘ fmap[RepeatFunctor]
                    (id_cast (eq_sym (@cprop_tensor_app unit LengthPROP
                                        cs ds))))
    by reflexivity.
  rewrite HLR.
  rewrite !fmap_id_cast.
  apply (braid_conj_close (CFreeCat_ObjDecEq USig unit_dec)).
Qed.

(** The coloured identity competitor's braid square. / 彩色身份竞争者的辫子方块。 *)
Lemma CId_SymmetricStrict_free :
  CSymmetricStrict USig unit_dec (FreeColouredPROP USig unit_dec)
    Id[CFreeCat USig]
    (@Id_StrictMonoidalFunctor (CFreeCat USig)
       (CFreeCat_Monoidal USig unit_dec)).
Proof.
  intros cs ds.
  assert (Hap : forall x y : list unit,
    to (@ap_iso _ _ _ _ Id[CFreeCat USig]
          (@strict_functor_is_monoidal _ _ _ _ Id[CFreeCat USig]
             (@Id_StrictMonoidalFunctor (CFreeCat USig)
                (CFreeCat_Monoidal USig unit_dec))) x y)
      ≈ id).
  { intros x y.
    exact (@strict_ap_iso_id _ _ _ _ Id[CFreeCat USig]
             (@Id_StrictMonoidalFunctor (CFreeCat USig)
                (CFreeCat_Monoidal USig unit_dec)) x y). }
  rewrite (Hap cs ds), (Hap ds cs).
  assert (Hsb : forall x y : list unit,
             cstrict_braid (FreeColouredPROP USig unit_dec) x y
             = CT_braid x y) by reflexivity.
  rewrite Hsb.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(*
   * Coloured generator transport against [hom_cast]: the boundary
   equalities are between colour WORDS; their [length]-images drive
   the [nsig_cast]. 

   --------
   * 彩色生成器在 [hom_cast] 上的传输：边界
   等式在颜色词之间；它们的 [length] 映像驱动
   [nsig_cast] 。
*)
Lemma CT_gen_cast_agree {cs a ds b : list unit}
  (ecs : cs = a) (eds : ds = b) (g : USig cs ds) :
  (CT_gen (nsig_cast (f_equal (@length unit) ecs)
                     (f_equal (@length unit) eds) g)
     : a ~{CFreeCat USig}~> b)
    ≈ @hom_cast (CFreeCat USig) cs ds a b ecs eds (CT_gen g).
Proof.
  destruct ecs, eds.
  reflexivity.
Qed.

(*
   * The coloured composite agrees with the tautological valuation on
   generators.  The computed [nsig_cast] rides [repeat_length] while
   the canonical conjugation rides [unit_list_eta]; the two are
   proofs of the same [nat] equalities, identified by
   [nsig_cast_irr] (UIP on [nat]). 

   --------
   * 有色复合体在生成元上的取值与重言式赋值一致。计算得到的 [nsig_cast] 骑在 [repeat_length] 上，而典范共轭骑在 [unit_list_eta] 上；这两者是相同 [nat] 等式的证明，由 [nsig_cast_irr]（在 [nat] 上的 UIP）所识别。
*)
Lemma RepeatLength_gen_agree (cs ds : list unit) (g : USig cs ds) :
  fmap[RepeatFunctor ◯ LengthFunctor] (CT_gen g)
    ≈ @hom_cast (CFreeCat USig) _ _ _ _
        (eq_sym (unit_list_eta cs)) (eq_sym (unit_list_eta ds))
        (ctaut_val cs ds g).
Proof.
  assert (Hg : fmap[RepeatFunctor ◯ LengthFunctor] (CT_gen g)
           = CT_gen (nsig_cast (eq_sym (repeat_length tt (length cs)))
                               (eq_sym (repeat_length tt (length ds))) g))
    by reflexivity.
  rewrite Hg.
  rewrite (nsig_cast_irr
             (eq_sym (repeat_length tt (length cs)))
             (f_equal (@length unit) (eq_sym (unit_list_eta cs)))
             (eq_sym (repeat_length tt (length ds)))
             (f_equal (@length unit) (eq_sym (unit_list_eta ds))) g).
  exact (CT_gen_cast_agree (eq_sym (unit_list_eta cs))
                           (eq_sym (unit_list_eta ds)) g).
Qed.

(*
   * The coloured identity competitor extends the tautological
   valuation with reflexivity-grade casts. 

   --------
   * 彩色身份竞争者通过反身性等级转换扩展了同义评价。
*)
Lemma CId_gen_agree (cs ds : list unit) (g : USig cs ds) :
  fmap[Id[CFreeCat USig]] (CT_gen g)
    ≈ @hom_cast (CFreeCat USig) _ _ _ _
        (eq_sym (@eq_refl _ (@cprop_of_list unit
                               (FreeColouredPROP USig unit_dec) cs)))
        (eq_sym (@eq_refl _ (@cprop_of_list unit
                               (FreeColouredPROP USig unit_dec) ds)))
        (ctaut_val cs ds g).
Proof.
  reflexivity.
Qed.

(*
   * THE round-trip law on the coloured side: going through lengths
   and back is the identity on every term, up to conjugation along
   [unit_list_eta].  By [cinterp_unique2] against the identity
   competitor. 

   --------
   * 彩色一侧的往返定律：经过某个长度再返回，在每个项上都是恒等的，直到沿着 [unit_list_eta] 的共轭。通过 [cinterp_unique2] 对抗恒等竞争者。
*)
Theorem RepeatLength_roundtrip (cs ds : list unit)
  (t : CTerm USig cs ds) :
  @hom_cast (CFreeCat USig) _ _ _ _
    (unit_list_eta cs) (unit_list_eta ds)
    (fmap[RepeatFunctor ◯ LengthFunctor] t)
    ≈ (t : cs ~{CFreeCat USig}~> ds).
Proof.
  exact (@cinterp_unique2 unit USig unit_dec
           (FreeColouredPROP USig unit_dec)
           (CFreeCat_ObjDecEq USig unit_dec) ctaut_val
           (RepeatFunctor ◯ LengthFunctor) RepeatLength_Strict
           RepeatLength_SymmetricStrict
           (fun ks : list unit => unit_list_eta ks)
           RepeatLength_gen_agree
           Id[CFreeCat USig]
           (@Id_StrictMonoidalFunctor (CFreeCat USig)
              (CFreeCat_Monoidal USig unit_dec))
           CId_SymmetricStrict_free
           (fun ks : list unit => eq_refl)
           CId_gen_agree
           cs ds t).
Qed.

(*
   * Object-level round trips, for the record: the composites act on
   objects exactly as [length ∘ repeat tt] and [repeat tt ∘ length],
   so the conjugating equalities above are precisely the two halves
   of the [list unit ≃ nat] bijection. 

   --------
   * 对象级往返，供参考：复合体对对象的作用与  [length ∘ repeat tt]  和  [repeat tt ∘ length]  完全相同，因此上面的共轭等式正好是  [list unit ≃ nat]  双射的两个部分。
*)
Example LengthRepeat_fobj (n : nat) :
  fobj[LengthFunctor ◯ RepeatFunctor] n = length (repeat tt n) := eq_refl.

Example RepeatLength_fobj (cs : list unit) :
  fobj[RepeatFunctor ◯ LengthFunctor] cs = repeat tt (length cs) := eq_refl.

End UnitBridge.

Arguments USig S _ _ : assert.
Arguments LengthPROP S : assert.
Arguments LengthFunctor S : assert.
Arguments RepeatPROP S : assert.
Arguments RepeatFunctor S : assert.
Arguments LengthRepeat_roundtrip S m n t : assert.
Arguments RepeatLength_roundtrip S cs ds t : assert.
