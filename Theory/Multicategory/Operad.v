Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Multicategory.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Operads as one-object multicategories / * 作为单对象多重范畴的操作范畴 *)

(*
nLab: https://ncatlab.org/nlab/show/operad

   An operad is a multicategory with a single object (colour), so that a
   multimorphism is determined by the ARITY of its source list alone.

   BUNDLING.  The one-object condition is recorded as the propositional
   equality [IsOperad M := @mobj M = poly_unit] — [=] on the Type-level
   object data of the multicategory, never on morphisms — bundled as a
   record ([Operad]).  Downstream consumers (operad algebras as
   multifunctors into the endomorphism multicategory of an object, whose
   colour type is [poly_unit] DEFINITIONALLY) only need the underlying
   multicategory, which the projection [operad_multi] exposes.

   THE DERIVED POINT.  Rather than transporting hom-sets along
   [operad_one], every accessor is phrased over the derived point
   [operad_pt O : mobj] (the transport of [ttt] backwards along
   [operad_one]).  Object contractibility [operad_obj_contr] — every
   object equals the point — is derived with no UIP: the transport
   lemma is proved by destructing an equality whose right endpoint is a
   variable.  For an instance whose colour type is [poly_unit]
   definitionally (so [operad_one := eq_refl]), [operad_pt] reduces to
   [ttt] and [ohom n] reduces to [mhom (repeat ttt n) ttt], with no
   transport anywhere.

   ARITY ACCESSORS.  [ohom n := mhom (repeat pt n) pt] is the setoid of
   n-ary operations; [oid] is the unary identity; [ocomp] is the
   single-slot operadic composition [∘ᵢ], obtained from the zipper
   [mcomp] at [Γ1 := repeat pt i], [Γ2 := repeat pt j], recast along the
   transparent [repeat]-arithmetic kit ([repeat_app_t]).  The
   symmetric-group action restricts to self-permutations of
   [repeat pt n]: the witnesses are the Type-valued [tperm] of
   Theory/Multicategory.v (the class's own index; the stdlib
   [Permutation] is recoverable through [tperm_Permutation]).

   THE ROUND TRIP.  Every list of objects of an operad is a [repeat] of
   the point ([all_repeat], by induction from contractibility), so every
   multimorphism [mhom Γ pt] is an [ohom (length Γ)] up to [mcast]; the
   two directions ([to_ohom]/[of_ohom]) compose to the identity up to
   [≈] by the [mcast] groupoid pack ([operad_roundtrip],
   [operad_roundtrip_inv]).

--------
nLab：https://ncatlab.org/nlab/show/operad

算子范畴是一个具有单一对象（颜色）的多重范畴，因此一个多重态射仅由其源列表的元数决定。

捆绑。单对象条件被记录为多重范畴的类型级对象数据上的命题等式 [IsOperad M := @mobj M = poly_unit] — [=]，而从不记录在态射上——作为一个记录（[Operad]）捆绑在一起。下游使用者（作为多函子指向某对象自同态多重范畴的运算代数，其颜色类型在定义上为 [poly_unit]）只需要底层的多重范畴，而投影 [operad_multi] 将其公开。

派生点。不是沿着 [operad_one] 传输同态集，每个访问器都表述于派生点 [operad_pt O : mobj]（[ttt] 沿 [operad_one] 向后传输）。对象可收缩性 [operad_obj_contr]——每个对象等于该点——在没有 UIP 的情况下得出：传输引理通过析构其右端点为变量的等式来证明。对于定义类型为 [poly_unit]（因此 [operad_one := eq_refl]）的实例，[operad_pt] 归约为 [ttt]，[ohom n] 归约为 [mhom (repeat ttt n) ttt]，并且没有任何传输。

多元访问器。[ohom n := mhom (repeat pt n) pt] 是 n 元运算的集合；[oid] 是一元恒等；[ocomp] 是单槽 operadic 组合 [∘ᵢ]，由 [mcomp] 上的拉链在 [Γ1 := repeat pt i]、[Γ2 := repeat pt j] 处获得，并沿透明的 [repeat] 算术套件 ([repeat_app_t]) 重新构造。对称群作用限制在 [repeat pt n] 的自排列上：证人是 Theory/Multicategory.v 中类型值的 [tperm]（类本身的索引；标准库中的 [Permutation] 可通过 [tperm_Permutation] 恢复）。

往返行程。每个操作器对象的列表都是一个点的[repeat]（通过可收缩性归纳得出[all_repeat]），所以每个多态射[mhom Γ pt]都是一个[ohom (length Γ)]，直到[mcast]；两个方向（[to_ohom]/[of_ohom]）通过[mcast]群体包（[operad_roundtrip]，[operad_roundtrip_inv]）组成到恒等映射，直到[≈]。
*)

(** ** The transport helper and the bundled record / ** 运输助手和捆绑记录 *)

(*
Transport an inhabitant of [poly_unit] along a Type equality.  Stated
   with the equality oriented [poly_unit = A] so that the contractibility
   lemma below can destruct it (the right endpoint is a variable).

--------
沿着类型等式传输 [poly_unit] 的一个居民。使用面向等式的 [poly_unit = A] 陈述，以便下面的可收缩性引理可以对其进行析构（右端点是一个变量）。
*)
Definition unit_transport {A : Type} (e : poly_unit = A) : A :=
  match e in _ = T return T with eq_refl => ttt end.

(*
Any type equal to [poly_unit] is contractible onto the transported
   point.  No UIP: [destruct e] abstracts the variable endpoint, and
   [poly_unit] has a single constructor.

--------
任何等于 [poly_unit] 的类型都可以收缩到传输的点上。没有 UIP：[destruct e] 抽象了变量端点，而 [poly_unit] 只有一个构造函数。
*)
Lemma unit_transport_contr {A : Type} (e : poly_unit = A) (x : A) :
  x = unit_transport e.
Proof.
  destruct e.
  now destruct x.
Qed.

(* The one-object condition: [=] on the Type-level colour data. / 单对象条件：Type级别颜色数据上的 [=]。 *)
Definition IsOperad (M : Multicategory) : Type :=
  @mobj M = poly_unit.

Record Operad : Type := {
  operad_multi : Multicategory;
  operad_one : IsOperad operad_multi
}.

(** ** The derived point and object contractibility / ** 导出点和对象的可收缩性 *)

(*
The unique colour of the operad.  When [operad_one] is [eq_refl]
   (colour type [poly_unit] on the nose), this reduces to [ttt].

--------
操作器的独特颜色。当 [operad_one] 是 [eq_refl]（鼻子上的颜色类型 [poly_unit]）时，这会减少到 [ttt]。
*)
Definition operad_pt (O : Operad) : @mobj (operad_multi O) :=
  unit_transport (eq_sym (operad_one O)).

(* Every object of an operad is the point. / 一个运算子的每一个对象都是点。 *)
Lemma operad_obj_contr (O : Operad) (x : @mobj (operad_multi O)) :
  x = operad_pt O.
Proof.
  apply unit_transport_contr.
Qed.

(*
Every LIST of objects of an operad is a [repeat] of the point: the
   list-level face of contractibility, and the equality along which the
   round trip below recasts.  [Defined] so the [f_equal2] spine computes
   on list constructors; its leaves ([operad_obj_contr], hence
   [unit_transport_contr]) are opaque, so full reduction stops there —
   no consumer needs more (the casts ride the class's groupoid pack).

--------
一个算子的每个对象列表都是一个点的 [repeat]：可收缩性的列表级面，以及下面回程重新构造的相等性。[Defined]，所以 [f_equal2] 脊柱在列表构造器上进行计算；它的叶子（[operad_obj_contr]，因此 [unit_transport_contr]）是不透明的，所以完全化简在那里停止——没有使用者需要更多（转换依附于类的群组包）。
*)
Definition all_repeat (O : Operad) (Γ : list (@mobj (operad_multi O))) :
  Γ = repeat (operad_pt O) (length Γ).
Proof.
  induction Γ as [|a Γ IH]; simpl.
  - reflexivity.
  - exact (f_equal2 cons (operad_obj_contr O a) IH).
Defined.

(**
** The transparent repeat-arithmetic kit

    The stdlib's [repeat_app] is stated with the concatenation on the
    right and is opaque in some supported versions; the accessors below
    need a proof that COMPUTES on [nat] constructors, so a transparent
    Fixpoint is defined here (the [map_app_t] pattern of
    Theory/Multicategory/Functor.v).

--------
** 透明的重复算术工具包

    stdlib 的 [repeat_app] 在右侧声明了连接，并且在一些支持的版本中是不透明的；下面的访问器需要一个关于 [nat] 构造函数上 COMPUTES 的证明，所以这里定义了一个透明的 Fixpoint（Theory/Multicategory/Functor.v 中的 [map_app_t] 模式）。
*)

Fixpoint repeat_app_t {A : Type} (x : A) (m n : nat) :
  repeat x (m + n) = repeat x m ++ repeat x n :=
  match m with
  | O => eq_refl
  | S m' => f_equal (cons x) (repeat_app_t x m' n)
  end.

(** ** Arity accessors / ** 元数访问器 *)

Section OperadAccessors.

Context (O : Operad).

Local Notation MO := (operad_multi O).
Local Notation pt := (operad_pt O).

(* The setoid of n-ary operations. / n 元运算的等值结构。 *)
Definition ohom (n : nat) : Type := @mhom MO (repeat pt n) pt.

#[export] Instance ohom_setoid (n : nat) : Setoid (ohom n) :=
  @mhomset MO (repeat pt n) pt.

(* The unary identity operation: [repeat pt 1] is [[pt]] on the nose. / 一元恒等运算：[repeat pt 1] 就是 [[pt]]。 *)
Definition oid : ohom 1 := @mid MO pt.

(**
*** The round trip

    Every multimorphism of the underlying multicategory whose target is
    the point is an n-ary operation, [n := length Γ], by recasting along
    [all_repeat]; the two directions cancel up to [≈] by the [mcast]
    groupoid pack.

--------
*** 往返行程

    每个以点为目标的底层多范畴的多态映射都是一个 n 元运算，[n := length Γ]，通过沿着 [all_repeat] 重新表达；通过 [mcast] 群体包，两种方向在 [≈] 上抵消。
*)

Definition to_ohom {Γ : list (@mobj MO)} (f : @mhom MO Γ pt) :
  ohom (length Γ) :=
  @mcast MO _ _ pt (all_repeat O Γ) f.

Definition of_ohom {Γ : list (@mobj MO)} (g : ohom (length Γ)) :
  @mhom MO Γ pt :=
  @mcast MO _ _ pt (eq_sym (all_repeat O Γ)) g.

#[export] Instance to_ohom_respects {Γ : list (@mobj MO)} :
  Proper (equiv ==> equiv) (@to_ohom Γ).
Proof. apply mcast_respects. Qed.

#[export] Instance of_ohom_respects {Γ : list (@mobj MO)} :
  Proper (equiv ==> equiv) (@of_ohom Γ).
Proof. apply mcast_respects. Qed.

Lemma operad_roundtrip {Γ : list (@mobj MO)} (f : @mhom MO Γ pt) :
  of_ohom (to_ohom f) ≈ f.
Proof. apply mcast_symm_l. Qed.

Lemma operad_roundtrip_inv {Γ : list (@mobj MO)} (g : ohom (length Γ)) :
  to_ohom (of_ohom g) ≈ g.
Proof. apply mcast_symm_r. Qed.

(**
*** Single-slot operadic composition

    The classical [∘ᵢ]: splice an n-ary operation into the (i+1)-st
    input of an (i + 1 + j)-ary operation, yielding an
    (i + (n + j))-ary operation.  The zipper of Theory/Multicategory.v
    is instantiated at [Γ1 := repeat pt i], [Γ2 := repeat pt j], and
    the boundary lists are renormalised to [repeat] form along the
    transparent arithmetic kit.

--------
*** 单槽运算子组合

    经典的 [∘ᵢ]：将一个 n 元运算嵌入到一个 (i + 1 + j) 元运算的第 (i+1) 个输入中，从而得到一个 (i + (n + j)) 元运算。Theory/Multicategory.v 中的拉链在 [Γ1 := repeat pt i]、[Γ2 := repeat pt j] 处实例化，并且边界列表沿着透明算术工具包被重新标准化为 [repeat] 形式。
*)

(*
The zipper form of a repeated context: [repeat pt (S j)] is
   [pt :: repeat pt j] on the nose, so [repeat_app_t] already has the
   stated type up to conversion.

--------
重复上下文的拉链形式：[repeat pt (S j)] 在鼻子上是 [pt :: repeat pt j]，因此 [repeat_app_t] 已经具有转换前所述的类型。
*)
Definition orep_zip (i j : nat) :
  repeat pt (i + S j) = repeat pt i ++ pt :: repeat pt j :=
  repeat_app_t pt i (S j).

(* Renormalising a three-block spliced context to [repeat] form. / 将三块拼接的上下文重新归一化为 [repeat] 形式。 *)
Definition orep_splice (i n j : nat) :
  repeat pt i ++ repeat pt n ++ repeat pt j = repeat pt (i + (n + j)) :=
  eq_sym (eq_trans (repeat_app_t pt i (n + j))
                   (f_equal (app (repeat pt i)) (repeat_app_t pt n j))).

Definition ocomp {i j n : nat} (f : ohom (i + S j)) (g : ohom n) :
  ohom (i + (n + j)) :=
  @mcast MO _ _ pt (orep_splice i n j)
    (@mcomp MO (repeat pt i) (repeat pt j) (repeat pt n) pt pt
       (@mcast MO _ _ pt (orep_zip i j) f) g).

#[export] Instance ocomp_respects {i j n : nat} :
  Proper (equiv ==> equiv ==> equiv) (@ocomp i j n).
Proof.
  intros f f' ef g g' eg; unfold ocomp.
  now rewrite ef, eg.
Qed.

(**
*** The symmetric-group action on arities

    Self-permutations of the repeated context [repeat pt n] act on
    n-ary operations.  The witnesses are the Type-valued [tperm] of
    Theory/Multicategory.v — the index of the class's own action; the
    stdlib [Permutation (repeat pt n) (repeat pt n)] proposition is
    recoverable through [tperm_Permutation].  The identity law is
    pinned to the canonical [tperm_refl] witness, and functoriality is
    along the [tperm_trans] constructor, exactly as in the class.

--------
*** 对元数的对称群作用

    重复上下文 [repeat pt n] 的自排列作用于 n 元操作。证据是 Theory/Multicategory.v 中的类型值 [tperm]——类自身作用的索引；标准库 [Permutation (repeat pt n) (repeat pt n)] 命题可以通过 [tperm_Permutation] 恢复。恒等律固定在规范的 [tperm_refl] 证据上，函子性沿着 [tperm_trans] 构造器，正如类中一样。
*)

Definition osym {n : nat} (p : tperm (repeat pt n) (repeat pt n)) :
  ohom n → ohom n :=
  @msym MO _ _ pt p.

#[export] Instance osym_respects {n : nat}
  (p : tperm (repeat pt n) (repeat pt n)) :
  Proper (equiv ==> equiv) (@osym n p).
Proof. apply msym_respects. Qed.

Lemma osym_id {n : nat} (f : ohom n) :
  osym (tperm_refl (repeat pt n)) f ≈ f.
Proof. apply msym_id. Qed.

Lemma osym_compose {n : nat} (p q : tperm (repeat pt n) (repeat pt n))
  (f : ohom n) :
  osym q (osym p f) ≈ osym (tperm_trans p q) f.
Proof. apply msym_compose. Qed.

End OperadAccessors.

