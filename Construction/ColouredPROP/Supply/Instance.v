Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Comonoid.Tensor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Presentation.
Require Import Category.Construction.ColouredPROP.Supply.
Require Import Category.Construction.ColouredPROP.Linear.

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Bool.Bool.
From Coq Require Import Eqdep_dec.
(*
 [Morphisms] (the [Prop]-relation generalized-rewriting classes) powers
 the [rewrite]s over the [Prop]-valued congruence [CTermEqW] in the
 singleton-collapse theorems below; the library's own crelation-based
 kit (Lib/Setoid.v) does not apply to raw [CTerm] formers. 

 --------
 [Morphisms]（[Prop]-关系广义重写类）作用于单例塌缩定理中 [Prop] 值同余 [CTermEqW] 上的 [rewrite]；库自身基于 crelation 的工具包（Lib/Setoid.v）不适用于原始 [CTerm] 生成元。
*)
From Coq Require Import Morphisms.

Generalizable All Variables.

(*
   * * The free selective supply: a presented coloured PROP with
   per-wire duplicators and deleters 

   --------
   * * 免费的选择性供应：一个带有每线复制器和删除器的呈现彩色道具
*)

(*
 nLab:      https://ncatlab.org/nlab/show/PROP
 nLab:      https://ncatlab.org/nlab/show/comonoid
 nLab:      https://ncatlab.org/nlab/show/generators+and+relations
 Reference: Fong & Spivak, "Supplying bells and whistles in symmetric
 monoidal categories" (arXiv:1908.02633)

 This file builds the free SUPPLIED coloured PROP on a signature: a
 base signature [S] is extended with WIRE-LEVEL generators — one
 duplicator [SG_dup c : [c] -> [c; c]] and one deleter
 [SG_del c : [c] -> []] for every colour the boolean predicate
 [copyable] marks as duplicable — and quotiented by the per-wire
 commutative-comonoid equations [SupplyEqs].  The result
 [SupplyPROP] is the library's THIRD inhabitant of
 [Construction/ColouredPROP.v]'s class (after [FreeColouredPROP]
 and the generic [CPresentedColouredPROP] it instantiates), and it
 carries a [SelectiveSupply] structure in the sense of
 [Construction/ColouredPROP/Supply.v]: every copyable wire's dup and
 del descend to a commutative comonoid in the quotient.

 Design decision, recorded: the generators are WIRE-level ONLY.  A
 comonoid on a composite boundary [cs] is not axiomatised; it is
 DERIVED by tensoring wire comonoids ([supply_list] of Supply.v,
 powered by the packaged tensor/unit comonoids of
 Theory/Algebra/Comonoid/Tensor.v).  This avoids any
 boundary-compatibility axiom family (e.g. a dup-on-append
 equation) and the cast-spelling pitfalls such axioms invite.

 The four [SupplyEqs] constructors are stated in the EXACT
 cast-normal shapes the [Comonoid]/[CommutativeComonoid] record
 fields reduce to at [CPresented_Monoidal] (checked by cbn, as for
 [CPresented_Strict] in Presentation.v):

 - coassociativity carries the single [app_assoc [c] [c] [c]]
 cast — the [from] of the presented associator;
 - the LEFT counit law is cast-free on the axiom side
 ([[] ++ [c]] is definitional), and the field's residual
 left-unitor cast [CT_cast (eq_sym (app_nil_l [c]))] is
 eliminated by [CT_cast_id] under [Cdec];
 - the RIGHT counit law carries the [app_nil_r [c]] cast — the
 [from] of the presented right unitor, [CT_cast (eq_sym
 (app_nil_r [c]))] — on its right-hand side, which IS the
 field's normal form (no massage needed);
 - cocommutativity is cast-free ([CT_braid [c] [c]] is the
 presented braid on the nose).

 The fan-out corollaries at the foot of the file are the categorical
 content of the linear fan-out check: over a base signature that is
 conservative at a non-copyable colour [c], the hom-set
 [[c] ~> [c; c]] of [SupplyPROP] is EMPTY (no axiom can create a
 fan-out that no term realises), while for copyable [c] the
 generator itself inhabits it.  Over the PURE supply PROP (base
 signature [Empty_CSig]) this becomes an exact characterisation:
 [[c] ~> [c; c]] is inhabited iff [copyable c = true]
 ([fanout_iff]). 

 --------
 nLab：       https://ncatlab.org/nlab/show/PROP 
 nLab：       https://ncatlab.org/nlab/show/comonoid 
 nLab：       https://ncatlab.org/nlab/show/generators+and+relations 
 参考文献：Fong & Spivak，《在对称单体范畴中提供铃声和口哨声》(arXiv:1908.02633)该文件在一个签名上构建了自由的提供的彩色 PROP：一个基础签名 [S] 被 WIRE-LEVEL 生成器扩展——每种布尔谓词 [copyable] 标记为可复制的颜色都对应一个复制器 [SG_dup c : [c] -> [c; c] 和一个删除器 [SG_del c : [c] -> []]——并按每根线的交换余子式等式 [SupplyEqs] 取商。结果 [SupplyPROP] 是库中 [Construction/ColouredPROP.v] 类的第三个元素（在 [FreeColouredPROP] 和它实例化的通用 [CPresentedColouredPROP] 之后），并且它以 [Construction/ColouredPROP/Supply.v] 的意义承载 [SelectiveSupply] 结构：每根可复制的线的复制和删除在商中降至一个交换余子式。设计决策，已记录：生成器仅为线级（WIRE-level）。复合边界 [cs] 上的 comonoid 并未被公理化；它是通过张量线级 comonoid（Supply.v 中的 [supply_list]，由 Theory/Algebra/Comonoid/Tensor.v 封装的张量/单位 comonoid 提供支持）推导出来的。这避免了任何边界兼容性公理族（例如 append 上的 dup 方程）以及这种公理容易引起的类型转换拼写陷阱。

 四个 [SupplyEqs] 构造函数以 EXACT cast-normal 形状表述，这是 [Comonoid] / [CommutativeComonoid] 记录字段在 [CPresented_Monoidal] 下归约的形状（通过 cbn 检查，就像 Presentation.v 中的 [CPresented_Strict] 一样）：- 共结合性携带单个 [app_assoc [c] [c] [c] ]
 cast —— 所呈现的结合子 [from] ;
 - 左单位元律在公理端上没有 cast
 ( [[] ++ [c] ] 是定义上的)，且域的剩余
 左单位元 cast [CT_cast (eq_sym (app_nil_l [c] ))] 被 [CT_cast_id] 在 [Cdec] 下消除；
 - 右单位元律携带 [app_nil_r [c] ] cast —— 所呈现的右单位元 [from] ，[CT_cast (eq_sym
 (app_nil_r [c] ))] —— 在其右侧，该右侧即为
 域的正规形式（无需额外处理）；
 - 余交换性没有 cast（ [CT_braid [c] [c] ] 是
 所呈现的编织变换（braid）原封不动）。文件底部的扇出推论是线性扇出检查的类别内容：在非可复制颜色 [c] 上是保守的基础签名下，[SupplyPROP] 的同态集 [[c]  ~>  [c; c] ] 是空的（没有公理可以创建没有项实现的扇出），而对于可复制的 [c]，生成器本身就属于该集。在 PURE supply PROP（基础签名 [Empty_CSig]）上，这变成了一个精确的表征：[[c]  ~>  [c; c] ] 当且仅当 [copyable c = true] ([fanout_iff]) 时是被占用的。
*)

Section SupplyInstance.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (S : CSignature Colour).
Context (copyable : Colour -> bool).

(*
   * ** The supply generators

   Wire-level only: one duplicator and one deleter per COPYABLE
   colour.  The copyability witness is carried by the generator, so
   non-copyable colours index no generators at all. 

   --------
   * ** 供应生成器

   仅限线路级别：每种可复制颜色有一个复制器和一个删除器。
   可复制性的证明由生成器携带，因此不可复制的颜色完全不对应任何生成器。
*)

Inductive SupplyGen : list Colour -> list Colour -> Type :=
  | SG_dup (c : Colour) : copyable c = true -> SupplyGen [c] [c; c]
  | SG_del (c : Colour) : copyable c = true -> SupplyGen [c] [].

(*
   * The extended signature: base generators plus supply generators. 

   --------
   * 扩展签名：基础发生器加供应发生器。
*)
Definition SupplyExtSig : CSignature Colour := Sum_CSig S SupplyGen.

(*
   * The generators as terms.  [[c] ++ [c] ≡ [c; c]] definitionally,
   so [sg_dup] also inhabits the tensor-shaped boundary on the
   nose. 

   --------
   * 作为项的生成元。   [[c]  ++  [c]  ≡  [c; c] ] 根据定义，
   因此  [sg_dup]  也位于张量形边界上，在鼻子处。
*)
Definition sg_dup (c : Colour) (H : copyable c = true) :
  CTerm SupplyExtSig [c] [c; c] :=
  CT_gen (inr (SG_dup c H)).

Definition sg_del (c : Colour) (H : copyable c = true) :
  CTerm SupplyExtSig [c] [] :=
  CT_gen (inr (SG_del c H)).

(*
   * ** The supply equations

   Per-wire commutative-comonoid axioms, and NOTHING else — no
   boundary-level equation is assumed (see the header).  Each
   constructor is stated in the cbn-normal shape of the record field
   it will discharge. 

   --------
   * ** 供给方程

   每根线的交换-余幺半群公理，仅此而已——没有假设任何边界级方程（见标题）。每个构造函数都以它将要释放的记录字段的 cbn-标准形态给出。
*)

Inductive SupplyEqs : forall cs ds : list Colour,
    CTerm SupplyExtSig cs ds -> CTerm SupplyExtSig cs ds -> Prop :=

  (*
   * Coassociativity.  The right-hand side carries the [from] of the
   presented associator at [([c], [c], [c])]: the single
   [app_assoc [c] [c] [c]] cast. 

   --------
   * 余结合性。右侧携带在 [([c]、[c]、[c] 处给出的结合子 [from]）：单个 [app_assoc [c] [c] [c]] 转换。
*)
  | SE_coassoc (c : Colour) (H : copyable c = true) :
      SupplyEqs [c] [c; c; c]
        (CT_comp (CT_tens (sg_dup c H) (CT_id [c])) (sg_dup c H))
        (CT_comp (CT_comp (CT_cast (app_assoc [c] [c] [c]))
                          (CT_tens (CT_id [c]) (sg_dup c H)))
                 (sg_dup c H))

  (*
   * Left counit law.  Cast-free: [[] ++ [c] ≡ [c]] definitionally,
   so deleting the left copy is the identity wire on the nose. 

   --------
   * 左余单位律。无类型转换：[[] ++ [c] ≡ [c] 根据定义，
   因此删除左侧副本就是完全的恒等线。
*)
  | SE_counit_left (c : Colour) (H : copyable c = true) :
      SupplyEqs [c] [c]
        (CT_comp (CT_tens (sg_del c H) (CT_id [c])) (sg_dup c H))
        (CT_id [c])

  (*
   * Right counit law.  The right-hand side carries the [from] of
   the presented right unitor at [[c]]: the
   [eq_sym (app_nil_r [c])] cast (a stuck endo-cast, since
   [[c] ++ [] ≡ [c]] definitionally but [app_nil_r] is opaque). 

   --------
   * 右余单位律。右侧承载了在 [[c] 的所呈现的右单位子器 [from] ]：[eq_sym (app_nil_r [c] )] 转换（一个卡住的自端转换，因为 [[c] ++ [] ≡ [c] ] 从定义上，但 [app_nil_r] 是不透明的）。
*)
  | SE_counit_right (c : Colour) (H : copyable c = true) :
      SupplyEqs [c] [c]
        (CT_comp (CT_tens (CT_id [c]) (sg_del c H)) (sg_dup c H))
        (CT_cast (eq_sym (app_nil_r [c])))

  (*
   * Cocommutativity.  Cast-free: [CT_braid [c] [c]] is the
   presented braid on the nose. 

   --------
   * 共交换性。无铸造：[CT_braid [c] [c]] 是所展示的编织图案。
*)
  | SE_cocomm (c : Colour) (H : copyable c = true) :
      SupplyEqs [c] [c; c]
        (CT_comp (CT_braid [c] [c]) (sg_dup c H))
        (sg_dup c H).

(* * ** The theory and its presented coloured PROP / * **理论及其呈现的彩色 PROP *)

Definition SupplySMT : CSMT Colour :=
  Build_CSMT Colour SupplyExtSig SupplyEqs.

(** The THIRD [ColouredPROP] instance of the library. / 该库的第三个 [ColouredPROP] 实例。 *)
Definition SupplyPROP : ColouredPROP Colour :=
  CPresentedColouredPROP SupplySMT Cdec.

(** The generators, as morphisms of [SupplyPROP]. / 作为 [SupplyPROP] 的态射的生成元。 *)
Definition SupplyPROP_dup (c : Colour) (H : copyable c = true) :
  ([c] : list Colour) ~{CPresentedCat SupplySMT}~> [c; c] :=
  cquot SupplySMT (sg_dup c H).

Definition SupplyPROP_del (c : Colour) (H : copyable c = true) :
  ([c] : list Colour) ~{CPresentedCat SupplySMT}~> [] :=
  cquot SupplySMT (sg_del c H).

(*
   * ** The wire comonoid laws

   Standalone law lemmas, each in the EXACT normal form of the
   record field it discharges; three of the four are
   verbatim [CTEW_ax] embeddings of the axioms, and the left counit
   law additionally eliminates the field's stuck left-unitor cast
   with [CT_cast_id] (list-UIP under [Cdec]). 

   --------
   * ** 线性余单子定律

   独立定律引理，每一个都处于它所解除的记录字段的完全标准形式；四条定律中有三条是公理的逐字 [CTEW_ax] 嵌入，而左辅单位元定律还通过 [CT_cast_id] 消除了该字段卡住的左单位元类型转换（在 [Cdec] 下的列表 UIP）。
*)

(*
   * Coassociativity, in the shape of [delta_coassoc] at
   [CPresented_Monoidal SupplySMT Cdec]. 

   --------
   * 共结合性，在 [CPresented_Monoidal SupplySMT Cdec] 处呈现为 [delta_coassoc] 的形状。
*)
Definition supply_wire_coassoc (c : Colour) (H : copyable c = true) :
  CTermEqW SupplySMT
    (CT_comp (CT_tens (sg_dup c H) (CT_id [c])) (sg_dup c H))
    (CT_comp (CT_comp (CT_cast (app_assoc [c] [c] [c]))
                      (CT_tens (CT_id [c]) (sg_dup c H)))
             (sg_dup c H)) :=
  CTEW_ax SupplySMT _ _ (SE_coassoc c H).

(*
   * Left counit, in the shape of [delta_counit_left]: the field's
   right-hand side is the [from] of the presented left unitor,
   [CT_cast (eq_sym (app_nil_l [c]))], a stuck endo-cast eliminated
   by [CT_cast_id]. 

   --------
   * 左余单位，形状为 [delta_counit_left]：该场的右侧是所展示左单元器的 [from]，[CT_cast (eq_sym (app_nil_l [c] ))]，一个被 [CT_cast_id] 消除的卡住的内转换。
*)
Lemma supply_wire_counit_left (c : Colour) (H : copyable c = true) :
  CTermEqW SupplySMT
    (CT_comp (CT_tens (sg_del c H) (CT_id [c])) (sg_dup c H))
    (CT_cast (eq_sym (app_nil_l [c]))).
Proof using Cdec.
  rewrite (CT_cast_id Cdec (eq_sym (app_nil_l [c]))).
  exact (CTEW_ax SupplySMT _ _ (SE_counit_left c H)).
Qed.

(*
   * Right counit, in the shape of [delta_counit_right]: the axiom is
   already stated with the field's right-hand side. 

   --------
   * 右余单位，形状为 [delta_counit_right]：公理已经在该域的右侧给出。
*)
Definition supply_wire_counit_right (c : Colour) (H : copyable c = true) :
  CTermEqW SupplySMT
    (CT_comp (CT_tens (CT_id [c]) (sg_del c H)) (sg_dup c H))
    (CT_cast (eq_sym (app_nil_r [c]))) :=
  CTEW_ax SupplySMT _ _ (SE_counit_right c H).

(*
   * Cocommutativity, in the shape of
   [delta_cocommutative_of_ccomon]. 

   --------
   * 余交换性，以 [delta_cocommutative_of_ccomon] 的形式。
*)
Definition supply_wire_cocomm (c : Colour) (H : copyable c = true) :
  CTermEqW SupplySMT
    (CT_comp (CT_braid [c] [c]) (sg_dup c H))
    (sg_dup c H) :=
  CTEW_ax SupplySMT _ _ (SE_cocomm c H).

(*
   * ** The wire comonoids

   Explicit [Build_*] applications (record literals would infer the
   wrong category); every law field is the corresponding standalone
   lemma, accepted by conversion against the field's normal form. 

   --------
   * ** 线状余幺半群

   显式的 [Build_*] 应用（记录字面量会推断出错误的范畴）；每个定律字段都是相应的独立引理，可通过与该字段的规范形式进行转换来接受。
*)

Definition supply_wire_comonoid_raw (c : Colour) (H : copyable c = true) :
  @Comonoid (CPresentedCat SupplySMT)
    (@braided_is_monoidal (CPresentedCat SupplySMT)
       (@symmetric_is_braided (CPresentedCat SupplySMT)
          (CPresented_Symmetric SupplySMT Cdec)))
    ([c] : list Colour) :=
  @Build_Comonoid (CPresentedCat SupplySMT)
    (@braided_is_monoidal (CPresentedCat SupplySMT)
       (@symmetric_is_braided (CPresentedCat SupplySMT)
          (CPresented_Symmetric SupplySMT Cdec)))
    ([c] : list Colour)
    (SupplyPROP_dup c H)
    (SupplyPROP_del c H)
    (supply_wire_coassoc c H)
    (supply_wire_counit_left c H)
    (supply_wire_counit_right c H).

(*
   * The commutative packaging, at the instances the [SelectiveSupply]
   class of Supply.v asks for ([wire c ≡ [c]] on the nose). 

   --------
   * 交换包装，在 [SelectiveSupply] 类供应.v 请求 ([wire c ≡ [c]] 准确时的实例。
*)
Definition supply_wire_comonoid (c : Colour) (H : copyable c = true) :
  @CommutativeComonoid (@cprop_cat Colour SupplyPROP)
    (@cprop_symmetric Colour SupplyPROP)
    (wire (P := SupplyPROP) c) :=
  @Build_CommutativeComonoid (CPresentedCat SupplySMT)
    (CPresented_Symmetric SupplySMT Cdec)
    ([c] : list Colour)
    (supply_wire_comonoid_raw c H)
    (supply_wire_cocomm c H).

(** ** The selective supply instance / ** 选择性供应实例 *)

Definition SupplyPROP_SelectiveSupply : SelectiveSupply SupplyPROP copyable :=
  @Build_SelectiveSupply Colour SupplyPROP copyable supply_wire_comonoid.

(*
   * ** Machine-checked sanity

   The mediation equalities of Supply.v REDUCE to [eq_refl] at
   [SupplyPROP] (the shared-record wiring of the presented tower
   makes both coherence paths definitional), so the derived boundary
   supply [supply_list] carries no residual transport here.  Each
   [Example] holds by [eq_refl]; any regression in the wiring is
   caught at this file rather than at a distant use site. 

   --------
   * ** 机器检查的合理性

   供应的中介等式在 [eq_refl] 处简化为 [SupplyPROP]（所展示塔的共享记录布线使得两条一致性路径具有定义性），因此导出的边界供应 [supply_list] 在此处不携带任何剩余传输。每个 [Example] 由 [eq_refl] 支持；布线中的任何回归将在此文件中被捕获，而不是在远端使用点。
*)

Example SupplyPROP_ctensor_app_b_refl (cs ds : list Colour) :
  ctensor_app_b SupplyPROP cs ds = eq_refl := eq_refl.

Example SupplyPROP_cunit_nil_b_refl :
  cunit_nil_b SupplyPROP = eq_refl := eq_refl.

Example SupplyPROP_coherence_is_refl :
  @cprop_monoidal_coherence Colour SupplyPROP = eq_refl := eq_refl.

Example SupplyPROP_wire (c : Colour) :
  wire (P := SupplyPROP) c = (c :: nil) := eq_refl.

(*
   * The empty-boundary supply is the unit comonoid on the nose (the
   [cunit_nil_b] transport vanished). 

   --------
   * 空边界供应在本质上是单位余单体（[cunit_nil_b] 传输消失）。
*)
Example SupplyPROP_supply_list_nil :
  supply_list (P := SupplyPROP) (SS := SupplyPROP_SelectiveSupply)
    [] (all_copyable_nil copyable)
  = @CommutativeComonoid_Unit (CPresentedCat SupplySMT)
      (CPresented_Symmetric SupplySMT Cdec) := eq_refl.

(*
   * The singleton-boundary supply collapses to the wire comonoid: it
   is DEFINITIONALLY the wire comonoid tensored with the unit
   comonoid — the [ctensor_app_b [c] []] transport vanished — up to
   the (proof-irrelevant, [UIP_dec Bool.bool_dec]) copyability
   evidence produced by the cons-peeling of [supply_list]. 

   --------
   * 单例边界供给坍缩为线复合子：从定义上它就是线复合子与单位复合子的张量 ——  [ctensor_app_b [c]  []] 传输消失 —— 直至由  [supply_list]  的 cons 剥离生成的（证明无关的，[UIP_dec Bool.bool_dec]）可复制性证据。
*)
Lemma SupplyPROP_supply_list_wire (c : Colour) (H : copyable c = true)
  (Hc : all_copyable copyable [c]) :
  supply_list (P := SupplyPROP) (SS := SupplyPROP_SelectiveSupply) [c] Hc
  = @CommutativeComonoid_Tensor (CPresentedCat SupplySMT)
      (CPresented_Symmetric SupplySMT Cdec) _ _
      (supply_wire_comonoid c H)
      (@CommutativeComonoid_Unit (CPresentedCat SupplySMT)
         (CPresented_Symmetric SupplySMT Cdec)).
Proof using Type.
  cbn.
  rewrite (UIP_dec Bool.bool_dec (proj1 (andb_prop _ _ Hc)) H).
  reflexivity.
Qed.

(*
   * The comultiplication of the singleton supply, pinned: it is the
   canonical tensor comultiplication of the wire comonoid with the
   unit comonoid.  (The further collapse of the unit factor — all
   the way down to the duplicator itself — is
   [SupplyPROP_scopy_wire] below.) 

   --------
   * 单例供应的共乘法，固定：它是带有单位余单子线的线余单子的规范张量共乘法。（单位因子的进一步塌缩——一直到复制器本身——如下所示 [SupplyPROP_scopy_wire]。）
*)
Example SupplyPROP_supply_list_wire_delta (c : Colour)
  (H : copyable c = true) (Hc : all_copyable copyable [c]) :
  ccomon_delta
    (supply_list (P := SupplyPROP) (SS := SupplyPROP_SelectiveSupply) [c] Hc)
  ≈[CPresentedCat SupplySMT]
  ccomon_delta
    (@CommutativeComonoid_Tensor (CPresentedCat SupplySMT)
       (CPresented_Symmetric SupplySMT Cdec) _ _
       (supply_wire_comonoid c H)
       (@CommutativeComonoid_Unit (CPresentedCat SupplySMT)
          (CPresented_Symmetric SupplySMT Cdec))).
Proof using Type.
  rewrite (SupplyPROP_supply_list_wire c H Hc).
  reflexivity.
Qed.

(*
   * Every supply axiom holds in [SupplyPROP], by construction. 

   --------
   * 每个供应公理在 [SupplyPROP] 中都成立，这是由构造决定的。
*)
Example SupplyPROP_cocomm_holds (c : Colour) (H : copyable c = true) :
  cquot SupplySMT (CT_comp (CT_braid [c] [c]) (sg_dup c H))
    ≈[CPresentedCat SupplySMT] SupplyPROP_dup c H :=
  CTEW_ax SupplySMT _ _ (SE_cocomm c H).

(*
   * ** The singleton collapse, up to [≈]

   The capstone of the collapse pins: on a single wire the DERIVED
   boundary copy/discard of Supply.v coincide with the generators
   themselves.  The derived [scopy [c]] is the canonical tensor
   comultiplication of the wire comonoid with the unit comonoid
   ([SupplyPROP_supply_list_wire] above); its interchange is built
   from associators, unitors and a unit braid, all of which are
   endo-casts or unit braids at CONCRETE colour words here, so the
   whole conjugation collapses by list-UIP ([CT_cast_id]), the
   unit-braid axiom, and the strict right-unit law.

   The rewrites run over the [Prop]-valued congruence [CTermEqW], so
   the file registers the (file-local) [Equivalence] and [Proper]
   instances the generalized-rewriting engine needs on the raw term
   formers. 

   --------
   * ** 单例塌缩，直到 [≈] 

   塌缩图钉的顶点：在单根线上，Supply.v 的派生边界复制/丢弃与发电器本身重合。派生的 [scopy [c] ] 是该线余单子与单位余单子（上文的 [SupplyPROP_supply_list_wire] ）的典范张量余乘法；它的交换是由结合子、单位子和单位编织构成的，这些都是具体色彩词上的自同态或单位编织，因此整个共轭通过列表-UIP（[CT_cast_id]）、单位编织公理和严格右单位律而塌缩。

   重写作用于 [Prop] 值的同余 [CTermEqW]，因此文件注册了（文件本地的）[Equivalence] 和 [Proper] 实例，这是广义重写引擎在原始项构造器上所需要的。
*)

#[local] Instance SupplyPROP_CTermEqW_Equivalence
  {cs ds : list Colour} :
  RelationClasses.Equivalence (@CTermEqW Colour SupplySMT cs ds).
Proof.
  split.
  - intro t; exact (CTermEqW_refl SupplySMT t).
  - intros s t Hst; exact (CTEW_sym _ s t Hst).
  - intros s t u H1 H2; exact (CTEW_trans _ s t u H1 H2).
Qed.

#[local] Instance SupplyPROP_CT_comp_Proper
  {cs ds es : list Colour} :
  Morphisms.Proper
    (Morphisms.respectful (@CTermEqW Colour SupplySMT ds es)
       (Morphisms.respectful (@CTermEqW Colour SupplySMT cs ds)
          (@CTermEqW Colour SupplySMT cs es)))
    (@CT_comp Colour SupplyExtSig cs ds es).
Proof.
  intros f f' Hf g g' Hg.
  exact (CTEW_comp _ f f' g g' Hf Hg).
Qed.

#[local] Instance SupplyPROP_CT_tens_Proper
  {cs1 ds1 cs2 ds2 : list Colour} :
  Morphisms.Proper
    (Morphisms.respectful (@CTermEqW Colour SupplySMT cs1 ds1)
       (Morphisms.respectful (@CTermEqW Colour SupplySMT cs2 ds2)
          (@CTermEqW Colour SupplySMT (cs1 ++ cs2) (ds1 ++ ds2))))
    (@CT_tens Colour SupplyExtSig cs1 ds1 cs2 ds2).
Proof.
  intros f f' Hf g g' Hg.
  exact (CTEW_tens _ f f' g g' Hf Hg).
Qed.

(*
   * Embedded identity/tensor bookkeeping, as rewrite rules for
   [CTermEqW]. 

   --------
   * 嵌入式身份/张量记账，作为 [CTermEqW] 的重写规则。
*)
Definition supply_eqw_id_left {cs ds : list Colour}
  (f : CTerm SupplyExtSig cs ds) :
  CTermEqW SupplySMT (CT_comp (CT_id ds) f) f :=
  CTEW_termeq SupplySMT _ _ (CTE_id_left f).

Definition supply_eqw_tens_id (a b : list Colour) :
  CTermEqW SupplySMT (CT_tens (CT_id a) (CT_id b)) (CT_id (a ++ b)) :=
  CTEW_termeq SupplySMT _ _ (CTE_tens_id a b).

(** The derived singleton copy IS the duplicator. / 派生的单例副本就是复制器。 *)
Theorem SupplyPROP_scopy_wire (c : Colour) (H : copyable c = true)
  (Hc : all_copyable copyable [c]) :
  scopy (P := SupplyPROP) (SS := SupplyPROP_SelectiveSupply) [c] Hc
  ≈[CPresentedCat SupplySMT] SupplyPROP_dup c H.
Proof.
  unfold scopy.
  rewrite (SupplyPROP_supply_list_wire c H Hc).
  cbn.
  (*
 The unit braid collapses (its [eq_rect] transport is over an
 endo-equality at the concrete word [[c]]). 

 --------
 该单位编织体坍塌（其 [eq_rect] 传输在具体单词 [[c] 上是一个内等式）。
*)
  pose proof (@CTE_braid_unit_right Colour SupplyExtSig [c]) as Hb.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r [c]) eq_refl) in Hb.
  cbn in Hb.
  (* The strict right-unit law at the duplicator. / 复印机处的严格右单位法则。 *)
  pose proof (@CTE_tens_id0_right Colour SupplyExtSig
                [c] [c; c] (sg_dup c H)) as Ht.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r [c; c]) eq_refl) in Ht.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r [c]) eq_refl) in Ht.
  cbn in Ht.
  (*
 Kill the five endo-casts (all boundary words are concrete). 

 --------
 消灭五个内铸体（所有边界词都是具体的）。
*)
  rewrite (CT_cast_id Cdec (app_assoc [c] [] [c])).
  rewrite (CT_cast_id Cdec (eq_sym (app_assoc [] [c] []))).
  rewrite (CT_cast_id Cdec (app_assoc [c] [] [])).
  rewrite (CT_cast_id Cdec (eq_sym (app_assoc [c] [c] []))).
  rewrite (CT_cast_id Cdec (eq_sym (app_nil_l []))).
  (*
 Braid to id, fuse the identity tensors, peel the identities. 

 --------
 将辫子作用于 id，融合身份张量，剥离身份。
*)
  rewrite (CTEW_termeq SupplySMT _ _ Hb).
  rewrite !supply_eqw_tens_id.
  rewrite (CTEW_termeq SupplySMT _ _ Ht).
  rewrite !supply_eqw_id_left.
  reflexivity.
Qed.

(** The derived singleton discard IS the deleter. / 派生的单例丢弃器就是删除器。 *)
Theorem SupplyPROP_sdiscard_wire (c : Colour) (H : copyable c = true)
  (Hc : all_copyable copyable [c]) :
  sdiscard (P := SupplyPROP) (SS := SupplyPROP_SelectiveSupply) [c] Hc
  ≈[CPresentedCat SupplySMT] SupplyPROP_del c H.
Proof.
  unfold sdiscard.
  rewrite (SupplyPROP_supply_list_wire c H Hc).
  cbn.
  (* The strict right-unit law at the deleter. / 在删除器处的严格右单位法则。 *)
  pose proof (@CTE_tens_id0_right Colour SupplyExtSig
                [c] [] (sg_del c H)) as Ht.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r ([] : list Colour)) eq_refl)
    in Ht.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r [c]) eq_refl) in Ht.
  cbn in Ht.
  (*
 The unit-comonoid counit is an endo-cast; kill it, then peel. 

 --------
 单位-余单元余单位是一个自端投射；杀掉它，然后剥开。
*)
  rewrite (CT_cast_id Cdec (app_nil_l [])).
  rewrite (CTEW_termeq SupplySMT _ _ Ht).
  rewrite !supply_eqw_id_left.
  reflexivity.
Qed.

(*
   * ** Fan-out corollaries

   The categorical content of the linear fan-out check: the supply
   generators are conservative at every NON-copyable colour, so
   hom-emptiness at linear colours survives the supply extension —
   no equational axiom can inhabit an empty hom-set. 

   --------
   * ** 扇出推论

   线性扇出检查的范畴内容：在每个不可复制的颜色上，供应生成器是保守的，因此线性色上的同态空性在供应扩展时得以保留——没有方程公理可以占据空同态集。
*)

(*
   * The supply generators mention only copyable colours, so a
   non-copyable colour occurs equally often (namely zero times) on
   both boundaries of every supply generator. 

   --------
   * 供应生成器只提到可复制的颜色，所以不可复制的颜色在每个供应生成器的两个边界上出现的次数相等（即零次）。
*)
Definition supplygen_conservative (c : Colour) (Hc : copyable c = false) :
  c_conservative Cdec SupplyGen c.
Proof using Type.
  intros cs ds g.
  destruct g as [d Hd | d Hd]; simpl.
  - (* SG_dup d : [d] -> [d; d] / SG_dup d : [d] -> [d; d] *)
    destruct (Cdec d c) as [e | n].
    + exfalso; subst d; rewrite Hd in Hc; discriminate.
    + reflexivity.
  - (* SG_del d : [d] -> [] *)
    destruct (Cdec d c) as [e | n].
    + exfalso; subst d; rewrite Hd in Hc; discriminate.
    + reflexivity.
Qed.

(*
   * The extended signature is conservative at [c] whenever the base
   signature is (the supply half always is, by the previous
   lemma). 

   --------
   * 当基签名为 [c] 时，扩展签名是保守的（根据前面的引理，补充部分总是如此）。
*)
Definition supplyextsig_conservative (c : Colour) (Hc : copyable c = false)
  (HS : c_conservative Cdec S c) :
  c_conservative Cdec SupplyExtSig c :=
  fun cs ds g =>
    match g with
    | inl gS => HS cs ds gS
    | inr gG => supplygen_conservative c Hc cs ds gG
    end.

(*
   * No fan-out at linear colours: over a base signature conservative
   at a non-copyable [c], the hom-set [[c] ~> [c; c]] of the
   presented supply PROP is EMPTY — the presented transfer of the
   free-level counting theorem ([no_linear_fanout_presented]:
   quotient homs are the same type, and no congruence can inhabit an
   empty hom). 

   --------
   * 在线性色上没有扇出：在不可复制的 [c] 的基础签名上，所呈现的供应 PROP 的同态集 [[c] ~> [c; c] 是空的——所呈现的自由级计数定理的传递（[no_linear_fanout_presented]：商同态是相同类型，并且没有同余可以存在于空同态中）。
*)
Theorem SupplyPROP_no_fanout (c : Colour) (Hc : copyable c = false)
  (HS : c_conservative Cdec S c) :
  (([c] : list Colour) ~{SupplyPROP}~> [c; c]) -> False.
Proof using Type.
  exact (no_linear_fanout_presented Cdec SupplySMT c
           (supplyextsig_conservative c Hc HS)).
Qed.

(** No discard either, by the same counting argument. / 也不弃牌，按照同样的计数论证。 *)
Theorem SupplyPROP_no_discard (c : Colour) (Hc : copyable c = false)
  (HS : c_conservative Cdec S c) :
  (([c] : list Colour) ~{SupplyPROP}~> []) -> False.
Proof using Type.
  exact (no_linear_discard_presented Cdec SupplySMT c
           (supplyextsig_conservative c Hc HS)).
Qed.

(*
   * Fan-out at copyable colours: the duplicator itself.  Note
   [[c] ++ [c] ≡ [c; c]] definitionally, so no cast intervenes. 

   --------
   * 可复制颜色的扇出：复制器本身。 注意 [[c]  ++  [c]  ≡  [c; c] ] 在定义上是如此，因此不会有类型转换介入。
*)
Definition SupplyPROP_fanout (c : Colour) (H : copyable c = true) :
  ([c] : list Colour) ~{SupplyPROP}~> [c; c] :=
  cquot SupplySMT (CT_gen (inr (SG_dup c H))).

End SupplyInstance.

Arguments SupplyGen {Colour} copyable _ _ : assert.
Arguments SupplyExtSig {Colour} S copyable _ _ : assert.
Arguments SupplySMT {Colour} S copyable : assert.
Arguments SupplyPROP {Colour} Cdec S copyable : assert.
Arguments SupplyPROP_dup {Colour} S copyable c H : assert.
Arguments SupplyPROP_del {Colour} S copyable c H : assert.
Arguments supply_wire_comonoid {Colour} Cdec S copyable c H : assert.
Arguments SupplyPROP_SelectiveSupply {Colour} Cdec S copyable : assert.
Arguments supplygen_conservative {Colour} Cdec copyable c Hc cs ds g : assert.
Arguments supplyextsig_conservative {Colour} Cdec S copyable c Hc HS cs ds g
  : assert.
Arguments SupplyPROP_no_fanout {Colour} Cdec S copyable c Hc HS _ : assert.
Arguments SupplyPROP_no_discard {Colour} Cdec S copyable c Hc HS _ : assert.
Arguments SupplyPROP_fanout {Colour} Cdec S copyable c H : assert.
Arguments SupplyPROP_scopy_wire {Colour} Cdec S copyable c H Hc : assert.
Arguments SupplyPROP_sdiscard_wire {Colour} Cdec S copyable c H Hc : assert.

(*
   * ** The pure supply PROP: the exact fan-out characterisation

   Over the empty base signature the supply generators are the ONLY
   generators, and copyability is characterised exactly by fan-out
   inhabitation.  This is the free-standing categorical statement of
   the linear fan-out check: linearity is hom-EMPTINESS, not a
   convention. 

   --------
   * ** 纯供应 PROP：精确的扇出特征

   在空基签名上，供应生成器是唯一的生成器，并且可复制性正好由扇出可居住性描述。这是线性扇出检查的独立范畴声明：线性是同态-空性，而不是一种约定。
*)

Section PureSupply.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (copyable : Colour -> bool).

(*
   * The empty signature is conservative at every colour —
   [Empty_CSig_conservative] of [Construction/ColouredPROP/Linear.v],
   at the section's [Cdec]. 

   --------
   * 空签名在每种颜色下都是保守的——  
   [Empty_CSig_conservative] 的 [Construction/ColouredPROP/Linear.v]，  
   在截面的 [Cdec]。
*)
Definition pure_base_conservative (c : Colour) :
  c_conservative Cdec Empty_CSig c :=
  Empty_CSig_conservative Cdec c.

(*
   * A wire of the pure supply PROP supports a fan-out iff its colour is
   copyable. 

   --------
   * 只有当其颜色可复制时，纯供应 PROP 的一根导线才支持扇出。
*)
Theorem fanout_iff (c : Colour) :
  inhabited
    (([c] : list Colour) ~{SupplyPROP Cdec Empty_CSig copyable}~> [c; c])
  <-> copyable c = true.
Proof using Type.
  split.
  - intros [t].
    destruct (copyable c) eqn:Hc.
    + reflexivity.
    + exfalso.
      exact (SupplyPROP_no_fanout Cdec Empty_CSig copyable c Hc
               (pure_base_conservative c) t).
  - intro H.
    exact (inhabits (SupplyPROP_fanout Cdec Empty_CSig copyable c H)).
Qed.

(** The discard-side mirror, for symmetry. / 弃牌区的镜子，为了对称。 *)
Theorem discard_iff (c : Colour) :
  inhabited
    (([c] : list Colour) ~{SupplyPROP Cdec Empty_CSig copyable}~> [])
  <-> copyable c = true.
Proof using Type.
  split.
  - intros [t].
    destruct (copyable c) eqn:Hc.
    + reflexivity.
    + exfalso.
      exact (SupplyPROP_no_discard Cdec Empty_CSig copyable c Hc
               (pure_base_conservative c) t).
  - intro H.
    exact (inhabits
             (cquot (SupplySMT Empty_CSig copyable)
                (CT_gen (inr (SG_del copyable c H))))).
Qed.

End PureSupply.

Arguments pure_base_conservative {Colour} Cdec c cs ds g : assert.
Arguments fanout_iff {Colour} Cdec copyable c : assert.
Arguments discard_iff {Colour} Cdec copyable c : assert.
