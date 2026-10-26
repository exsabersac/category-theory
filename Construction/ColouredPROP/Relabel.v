Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
(*
 [Instance.Fun] is Required but NOT Imported: its functor-category
 notation “[ C , D ]” (level 90) and ListNotations' “[]” have
 incompatible parsing prefixes, and this file needs the latter for
 colour words.  The one use of the functor category below names
 [Category.Instance.Fun.Fun] qualified. 

 --------
 [Instance.Fun] 是必需的但未导入：其函子范畴符号 “[ C , D ]”（级别 90）与 ListNotations 的 “[]” 具有不兼容的解析前缀，而此文件需要后者来表示颜色词。下面对函子范畴的唯一使用命名了合格的 [Category.Instance.Fun.Fun]。
*)
Require Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(*
   * * Relabelling coloured-PROP terms along a signature morphism 

   --------
   * * 沿着特征态射重新标记有色-PROP 项
*)

(*
 nLab: https://ncatlab.org/nlab/show/generators+and+relations
 nLab: https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 A signature relabelling [h : CSubSig S T] ([Construction/
 ColouredPROP/Signature.v]) preserves generator boundaries on the
 nose, so it acts on typed string-diagram terms by pure structural
 recursion: relabel every generator leaf through [h] and leave the
 structural constructors untouched.  No injectivity of [h] is
 assumed or used anywhere in this file — everything applies to
 arbitrary boundary-preserving relabellings, including generator
 collapses.  This file develops that action and its consequences,
 the coloured mirror of the signature-morphism half of
 [Construction/PROP/Tietze.v] (its [T_map] development, with
 [list Colour] replacing [nat], [++] replacing [Nat.add], and
 [app_nil_r] / [app_assoc] replacing [Nat.add_0_r] /
 [Nat.add_assoc]):

 1.  [CT_map h] is a computing [Fixpoint] — e.g. [CT_map h (CT_comp
 g f)] is definitionally [CT_comp (CT_map h g) (CT_map h f)] —
 so the functor packaging below discharges its identity and
 composition laws by [CTE_refl].  Because [h] preserves
 boundaries exactly, NO boundary-mismatch casts are needed to
 STATE [CT_map]'s action: the boundaries of a term and of its
 image agree on the nose.  ([CT_cast] does still appear in a
 few statements — [CT_map_CT_cast] and the coherence squares of
 item 4 — but there it is a first-class term being mapped, the
 monoidal structural map under study, never a repair of a
 boundary mismatch introduced by [CT_map] itself.)  (Per the
 note at the foot of [Signature.v], there is
 no tactic-built precursor to bridge to: the coloured spine has
 [CT_map] from day one.)

 2.  [CT_map] fixes casts ([CT_map_CT_cast]) and commutes with the
 three [eq_rect] transport shapes in which [CTermEq] states its
 strict-PROP axioms (the transport seams [CT_map_eq_rect_cod] /
 [CT_map_eq_rect_dom] / [CT_map_eq_rect_r_dom]) — each a Leibniz
 equality by destructing the boundary equation.

 3.  Soundness for the equational theory ([CT_map_CTermEq]): the
 induction covers all NINETEEN [CTermEq] constructors — the
 thirteen constructor-to-constructor cases reduce by
 computation, and the six transport-form cases first move
 [CT_map] across the [eq_rect] seams, then close with the same
 primitive constructor.

 4.  The induced functor [CRelabelFunctor h : CFreeCat S ⟶
 CFreeCat T] — identity on objects (colour words), [CT_map h] on
 morphisms — is STRICT SYMMETRIC monoidal: both comparison maps
 are identities on the nose, the object equalities are
 [eq_refl], and the braid square commutes because [CT_map] fixes
 [CT_braid].  Signature morphisms induce strict symmetric maps
 of free coloured PROPs ([CRelabelFunctor_Monoidal] /
 [CRelabelFunctor_Strict] / [CRelabelFunctor_Braided] /
 [CRelabelFunctor_Symmetric]).  The comparison squares are fed
 by the identity-bookkeeping quartet [ctm_id_swap] /
 [ctm_comp_id_tens] / [ctm_collapse_r] / [ctm_collapse_l] of
 [Construction/ColouredPROP/TermEq.v].

 Everything is elementary syntax: the only relation involved is the
 [Prop]-valued congruence [CTermEq], and no proof irrelevance is
 used anywhere — the decidability discipline (D2) enters only
 through the shared [Monoidal] record [CFreeCat_Monoidal _ Cdec]
 that the packaged records name in their types.  Following the
 [Free.v] discipline, the records are explicit [Build_*]
 applications with standalone, named comparison lemmas. 

 --------
 nLab:  https://ncatlab.org/nlab/show/generators+and+relations 
 nLab:  https://ncatlab.org/nlab/show/PROP 
 维基百科:  https://en.wikipedia.org/wiki/PROP_(category_theory) 

 一个签名重新标记  [h : CSubSig S T]  ([Construction/
 ColouredPROP/Signature.v]) 在节点上保留生成元边界，因此它通过纯结构递归作用于类型化字符串图项：通过  [h]  重新标记每个生成元叶子，并保留结构构造不变。 本文件中不假设或使用  [h]  的单射性——所有内容适用于任意保持边界的重新标记，包括生成元的合并。 本文件开发了该作用及其后果，即签名态射一半的彩色镜像 [Construction/PROP/Tietze.v]（其 [T_map] 开发，其中 [list Colour] 替代 [nat]，[++] 替代 [Nat.add]，以及 [app_nil_r] / [app_assoc] 替代 [Nat.add_0_r] / [Nat.add_assoc]）:1. [CT_map h] 是一个计算 [Fixpoint] —— 例如 [CT_map h (CT_comp g f)] 在定义上是 [CT_comp (CT_map h g) (CT_map h f)] —— 所以下面的函子打包通过 [CTE_refl] 解决了它的恒等性和组合律。因为 [h] 能够精确地保持边界，所以不需要任何边界不匹配的转换来表达 [CT_map] 的作用：一个项及其映像的边界完全一致。([CT_cast] 仍然出现在一些语句中——[CT_map_CT_cast] 以及项目 4 的相干广场——但在那里它是一个被映射的一流项，即正在研究的单幺结构映射，从不作为 [CT_map] 本身引入的边界不匹配的修正。)（根据 [Signature.v] 底部的注释，没有由策略构建的前驱以桥接到：彩色主干从第一天起就有 [CT_map]。）

 2. [CT_map] 修复类型转换（[CT_map_CT_cast]）并与三种 [eq_rect] 传输形状交换，这三种形状中 [CTermEq] 陈述其严格 PROP 公理（传输接缝 [CT_map_eq_rect_cod] / [CT_map_eq_rect_dom] / [CT_map_eq_rect_r_dom]）——每一个都是通过解构边界方程得到的莱布尼茨等式。3. 关于等式理论 ([CT_map_CTermEq]) 的正确性：归纳涵盖了所有十九个 [CTermEq] 构造函数——十三个构造函数到构造函数的情况通过计算化简，而六个传输形式的情况先将 [CT_map] 移到 [eq_rect] 接缝处，然后用相同的原始构造函数封闭。4.  所诱导的函子 [CRelabelFunctor h : CFreeCat S ⟶ CFreeCat T] —— 在对象（颜色字）上是恒等的，[CT_map h] 在态射上 —— 是严格对称单体的：两个比较映射在本质上都是恒等的，对象等式是 [eq_refl]，并且因为 [CT_map] 固定 [CT_braid]，所以编织方格是交换的。签名态射诱导自由彩色 PROP 的严格对称映射（[CRelabelFunctor_Monoidal] / [CRelabelFunctor_Strict] / [CRelabelFunctor_Braided] / [CRelabelFunctor_Symmetric]）。比较方格由恒等记账四重组 [ctm_id_swap] / [ctm_comp_id_tens] / [ctm_collapse_r] / [ctm_collapse_l] 的 [Construction/ColouredPROP/TermEq.v] 提供。一切都是基本语法：唯一涉及的关系是 [Prop] 值的同余 [CTermEq]，并且在任何地方都没有使用证明不相关性——可判定性规范 (D2) 仅通过打包记录类型中命名的共享 [Monoidal] 记录 [CFreeCat_Monoidal _ Cdec] 引入。遵循 [Free.v] 规范，这些记录是带有独立、命名比较引理的显式 [Build_*] 应用。
*)

(*
   * ** The relabelling action on terms

   [CT_map h] relabels every generator leaf through [h] and leaves
   the structural constructors untouched.  It COMPUTES on
   constructors, which the functor and monoidal-functor packaging
   below exploits: identity/composition preservation are
   [CTE_refl]. 

   --------
   * ** 关于术语的重新标记操作

   [CT_map h] 通过 [h] 重新标记每个生成器叶子，并保持结构构造器不变。它对构造器进行计算，下面的函子和单调函子打包利用了这一点：身份/组合的保持是 [CTE_refl] 。
*)

Fixpoint CT_map {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {cs ds : list Colour}
  (t : CTerm S cs ds) : CTerm T cs ds :=
  match t in CTerm _ cs' ds' return CTerm T cs' ds' with
  | CT_id ks       => CT_id ks
  | CT_braid us vs => CT_braid us vs
  | CT_comp g f    => CT_comp (CT_map h g) (CT_map h f)
  | CT_tens f g    => CT_tens (CT_map h f) (CT_map h g)
  | CT_gen g       => CT_gen (h _ _ g)
  end.

(*
   * Casts are fixed by every signature morphism (a Leibniz equality:
   both sides are the same [match] once [e] is destructed). 

   --------
   * 每个签名态射都会固定类型转换（一个莱布尼茨等式：一旦  [e] 被解构，两边都是相同的 [match]）。
*)
Lemma CT_map_CT_cast {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {cs ds : list Colour} (e : cs = ds) :
  CT_map h (CT_cast e) = CT_cast e.
Proof. destruct e; reflexivity. Qed.

(*
   * *** Transport seams

   The strict-PROP axioms of [CTermEq] carry their boundary
   mismatches as [eq_rect] transports over [app_nil_r] / [app_assoc]
   equations; [CT_map] commutes with each transport shape by Leibniz
   equality (destruct the boundary equation). 

   --------
   * *** 传输缝

   [CTermEq] 的严格 PROP 公理将其边界不匹配以 [eq_rect] 的形式，通过 [app_nil_r] / [app_assoc] 方程进行传输；[CT_map] 与每个传输形状按 Leibniz 等式交换（分解边界方程）。
*)

Lemma CT_map_eq_rect_cod {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {a b b' : list Colour} (e : b = b')
  (t : CTerm S a b) :
  CT_map h (eq_rect b (fun k : list Colour => CTerm S a k) t b' e)
  = eq_rect b (fun k : list Colour => CTerm T a k) (CT_map h t) b' e.
Proof. destruct e; reflexivity. Qed.

Lemma CT_map_eq_rect_dom {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {a a' b : list Colour} (e : a = a')
  (t : CTerm S a b) :
  CT_map h (eq_rect a (fun k : list Colour => CTerm S k b) t a' e)
  = eq_rect a (fun k : list Colour => CTerm T k b) (CT_map h t) a' e.
Proof. destruct e; reflexivity. Qed.

Lemma CT_map_eq_rect_r_dom {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {a a' b : list Colour} (e : a' = a)
  (t : CTerm S a b) :
  CT_map h (eq_rect_r (fun k : list Colour => CTerm S k b) t e)
  = eq_rect_r (fun k : list Colour => CTerm T k b) (CT_map h t) e.
Proof. destruct e; reflexivity. Qed.

(*
   * *** Soundness of relabelling

   [CT_map h] carries every free equation of [CTermEq S] to the
   corresponding free equation of [CTermEq T].  The induction covers
   all nineteen constructors: the thirteen
   constructor-to-constructor cases reduce by computation, and the
   six transport-form cases ([CTE_tens_id0_right], [CTE_tens_assoc],
   the two hexagons, and the two unit braids) first move [CT_map]
   across the [eq_rect] seams by the Leibniz bridges above, then
   close with the same primitive constructor. 

   --------
   * *** 重标记的正确性

   [CT_map h] 将 [CTermEq S] 的每一个自由方程映射到 [CTermEq T] 的对应自由方程。归纳涵盖了所有十九个构造子：十三个构造子对构造子的情况通过计算简化，而六个传输形式的情况（[CTE_tens_id0_right]、[CTE_tens_assoc]、两个六边形和两个单位编织）首先通过上面的莱布尼茨桥将 [CT_map] 移到 [eq_rect] 接缝处，然后用相同的原始构造子完成。
*)

Lemma CT_map_CTermEq {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {cs ds : list Colour} {s t : CTerm S cs ds} :
  CTermEq S s t → CTermEq T (CT_map h s) (CT_map h t).
Proof.
  intros HT.
  induction HT.
  - (* CTE_refl *)
    apply CTE_refl.
  - (* CTE_sym *)
    exact (CTE_sym _ _ IHHT).
  - (* CTE_trans / CTE_转 *)
    exact (CTE_trans _ _ _ IHHT1 IHHT2).
  - (* CTE_comp_cong / CTE_复合_并发 *)
    cbn [CT_map]; apply CTE_comp_cong; assumption.
  - (* CTE_tens_cong / CTE_张力电容 *)
    cbn [CT_map]; apply CTE_tens_cong; assumption.
  - (* CTE_id_left / CTE_id_左 *)
    cbn [CT_map]; apply CTE_id_left.
  - (* CTE_id_right / CTE_id_右 *)
    cbn [CT_map]; apply CTE_id_right.
  - (* CTE_assoc / CTE_关联 *)
    cbn [CT_map]; apply CTE_assoc.
  - (* CTE_tens_id / CTE_张力编号 *)
    cbn [CT_map]; apply CTE_tens_id.
  - (* CTE_interchange / CTE_互换 *)
    cbn [CT_map]; apply CTE_interchange.
  - (* CTE_braid_invol / CTE_辫子_参与 *)
    cbn [CT_map]; apply CTE_braid_invol.
  - (* CTE_braid_natural / CTE_自然编织 *)
    cbn [CT_map]; apply CTE_braid_natural.
  - (* CTE_tens_id0_left / CTE_张力_id0_左 *)
    cbn [CT_map]; apply CTE_tens_id0_left.
  - (* CTE_tens_id0_right / CTE_张力_id0_右 *)
    rewrite CT_map_eq_rect_cod, CT_map_eq_rect_r_dom.
    cbn [CT_map]; apply CTE_tens_id0_right.
  - (* CTE_tens_assoc / CTE_张量关联 *)
    rewrite CT_map_eq_rect_cod, CT_map_eq_rect_r_dom.
    cbn [CT_map]; apply CTE_tens_assoc.
  - (* CTE_braid_hex_left / CTE_左侧六边形编织 *)
    cbn [CT_map].
    rewrite CT_map_eq_rect_cod, !CT_map_eq_rect_dom.
    cbn [CT_map]; apply CTE_braid_hex_left.
  - (* CTE_braid_hex_right / CTE_右侧六边形编织 *)
    cbn [CT_map].
    rewrite CT_map_eq_rect_cod, !CT_map_eq_rect_dom.
    cbn [CT_map]; apply CTE_braid_hex_right.
  - (* CTE_braid_unit_left / CTE_左侧编织单元 *)
    rewrite CT_map_eq_rect_cod.
    cbn [CT_map]; apply CTE_braid_unit_left.
  - (* CTE_braid_unit_right / CTE_右侧编织单元 *)
    rewrite CT_map_eq_rect_dom.
    cbn [CT_map]; apply CTE_braid_unit_right.
Qed.

(*
   * ** The induced functor of free coloured PROPs

   A signature morphism [h : CSubSig S T] induces [CRelabelFunctor h :
   CFreeCat S ⟶ CFreeCat T] — identity on objects (colour words),
   [CT_map h] on morphisms — and the functor is STRICT SYMMETRIC
   monoidal: both comparison maps are identities on the nose, the
   object equalities are [eq_refl], and the braid square commutes
   because [CT_map] fixes [CT_braid].  The packaging mirrors the
   one-sorted donor's [RelabelFunctor] tower of [Construction/PROP/
   Tietze.v], with the monoidal instances drawn from the ONE shared
   record [CFreeCat_Monoidal _ Cdec] (see the D2 WARNING at the foot
   of [Construction/ColouredPROP/Monoidal.v]: fix one canonical
   [Cdec] per colour type); the coherence squares are discharged with
   the shared identity-bookkeeping lemmas [ctm_id_swap] /
   [ctm_comp_id_tens] / [ctm_collapse_r] / [ctm_collapse_l] of
   [Construction/ColouredPROP/TermEq.v]. 

   --------
   * ** 自由有色PROP的诱导函子一个签名态射 [h : CSubSig S T] 诱导了 [CRelabelFunctor h : CFreeCat S ⟶ CFreeCat T]——在对象（颜色词）上是恒等，[CT_map h] 在态射上——且该函子是严格对称单态的：两个比较映射在形式上都是恒等，对象等式是 [eq_refl]，编织图平方交换律成立，因为 [CT_map] 固定 [CT_braid]。其打包方式模仿了单排序供体的 [RelabelFunctor] 塔的 [Construction/PROP/Tietze.v]，单态实例取自共享记录 ONE [CFreeCat_Monoidal _ Cdec]（见 [Construction/ColouredPROP/Monoidal.v] 底部的 D2 警告：每种颜色类型固定一个标准 [Cdec]）；相干方形通过共享恒等记账引理 [ctm_id_swap] / [ctm_comp_id_tens] / [ctm_collapse_r] / [ctm_collapse_l] 的 [Construction/ColouredPROP/TermEq.v] 处理。
*)

Section CSignatureMorphism.

Context {Colour : Type}.
Context (S T : CSignature Colour).
Context (h : CSubSig S T).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).

Definition CRelabelFunctor : CFreeCat S ⟶ CFreeCat T :=
  Build_Functor (CFreeCat S) (CFreeCat T)
    (fun cs : list Colour => cs)
    (fun cs ds (t : CTerm S cs ds) => CT_map h t)
    (fun cs ds s t Hst => CT_map_CTermEq h Hst)
    (fun cs => CTE_refl (CT_id cs))
    (fun x y z f g => CTE_refl (CT_comp (CT_map h f) (CT_map h g))).

(*
   * The tensor-then-map and map-then-tensor composites related by the
   tensor comparison of the monoidal structure. 

   --------
   * 与单体结构的张量比较相关的张量-然后映射和映射-然后张量复合。
*)
Definition CRelabel_ap_dom : CFreeCat S ∏ CFreeCat S ⟶ CFreeCat T :=
  CFreeCat_Tensor T ◯ (CRelabelFunctor ∏⟶ CRelabelFunctor).

Definition CRelabel_ap_cod : CFreeCat S ∏ CFreeCat S ⟶ CFreeCat T :=
  CRelabelFunctor ◯ CFreeCat_Tensor S.

(*
   * Both directions of the tensor comparison are families of
   identities — [CT_map] computes through [CT_tens], so the two
   functors have definitionally equal actions — and naturality is
   [ctm_id_swap]. 

   --------
   * 张量比较的两个方向都是恒等式的族 —— [CT_map] 通过 [CT_tens] 进行计算，所以两个函子在定义上具有相等的作用 —— 并且自然性是 [ctm_id_swap] 。
*)
Definition CRelabel_ap_to : CRelabel_ap_dom ⟹ CRelabel_ap_cod :=
  @Build_Transform' (CFreeCat S ∏ CFreeCat S) (CFreeCat T)
    CRelabel_ap_dom CRelabel_ap_cod
    (fun p => CT_id (fst p ++ snd p))
    (fun p q f => ctm_id_swap (CT_tens (CT_map h (fst f)) (CT_map h (snd f)))).

Definition CRelabel_ap_from : CRelabel_ap_cod ⟹ CRelabel_ap_dom :=
  @Build_Transform' (CFreeCat S ∏ CFreeCat S) (CFreeCat T)
    CRelabel_ap_cod CRelabel_ap_dom
    (fun p => CT_id (fst p ++ snd p))
    (fun p q f => ctm_id_swap (CT_tens (CT_map h (fst f)) (CT_map h (snd f)))).

(*
   * The identity components are inverse up to [CTermEq] (the identity
   natural transformation of a composite-with-tensor functor has
   components [CT_tens (CT_id _) (CT_id _)]). 

   --------
   * 恒等分量是 ZZ W0WZZ 下的逆（复合张量函子的恒等自然变换具有分量 ZZ W1WZZ）。
*)
Definition CRelabel_ap_iso :
  @Isomorphism (@Category.Instance.Fun.Fun (CFreeCat S ∏ CFreeCat S)
                  (CFreeCat T))
    CRelabel_ap_dom CRelabel_ap_cod :=
  @Build_Isomorphism (@Category.Instance.Fun.Fun (CFreeCat S ∏ CFreeCat S)
                        (CFreeCat T))
    CRelabel_ap_dom CRelabel_ap_cod
    CRelabel_ap_to CRelabel_ap_from
    (fun p => ctm_comp_id_tens (fst p) (snd p))
    (fun p => ctm_comp_id_tens (fst p) (snd p)).

(*
   * *** The coherence squares

   Each structural map of [CFreeCat_Monoidal] is a [CT_cast], which
   [CT_map] fixes ([CT_map_CT_cast]); after that rewrite the squares
   are pure identity bookkeeping. 

   --------
   * *** 一致性方块

   [CFreeCat_Monoidal] 的每个结构图都是一个 [CT_cast]，它
   [CT_map] 固定（[CT_map_CT_cast]）；之后重写的方块
   只是纯粹的身份记录。
*)

Lemma CRelabel_unit_left_square (x : list Colour) :
  CTermEq T (CT_cast (app_nil_l x))
    (CT_comp (CT_comp (CT_map h (CT_cast (app_nil_l x))) (CT_id ([] ++ x)))
             (CT_tens (CT_id []) (CT_id x))).
Proof.
  rewrite (CT_map_CT_cast h (app_nil_l x)).
  apply CTE_sym, ctm_collapse_r.
Qed.

Lemma CRelabel_unit_right_square (x : list Colour) :
  CTermEq T (CT_cast (app_nil_r x))
    (CT_comp (CT_comp (CT_map h (CT_cast (app_nil_r x))) (CT_id (x ++ [])))
             (CT_tens (CT_id x) (CT_id []))).
Proof.
  rewrite (CT_map_CT_cast h (app_nil_r x)).
  apply CTE_sym, ctm_collapse_r.
Qed.

Lemma CRelabel_assoc_square (x y z : list Colour) :
  CTermEq T
    (CT_comp (CT_comp (CT_map h (CT_cast (eq_sym (app_assoc x y z))))
                      (CT_id ((x ++ y) ++ z)))
             (CT_tens (CT_id (x ++ y)) (CT_id z)))
    (CT_comp (CT_comp (CT_id (x ++ (y ++ z)))
                      (CT_tens (CT_id x) (CT_id (y ++ z))))
             (CT_cast (eq_sym (app_assoc x y z)))).
Proof.
  rewrite (CT_map_CT_cast h (eq_sym (app_assoc x y z))).
  apply CTE_trans with (CT_cast (eq_sym (app_assoc x y z))).
  - apply ctm_collapse_r.
  - apply CTE_sym, ctm_collapse_l.
Qed.

(*
   * The strong monoidal structure: the unit comparison is [iso_id],
   the tensor comparison is the identity family [CRelabel_ap_iso], and
   the three coherence squares are the lemmas above.  Both [Monoidal]
   instances are the shared records [CFreeCat_Monoidal _ Cdec]. 

   --------
   * 强单范结构：单位比较是  [iso_id] ，张量比较是恒等族  [CRelabel_ap_iso] ，
   三个相容性方形是上述引理。两个  [Monoidal] 实例如出自共享记录  [CFreeCat_Monoidal _ Cdec] 。
*)
Definition CRelabelFunctor_Monoidal :
  @MonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal T Cdec) CRelabelFunctor :=
  @Build_MonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal T Cdec) CRelabelFunctor
    iso_id
    CRelabel_ap_iso
    (fun x => iso_id)
    (fun x => iso_id)
    (fun x y z => @tensor_assoc (CFreeCat T) (CFreeCat_Monoidal T Cdec) x y z)
    (fun x => CRelabel_unit_left_square x)
    (fun x => CRelabel_unit_right_square x)
    (fun x y z => CRelabel_assoc_square x y z).

(*
   * Both comparison maps are identities on the nose, so the functor is
   STRICT monoidal with [eq_refl] object equalities; the two
   comparison fields reduce to [CTE_refl]-grade goals. 

   --------
   * 两个比较映射在本质上都是恒等映射，因此该函子是严格的幺半群函子，其  [eq_refl] 对象相等；两个比较域简化为  [CTE_refl] 等级目标。
*)
Definition CRelabelFunctor_Strict :
  @StrictMonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal T Cdec) CRelabelFunctor :=
  @Build_StrictMonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal T Cdec) CRelabelFunctor
    CRelabelFunctor_Monoidal
    eq_refl
    (fun x y => eq_refl)
    (CTE_refl (CT_id []))
    (fun x y => CTE_refl (CT_id (x ++ y))).

(*
   * The braid-compatibility square: [CT_map] fixes [CT_braid], and
   both tensor comparisons are identities, so the square is one slide
   of an identity past the braid. 

   --------
   * 辫子兼容方格：[CT_map] 固定 [CT_braid]，且两个张量比较都是恒等变换，因此该方格就是将恒等变换滑过辫子的一次滑动。
*)
Lemma CRelabelFunctor_braid (m n : list Colour) :
  fmap[CRelabelFunctor] (@braid (CFreeCat S) (CFreeCat_Braided S Cdec) m n)
    ∘ to (@ap_iso _ _ _ _ CRelabelFunctor CRelabelFunctor_Monoidal m n)
  ≈[CFreeCat T]
  to (@ap_iso _ _ _ _ CRelabelFunctor CRelabelFunctor_Monoidal n m)
    ∘ @braid (CFreeCat T) (CFreeCat_Braided T Cdec) m n.
Proof.
  exact (ctm_id_swap (CT_braid m n)).
Qed.

Definition CRelabelFunctor_Braided :
  @BraidedMonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Braided S Cdec) (CFreeCat_Braided T Cdec) CRelabelFunctor :=
  @Build_BraidedMonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Braided S Cdec) (CFreeCat_Braided T Cdec) CRelabelFunctor
    CRelabelFunctor_Monoidal
    (fun x y => ctm_id_swap (CT_braid x y)).

(*
   * A braided monoidal functor between symmetric monoidal categories
   IS a symmetric monoidal functor ([SymmetricMonoidalFunctor] is a
   definition, not a class); supplied explicitly, as the alias does
   not participate in instance resolution. 

   --------
   * 对称幺半范畴之间的编织幺半函子
   是对称幺半函子（[SymmetricMonoidalFunctor] 是一个
   定义，而不是一个类）；需要显式提供，因为别名不参与实例解析。
*)
Definition CRelabelFunctor_Symmetric :
  @SymmetricMonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Symmetric S Cdec) (CFreeCat_Symmetric T Cdec) CRelabelFunctor :=
  CRelabelFunctor_Braided.

End CSignatureMorphism.

Arguments CRelabelFunctor {Colour S T} h : assert.
Arguments CRelabelFunctor_Monoidal {Colour S T} h Cdec : assert.
Arguments CRelabelFunctor_Strict {Colour S T} h Cdec : assert.
Arguments CRelabelFunctor_Braided {Colour S T} h Cdec : assert.
Arguments CRelabelFunctor_Symmetric {Colour S T} h Cdec : assert.

(*
   * ** Machine-checked sanity

   [CT_map] computes on the structural constructors, so the functor
   action of [CRelabelFunctor] is definitional, and the sub-signature
   algebra of [Signature.v] is respected on the nose. 

   --------
   * ** 机器检查的合理性

   [CT_map] 在结构构造上进行计算，因此 [CRelabelFunctor] 的函子作用是定义性的，并且 [Signature.v] 的子签名代数严格遵守。
*)

Example CT_map_fixes_id {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) (cs : list Colour) :
  CT_map h (CT_id cs) = CT_id cs := eq_refl.

Example CT_map_fixes_braid {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) (cs ds : list Colour) :
  CT_map h (CT_braid cs ds) = CT_braid cs ds := eq_refl.

Example CT_map_computes_comp {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {a b c : list Colour}
  (g : CTerm S b c) (f : CTerm S a b) :
  CT_map h (CT_comp g f) = CT_comp (CT_map h g) (CT_map h f) := eq_refl.

Example CT_map_computes_tens {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {a b c d : list Colour}
  (f : CTerm S a b) (g : CTerm S c d) :
  CT_map h (CT_tens f g) = CT_tens (CT_map h f) (CT_map h g) := eq_refl.

Example CT_map_relabels_gen {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {cs ds : list Colour} (g : S cs ds) :
  CT_map h (CT_gen g) = CT_gen (h cs ds g) := eq_refl.

Example CT_map_id_sig {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (g : S cs ds) :
  CT_map (CSubSig_id S) (CT_gen g) = CT_gen g := eq_refl.

Example CT_map_compose_sig {Colour : Type} {S T U : CSignature Colour}
  (h2 : CSubSig T U) (h1 : CSubSig S T)
  {cs ds : list Colour} (g : S cs ds) :
  CT_map (CSubSig_compose h2 h1) (CT_gen g)
  = CT_map h2 (CT_map h1 (CT_gen g)) := eq_refl.

Example CRelabelFunctor_obj_id {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) (cs : list Colour) :
  fobj[CRelabelFunctor h] cs = cs := eq_refl.
