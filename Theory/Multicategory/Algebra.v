Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Theory.Multicategory.
Require Import Category.Theory.Multicategory.Functor.
Require Import Category.Theory.Multicategory.Endomorphism.
Require Import Category.Theory.Multicategory.Operad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.CMon.

From Coq Require Import Lists.List.
From Coq Require Import Logic.Eqdep_dec.
Import ListNotations.

Generalizable All Variables.

(** * Operad algebras / * 操作代数 *)

(*
nLab: https://ncatlab.org/nlab/show/algebra+over+an+operad

   An algebra for an operad [O] on an object [X] of a cartesian category is
   exactly a multifunctor from the underlying one-object multicategory of
   [O] to the endomorphism operad [EndOperad X] of
   Theory/Multicategory/Endomorphism.v.  That IS the definition here
   ([OperadAlgebra]), so the classical universal property of the
   endomorphism operad — "an O-algebra structure on X is a map of operads
   O ⟶ End(X)" — holds definitionally ([OperadAlgebra_is_MultiFunctor]).

   THE CONVENIENCE CONSTRUCTOR.  The object map of such a multifunctor is
   forced (the colour type of [EndOperad X] is [poly_unit]), so an algebra
   is determined by its ACTION MAPS [ohom O n → (pow X n ~> X)] together
   with identity/composition/symmetry preservation restated at the arity
   accessors of Theory/Multicategory/Operad.v ([OperadAction]);
   [Build_OperadAlgebra] assembles the full multifunctor, discharging the
   boundary bookkeeping once and for all.  The target-object casts ride on
   axiom-free UIP for the operad's colour type ([operad_obj_UIP]: the
   colour type is propositionally [poly_unit], and UIP transports along
   type equality by [destruct]; the [poly_unit] end is Hedberg via
   [UIP_dec], as in the [UIP_nat] use of
   Theory/Multicategory/Endomorphism.v).

   THE CATEGORY OF ALGEBRAS.  Morphisms of algebras are carrier maps
   intertwining the actions at every arity, with the finite-power
   functoriality [pow_map]; the bundled category [OperadAlgebras] follows
   the first-projection idiom of Construction/FAlg.v.

   THE COMMUTATIVE OPERAD.  [Comm] is the terminal operad: one operation
   in every arity ([mhom Γ c := poly_unit], trivial setoid).  Its algebras
   in [Sets] are commutative monoids in both directions (a full
   categorical equivalence is not claimed; see the bundled note below):
   [Comm_algebra_to_CMon] (binary action + nullary action, with
   associativity/commutativity/unit extracted from the multifunctor laws
   at concrete contexts) and [CMon_to_Comm_algebra] (n-fold sums via the
   convenience constructor), bundled as [Comm_algebra_CMon].

   A RECORDED STRENGTH CHANGE, ON THE FORWARD DIRECTION ONLY.  An
   earlier revision of this paragraph stated that direction
   unconditionally: every [Comm]-algebra on an [X : Sets] yields a
   commutative monoid.  Since the PR "algebraic carriers are sets"
   (2026-09-17) a [CMonObject] carries [cmon_prop], a [PropEquiv] for its
   carrier setoid, and [Comm_algebra_to_CMon] takes its carrier setoid
   straight from [X]; an arbitrary object of [Sets] supplies no [Prop]
   mirror of its `≈`, and there is no [LocallyPropositional Sets] to
   supply one either (Lib/Setoid/Propositional.v,
   Instance/Sets/Propositional.v's header records both measurements).  So
   [Comm_algebra_to_CMon] takes a [PropEquiv (is_setoid X)] as a section
   hypothesis, and [Comm_algebra_CMon]'s left component asks for it too:

     (∀ (X : Sets) (PX : PropEquiv (is_setoid X)),
        OperadAlgebra Comm X → CMonObject) * …

   Those two constants are the only ones in this file whose statement
   changed.  The REVERSE direction is untouched — [CMon_to_Comm_algebra]
   starts from a [CMonObject], whose carrier supplies its own
   [cmon_prop] — and so are [Comm], [OperadAlgebra], the convenience
   constructor and the category of algebras.  The hypothesis sits
   exactly at the PASSAGE from an operadic action to a concrete
   algebraic record, not in the operad theory, which keeps the ambient
   `≈` throughout: the SCOPE paragraph of Structure/Complete.v's size
   note (item 4), read at this file.  It is supplied rather than
   resolved here because [X] is a bare object of [Sets]; every concrete
   carrier in the tree has one, and the analogous hypothesis on a
   CATEGORY is the class [LocallyPropositional] used by
   Adjunction/Additive.v's [hom_ab] and Theory/Algebra/Rig.v's
   [EndRig].

--------
nLab：https://ncatlab.org/nlab/show/algebra+over+an+operad

在一个笛卡尔范畴的对象 [X] 上，运算器 [O] 的代数正好是从 [O] 的基础单对象多范畴到 Theory/Multicategory/Endomorphism.v 的自同态运算器 [EndOperad X] 的多函子。这就是这里 ([OperadAlgebra]) 的定义，因此自同态运算器的经典泛性质——“X 上的 O-代数结构就是从运算器 O ⟶ End(X) 的映射”——在定义上成立 ([OperadAlgebra_is_MultiFunctor])。

便利构造函数。这样的多函子对象映射是强制的（[EndOperad X]的颜色类型是[poly_unit]），因此一个代数由它的作用映射[ohom O n → (pow X n ~> X)]决定，同时在Theory/Multicategory/Operad.v的元数访问器处重新表述恒等/组成/对称性保持（[OperadAction]）；[Build_OperadAlgebra]组装完整的多函子，一劳永逸地处理边界簿记。目标对象的类型转换依赖于该Operad颜色类型的无公理UIP（[operad_obj_UIP]：颜色类型在命题上是[poly_unit]，并且UIP通过类型等价沿着[destruct]传输；[poly_unit]端是通过[UIP_dec]的Hedberg，如同在Theory/Multicategory/Endomorphism.v的[UIP_nat]使用）。

代数范畴。代数的态射是承载映射，在每个元数上交织作用，并具有有限次幂函子性 [pow_map]；捆绑的范畴 [OperadAlgebras] 遵循 Construction/FAlg.v 的首投影惯例。

可交换运算子。 [Comm] 是终端运算子：每个元数都有一个操作（[mhom Γ c := poly_unit]，平凡集合类）。 它在 [Sets] 中的代数是双向的交换幺半群（不宣称有完全的范畴等价；见下面的捆绑注释）： [Comm_algebra_to_CMon]（二元操作 + 零元操作，通过具体上下文中的多函子定律提取结合律/交换律/单位元）和 [CMon_to_Comm_algebra]（通过便利构造函数的 n 重和），捆绑为 [Comm_algebra_CMon]。

仅在正向方向上记录的强度变化。 该段落的早期修订无条件地陈述了方向：每个 [Comm]-代数在 [X : Sets] 上都会产生一个交换幺半群。 自从 PR “代数载体是集合”（2026-09-17）之后，[CMonObject] 携带 [cmon_prop]，[PropEquiv] 为其载体集合族，而 [Comm_algebra_to_CMon] 直接从 [X] 获取其载体集合族； [Sets] 的任意对象不提供其 `≈` 的 [Prop] 镜像，也没有 [LocallyPropositional Sets] 来提供它（Lib/Setoid/Propositional.v，Instance/Sets/Propositional.v 的头部记录了两种测量）。 因此 [Comm_algebra_to_CMon] 将 [PropEquiv (is_setoid X)] 作为截面假设，而 [Comm_algebra_CMon] 的左组件也要求它：

(∀（X : Sets）（PX : PropEquiv（is_setoid X）），OperadAlgebra Comm X → CMonObject) * …

这两个常量是此文件中唯一声明发生变化的常量。REVERSE 方向未被触及——[CMon_to_Comm_algebra] 起始于一个 [CMonObject]，其承载者提供自己的 [cmon_prop]——[Comm]、[OperadAlgebra]、便捷构造函数和代数范畴也是如此。假设正好位于从算子作用到具体代数记录的过渡阶段，而不是在算子理论中，算子理论始终保持环境 `≈`：在 Structure/Complete.v 的大小注释（条目 4）的 SCOPE 段落中，在此文件中阅读。它在此处是提供的而非解决的，因为 [X] 是 [Sets] 的一个裸对象；树中的每个具体承载者都有一个，并且在 CATEGORY 上的类似假设是 Adjunction/Additive.v 的 [hom_ab] 和 Theory/Algebra/Rig.v 的 [EndRig] 使用的 [LocallyPropositional] 类。
*)

(** ** The transparent length kit / ** 透明长度套件 *)

Fixpoint map_length_t {A B : Type} (f : A → B) (l : list A) :
  length (map f l) = length l :=
  match l with
  | [] => eq_refl
  | x :: t => f_equal S (map_length_t f t)
  end.

Fixpoint repeat_length_t {A : Type} (x : A) (n : nat) :
  length (repeat x n) = n :=
  match n with
  | O => eq_refl
  | S k => f_equal S (repeat_length_t x k)
  end.

Definition len_map_repeat {A B : Type} (φ : A → B) (x : A) (n : nat) :
  length (map φ (repeat x n)) = n :=
  eq_trans (map_length_t φ (repeat x n)) (repeat_length_t x n).

(*
The length of a permutation witness's two boundary lists agree; a
   transparent Fixpoint so that concrete witnesses compute.

--------
一个排列见证的两个边界列表的长度一致；一个透明的固定点，以便具体的见证可以计算。
*)
Fixpoint tperm_length {A : Type} {Γ Δ : list A} (p : tperm Γ Δ) :
  length Γ = length Δ :=
  match p with
  | tperm_nil => eq_refl
  | tperm_skip x q => f_equal S (tperm_length q)
  | tperm_swap x y l => eq_refl
  | tperm_trans q r => eq_trans (tperm_length q) (tperm_length r)
  end.

(**
** UIP for the colour type of an operad

    The colour type is propositionally [poly_unit] ([operad_one]), and UIP
    transports backwards along a type equality by [destruct]; on
    [poly_unit] itself, equality is decidable, so Hedberg ([UIP_dec],
    axiom-free) applies.

--------
** 操作代数的颜色类型的 UIP

颜色类型是命题性 [poly_unit] ([operad_one])，且 UIP 可以沿类型等式通过 [destruct] 向后传输；在 [poly_unit] 本身上，等式是可判定的，因此 Hedberg ([UIP_dec]，无公理) 适用。
*)

Lemma operad_obj_UIP (O : Operad) (x y : @mobj (operad_multi O))
  (e1 e2 : x = y) : e1 = e2.
Proof.
  destruct O as [M e]; simpl in *.
  unfold IsOperad in e.
  revert x y e1 e2.
  rewrite e.
  intros.
  apply UIP_dec.
  intros a b.
  destruct a, b.
  now left.
Qed.

(** ** Operad algebras as multifunctors / ** 作为多函子的运算代数 *)

Definition OperadAlgebra (O : Operad) {C : Category}
  `{@Cartesian C} `{@Terminal C} (X : C) : Type :=
  MultiFunctor (operad_multi O) (EndOperad X).

(*
The universal property of the endomorphism operad, definitionally: an
   O-algebra structure on X IS a map of multicategories into End(X).

--------
端同态运算子作的普遍性质，按定义：X 上的 O-代数结构就是一个指向 End(X) 的多范畴映射。
*)
Definition OperadAlgebra_is_MultiFunctor (O : Operad) {C : Category}
  `{@Cartesian C} `{@Terminal C} (X : C) :
  OperadAlgebra O X = MultiFunctor (operad_multi O) (EndOperad X) :=
  eq_refl.

(** ** The convenience constructor / ** 便捷构造函数 *)

Section Build.

Context (O : Operad).
Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (X : C).

Local Notation MO := (operad_multi O).
Local Notation pt := (operad_pt O).

(*
The forced object map: the colour type of [EndOperad X] is
   [poly_unit].

--------
强制对象映射：[EndOperad X] 的颜色类型是 [poly_unit]。
*)
Definition oalg_obj : @mobj MO → poly_unit := λ _, ttt.

(*
The canonical boundary witness: every context is a repeat of the point,
   at the arity that the image context reports.

--------
规范边界见证：每个上下文都是该点的重复，按图像上下文报告的元数。
*)
Definition oalg_ctx (Γ : list (@mobj MO)) :
  Γ = repeat pt (length (map oalg_obj Γ)) :=
  eq_trans (all_repeat O Γ)
           (f_equal (repeat pt) (eq_sym (map_length_t oalg_obj Γ))).

(*
An operad action: the action maps at every arity, respecting [≈], with
   the three preservation laws restated at the accessor level of
   Theory/Multicategory/Operad.v.  The symmetry law conjugates the
   permutation action of the endomorphism operad by the reindexing casts
   normalising [length (map oalg_obj (repeat pt n))] to [n].

--------
一个操作器作用：该作用在每个元数下进行映射，遵守 [≈]，并且三个保持律在 Theory/Multicategory/Operad.v 的访问器层面上重新表述。对称律通过重定义转换将终态操作器的置换作用共轭化，从而将 [length (map oalg_obj (repeat pt n))] 规范化为 [n]。
*)
Record OperadAction : Type := {
  oact (n : nat) : ohom O n → (pow X n ~> X);

  oact_respects (n : nat) : Proper (equiv ==> equiv) (oact n);

  oact_id : oact 1 (oid O) ≈ exl;

  oact_comp (i j n : nat) (f : ohom O (i + S j)) (g : ohom O n) :
    oact (i + (n + j))%nat (ocomp O f g)
      ≈ oact (i + S j)%nat f ∘ graft X i n j (oact n g);

  oact_sym (n : nat) (p : tperm (repeat pt n) (repeat pt n))
    (f : ohom O n) :
    oact n (osym O p f)
      ≈ oact n f
          ∘ pow_cast X (len_map_repeat oalg_obj pt n)
          ∘ perm_act X (perm_map oalg_obj p)
          ∘ pow_cast X (eq_sym (len_map_repeat oalg_obj pt n))
}.

#[local] Instance oact_proper (a : OperadAction) (n : nat) :
  Proper (equiv ==> equiv) (oact a n) := oact_respects a n.

(* Target-object casts collapse on loops, by UIP for the colour type. / 目标对象在循环上投射折叠，由 UIP 为颜色类型处理。 *)
Lemma mtarget_loop {Γ : list (@mobj MO)} (e : pt = pt)
  (f : @mhom MO Γ pt) :
  mtarget_cast e f ≈ f.
Proof.
  rewrite (operad_obj_UIP O _ _ e eq_refl).
  reflexivity.
Qed.

(* Moving an action across a reindexing of its arity. / 将一个操作跨其元数的重新索引进行移动。 *)
Lemma oact_cast (a : OperadAction) {m n : nat} (e : m = n)
  (h : ohom O m) :
  oact a n (mcast (f_equal (repeat pt) e) h)
    ≈ oact a m h ∘ pow_cast X (eq_sym e).
Proof.
  destruct e; simpl.
  rewrite (mcast_id eq_refl h).
  now rewrite id_right.
Qed.

(* The reindexing move along ANY boundary proof between repeat contexts. / 重新索引沿着重复上下文之间的任何边界证明进行。 *)
Lemma oact_cast_any (a : OperadAction) {m n : nat} (e : n = m)
  (E : repeat pt m = repeat pt n) (h : ohom O m) :
  oact a n (mcast E h) ≈ oact a m h ∘ pow_cast X e.
Proof.
  rewrite (mcast_proof_irrel E (f_equal (repeat pt) (eq_sym e)) h).
  rewrite oact_cast.
  now rewrite (pow_cast_irrel X (eq_sym (eq_sym e)) e).
Qed.

(* Conjugating a graft by reindexing casts on all three block sizes. / 通过重新索引所有三种区块大小上的投射来结合一个移植。 *)
Lemma graft_cast {m m' d d' k k' : nat}
  (em : m = m') (ed : d = d') (ek : k = k')
  (E1 : (m + (d + k))%nat = (m' + (d' + k'))%nat)
  (E2 : (m' + S k')%nat = (m + S k)%nat)
  (v : pow X d' ~> X) :
  graft X m d k (v ∘ pow_cast X ed)
    ≈ pow_cast X E2 ∘ graft X m' d' k' v ∘ pow_cast X E1.
Proof.
  destruct em, ed, ek.
  rewrite (pow_cast_refl X E1), (pow_cast_refl X E2).
  rewrite id_right, id_left.
  apply graft_respects.
  rewrite (pow_cast_refl X eq_refl).
  now rewrite id_right.
Qed.

Local Obligation Tactic := idtac.

(*
Assembling the full multifunctor from the action maps: the object map
   is forced, the multimorphism map recasts every context to its repeat
   form and every target to the point, and the three multifunctor laws
   are discharged from the accessor-level laws by the cast calculus.

--------
从作用映射组装完整多函子：对象映射是强制的，多态映射将每个上下文重构为其重复形式，将每个目标映射为点，并且三个多函子定律通过投射演算从访问器级定律中推导出来。
*)
Program Definition Build_OperadAlgebra (α : OperadAction) :
  OperadAlgebra O X := {|
  mf_obj := oalg_obj;
  mf_map := λ Γ c f,
    oact α (length (map oalg_obj Γ))
      (mtarget_cast (operad_obj_contr O c) (mcast (oalg_ctx Γ) f))
|}.
Next Obligation.
  intros α Γ c.
  proper.
  now rewrite X0.
Qed.
Next Obligation.
  intros α a.
  pose proof (operad_obj_contr O a) as Ha; subst a.
  rewrite mtarget_loop.
  rewrite (mcast_id (oalg_ctx [pt]) (mid pt)).
  apply oact_id.
Qed.
Next Obligation.
  intros α Γ1 Γ2 Δ b c f g ez es.
  (* Collapse the slot/target objects and the contexts to repeat form. / 将槽/目标对象和上下文折叠以重复形式。 *)
  pose proof (operad_obj_contr O b) as Hb; subst b.
  pose proof (operad_obj_contr O c) as Hc; subst c.
  pose proof (all_repeat O Γ1) as H1;
  set (n1 := length Γ1) in H1; clearbody n1.
  pose proof (all_repeat O Γ2) as H2;
  set (n2 := length Γ2) in H2; clearbody n2.
  pose proof (all_repeat O Δ) as HD;
  set (nd := length Δ) in HD; clearbody nd.
  subst Γ1 Γ2 Δ.
  rewrite !mtarget_loop.
  (* The unzipped operation and its round trip. / 解压操作及其往返过程。 *)
  set (F := mcast (eq_sym (orep_zip O n1 n2)) f).
  assert (Hf : mcast (orep_zip O n1 n2) F ≈ f) by apply mcast_symm_r.
  clearbody F.
  (* The left side through the operadic composition. / 左侧通过操作组成。 *)
  assert (HL : mcomp f g
                 ≈ mcast (eq_sym (orep_splice O n1 nd n2)) (ocomp O F g)).
  { unfold ocomp.
    rewrite Hf.
    now rewrite mcast_symm_l. }
  rewrite HL.
  rewrite <- Hf.
  rewrite !mcast_trans.
  (* Canonical nat-level boundary equations. / 规范自然级边界方程。 *)
  assert (HS : length (map oalg_obj
                 (repeat pt n1 ++ repeat pt nd ++ repeat pt n2))
                 = (n1 + (nd + n2))%nat)
    by (rewrite map_length_t, !len_app; now rewrite !repeat_length_t).
  assert (HF : length (map oalg_obj (repeat pt n1 ++ pt :: repeat pt n2))
                 = (n1 + S n2)%nat)
    by (rewrite map_length_t, len_app; simpl;
        now rewrite !repeat_length_t).
  assert (HDl : length (map oalg_obj (repeat pt nd)) = nd)
    by apply len_map_repeat.
  assert (Hm : length (map oalg_obj (repeat pt n1)) = n1)
    by apply len_map_repeat.
  assert (Hk : length (map oalg_obj (repeat pt n2)) = n2)
    by apply len_map_repeat.
  (* Reindex all three actions to their canonical arities. / 将所有三个操作重新索引到它们的标准元数。 *)
  rewrite (oact_cast_any α HS).
  rewrite (oact_cast_any α HF).
  rewrite (oact_cast_any α HDl).
  rewrite oact_comp.
  (* Unfold the endomorphism side and settle the cast algebra. / 展开自同态的一侧并解决铸造代数。 *)
  cbn [mcast mcomp EndOperad].
  unfold End_mcast, End_mcomp.
  rewrite (graft_cast Hm HDl Hk
             (f_equal2 Nat.add Hm (f_equal2 Nat.add HDl Hk))
             (eq_sym (f_equal2 Nat.add Hm (f_equal S Hk)))
             (oact α nd g)).
  rewrite <- !comp_assoc.
  rewrite !pow_cast_fuse'.
  rewrite !pow_cast_fuse.
  rewrite pow_cast_refl, id_left.
  apply compose_respects; [reflexivity|].
  apply compose_respects; [reflexivity|].
  apply pow_cast_irrel.
Qed.
Next Obligation.
  intros α Γ Δ c p f.
  pose proof (operad_obj_contr O c) as Hc; subst c.
  pose proof (all_repeat O Γ) as HG;
  set (n := length Γ) in HG; clearbody n.
  pose proof (all_repeat O Δ) as HDl;
  set (n' := length Δ) in HDl; clearbody n'.
  subst Γ Δ.
  pose proof (tperm_length p) as Hnn.
  rewrite !repeat_length_t in Hnn.
  subst n'.
  rewrite !mtarget_loop.
  rewrite !(oact_cast_any α (len_map_repeat oalg_obj pt n)).
  rewrite (oact_sym α n p f).
  cbn [msym EndOperad].
  unfold End_msym.
  rewrite <- !comp_assoc.
  rewrite pow_cast_fuse.
  rewrite pow_cast_refl, id_right.
  reflexivity.
Qed.

End Build.

(**
** The category of O-algebras

    Following the [FAlgHom] idiom of Construction/FAlg.v: a morphism of
    algebras is a carrier map intertwining the actions at every arity,
    through the functorial action [pow_map] on finite powers.

--------
** O-代数的范畴

遵循 Construction/FAlg.v 中的 [FAlgHom] 习惯用法：代数的一个态射是一个承载映射，它在每一个元数上将作用交织，通过 [pow_map] 在有限次幂上的函子作用。
*)

Section Algebras.

Context (O : Operad).
Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(* The arity-n action of an algebra, at the canonical power. / 代数的n元作用，在典范幂上。 *)
Definition alg_act {X : C} (A : OperadAlgebra O X) (n : nat)
  (o : ohom O n) : pow X n ~> X :=
  mf_map A o
    ∘ pow_cast X (eq_sym (len_map_repeat (mf_obj A) (operad_pt O) n)).

(*
Sanity: the convenience constructor does not scramble the action — at
   every arity the assembled multifunctor's action IS the input action,
   the boundary casts fusing away.

--------
理智：便利构造函数不会扰乱动作——在每一种元数下，组装的多函子动作就是输入动作，边界投射被融合掉。
*)
#[local] Instance alg_oact_proper {X : C} (α : OperadAction O X) (n : nat) :
  Proper (equiv ==> equiv) (oact O X α n) := oact_respects O X α n.

Lemma alg_act_Build {X : C} (α : OperadAction O X) (n : nat)
  (o : ohom O n) :
  alg_act (Build_OperadAlgebra O X α) n o ≈ oact O X α n o.
Proof.
  unfold alg_act; simpl.
  rewrite mtarget_loop.
  rewrite (oact_cast_any O X α
             (len_map_repeat (oalg_obj O) (operad_pt O) n)
             (oalg_ctx O (repeat (operad_pt O) n)) o).
  rewrite <- comp_assoc.
  rewrite pow_cast_fuse.
  rewrite pow_cast_refl.
  now rewrite id_right.
Qed.

(* The action of a carrier map on finite powers. / 载体映射在有限幂上的作用。 *)
Fixpoint pow_map {x y : C} (h : x ~> y) (n : nat) :
  pow x n ~> pow y n :=
  match n as m return ((pow x m ~> pow y m) : Type) with
  (* the section variable [O] shadows the [nat] constructor in patterns / section 变量 [O] 在模式中遮蔽了 [nat] 构造函数 *)
  | 0%nat => @id C (pow x 0)
  | S k => Cartesian.split h (pow_map h k)  (* [List.split] shadows / [List.split] 阴影 *)
  end.

Lemma pow_map_id {x : C} (n : nat) : pow_map (id[x]) n ≈ id.
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite IHn.
    apply split_id.
Qed.

Lemma pow_map_comp {x y z : C} (h2 : y ~> z) (h1 : x ~> y) (n : nat) :
  pow_map (h2 ∘ h1) n ≈ pow_map h2 n ∘ pow_map h1 n.
Proof.
  induction n; simpl.
  - now rewrite id_left.
  - rewrite IHn.
    symmetry; apply split_comp.
Qed.

(* An algebra morphism: a carrier map intertwining the actions. / 代数同态：一个承载映射，交织作用。 *)
Class OperadAlgebraHom {X Y : C}
  (A : OperadAlgebra O X) (B : OperadAlgebra O Y) := {
  oalg_hom : X ~> Y;
  oalg_commutes (n : nat) (o : ohom O n) :
    oalg_hom ∘ alg_act A n o ≈ alg_act B n o ∘ pow_map oalg_hom n
}.

End Algebras.

Arguments oalg_hom {O C H H0 X Y A B} _.
Arguments oalg_commutes {O C H H0 X Y A B} _ n o.

(*
The category of O-algebras in C.

       objects: pairs of a carrier and an algebra structure
        arrows: action-intertwining carrier maps
      identity: the identity carrier map
   composition: composition of carrier maps, pasting the squares

--------
C 中的 O-代数范畴。

       对象：承载体和代数结构的对
        箭头：作用交织的承载体映射
      恒等：恒等承载体映射
   复合：承载体映射的复合，将方形图拼接
*)
Program Definition OperadAlgebras (O : Operad) (C : Category)
  `{@Cartesian C} `{@Terminal C} : Category := {|
  obj     := ∃ X : C, OperadAlgebra O X;
  hom     := λ x y, OperadAlgebraHom O (`2 x) (`2 y);
  homset  := λ _ _, {| equiv := λ f g, oalg_hom f ≈ oalg_hom g |};
  id      := λ _, {| oalg_hom := id |};
  compose := λ _ _ _ f g, {| oalg_hom := oalg_hom f ∘ oalg_hom g |}
|}.
Next Obligation.
  rewrite id_left.
  rewrite pow_map_id.
  now rewrite id_right.
Qed.
Next Obligation.
  rewrite pow_map_comp.
  rewrite <- comp_assoc.
  rewrite (oalg_commutes g).
  rewrite !comp_assoc.
  now rewrite (oalg_commutes f).
Qed.

(**
** The commutative operad

    The terminal operad: exactly one operation in every arity, with the
    trivial setoid on each multimorphism carrier.  Every law holds
    trivially.

--------
** 交换算子

    终端算子：在每个元数上恰好有一个运算，每个多态载体上都有平凡等价关系。每条定律都显然成立。
*)

Program Definition Comm_Multi : Multicategory := {|
  mobj := poly_unit;
  mhom := λ _ _, poly_unit;
  mhomset := λ _ _, {| equiv := λ _ _, True |};
  mcast := λ _ _ _ _ f, f;
  mid := λ _, ttt;
  mcomp := λ _ _ _ _ _ _ _, ttt;
  msym := λ _ _ _ _ f, f
|}.

Definition Comm : Operad := {|
  operad_multi := Comm_Multi;
  operad_one := eq_refl
|}.

(**
** Comm-algebras in Sets are commutative monoids

    Forward direction, and since the PR "algebraic carriers are sets"
    (2026-09-17) it asks the carrier for a [PropEquiv]; the strength-change
    paragraph of the file header records why, and names the two constants
    of this file that gained the hypothesis.

    The binary and nullary actions of a Comm-algebra
    furnish the operation and unit; associativity comes from the two ways
    of splicing the binary operation into itself ([mf_comp] at concrete
    contexts), commutativity from the symmetric action at the swap
    witness ([mf_sym]), and the unit law from [mf_comp] against the
    nullary operation combined with [mf_id].  Everything is definitional
    in [Sets], so each law is an instance of the corresponding
    multifunctor law evaluated at a point.

--------
** 集合中的换位代数是交换幺半群

前向方向，由于 PR “代数承载是集合”
（2026-09-17）它询问 [PropEquiv] 的承载；文件头的强度更改段记录了原因，并命名了该文件中获得假设的两个常量。

换位代数的二元和零元作用提供了运算和单位；结合性来自将二元运算自身拼接的两种方式（具体上下文中的 [mf_comp]），交换性来自交换证明处的对称作用（[mf_sym]），单位律来自针对零元运算的 [mf_comp] 结合 [mf_id]。[Sets] 中的一切都是定义性的，因此每个定律都是在某一点处评估的相应多函子定律的实例。
*)

Section CommToCMon.

Context {X : Sets}.
(*
Since the PR "algebraic carriers are sets" (2026-09-17) a [CMonObject]
   carries [cmon_prop], and [Comm_algebra_to_CMon] below takes its carrier
   setoid straight from [X] -- an arbitrary object of [Sets], which supplies
   no [Prop] mirror of its own (Instance/Sets/Propositional.v's header records
   why there is no such instance in general).  The section therefore takes one
   as a hypothesis; every concrete [X] in the tree has one.

--------
自从 PR “代数承载体是集合”（2026-09-17）之后，一个 [CMonObject] 承载 [cmon_prop]，而下面的 [Comm_algebra_to_CMon] 直接从 [X] 获取其承载集合；[X] 是 [Sets] 的一个任意对象，它自身不提供任何 [Prop] 镜像（Instance/Sets/Propositional.v 的头部记录了为什么通常没有这样的实例）。因此，本节将其作为一个假设；树中的每个具体 [X] 都有一个。
*)
Context (PX : PropEquiv (is_setoid X)).
Context (A : OperadAlgebra Comm X).

(* The distinguished actions at concrete arities. / 在具体元数上的显著动作。 *)
Definition comm_mu : pow X 2 ~{Sets}~> X :=
  mf_map A (Γ:=[ttt; ttt]) (c:=ttt) ttt.

Definition comm_eps : pow X 0 ~{Sets}~> X :=
  mf_map A (Γ:=[]) (c:=ttt) ttt.

Definition comm_u1 : pow X 1 ~{Sets}~> X :=
  mf_map A (Γ:=[ttt]) (c:=ttt) ttt.

Definition comm_t3 : pow X 3 ~{Sets}~> X :=
  mf_map A (Γ:=[ttt; ttt; ttt]) (c:=ttt) ttt.

(* The unary action is the projection: [mf_id] at the point. / 一元作用是在该点的投影：[mf_id]。 *)
Lemma comm_u1_id (a : X) (u : poly_unit) : comm_u1 (a, u) ≈ a.
Proof. exact (mf_id A ttt (a, u)). Qed.

(* Commutativity: [mf_sym] at the swap witness. / 交换性：[mf_sym] 在交换证明中。 *)
Lemma comm_mu_comm (a b : X) (u : poly_unit) :
  comm_mu (a, (b, u)) ≈ comm_mu (b, (a, u)).
Proof. exact (mf_sym A (tperm_swap ttt ttt []) ttt (a, (b, u))). Qed.

(* Associativity, left splice: the slot before the passive input. / 结合性，左拼接：被动输入前的插槽。 *)
Lemma comm_assoc_l (a b c : X) (u : poly_unit) :
  comm_t3 (a, (b, (c, u))) ≈ comm_mu (comm_mu (a, (b, ttt)), (c, u)).
Proof.
  exact (mf_comp A (Γ1:=[]) (Γ2:=[ttt]) (Δ:=[ttt; ttt]) (b:=ttt) (c:=ttt)
           ttt ttt eq_refl eq_refl (a, (b, (c, u)))).
Qed.

(* Associativity, right splice: the slot after the passive input. / 结合性，右拼接：被动输入之后的插槽。 *)
Lemma comm_assoc_r (a b c : X) (u : poly_unit) :
  comm_t3 (a, (b, (c, u))) ≈ comm_mu (a, (comm_mu (b, (c, ttt)), u)).
Proof.
  exact (mf_comp A (Γ1:=[ttt]) (Γ2:=[]) (Δ:=[ttt; ttt]) (b:=ttt) (c:=ttt)
           ttt ttt eq_refl eq_refl (a, (b, (c, u)))).
Qed.

(* The unit law: splicing the nullary operation into the binary one. / 幺元律：将零元运算拼接到二元运算中。 *)
Lemma comm_unit_l (a : X) (u : poly_unit) :
  comm_u1 (a, u) ≈ comm_mu (comm_eps ttt, (a, u)).
Proof.
  exact (mf_comp A (Γ1:=[]) (Γ2:=[ttt]) (Δ:=[]) (b:=ttt) (c:=ttt)
           ttt ttt eq_refl eq_refl (a, u)).
Qed.

Local Obligation Tactic := idtac.

Program Definition Comm_algebra_to_CMon : CMonObject := {|
  cmon_setoid := X;
  cmon_zero := comm_eps ttt;
  cmon_plus := λ a b, comm_mu (a, (b, ttt));
  cmon_prop := PX
|}.
Next Obligation.
  intros a a' Ha b b' Hb.
  exact (proper_morphism comm_mu (a, (b, ttt)) (a', (b', ttt))
           (Ha, (Hb, eq_refl))).
Qed.
Next Obligation.
  intros a b c; simpl.
  rewrite <- (comm_assoc_l a b c ttt).
  apply (comm_assoc_r a b c ttt).
Qed.
Next Obligation.
  intros a b; simpl.
  apply (comm_mu_comm a b ttt).
Qed.
Next Obligation.
  intros a; simpl.
  rewrite <- (comm_unit_l a ttt).
  apply (comm_u1_id a ttt).
Qed.

End CommToCMon.

(**
** Commutative monoids are Comm-algebras

    Converse direction, through the convenience constructor: the arity-n
    action is the n-fold sum, identity/composition/symmetry preservation
    are the unit law, the fold-of-a-graft computation, and invariance of
    sums under permutation (associativity + commutativity).

--------
** 交换幺半群是交换代数

反方向，通过便利构造器：arity-n 操作是 n 倍求和，单位/组合/对称性保持是单位律、嫁接的折叠计算，以及在置换下和的不变性（结合律 + 交换律）。
*)

Section CMonToComm.

Context (M : CMonObject).

(* The n-fold sum on the underlying carrier. / 基础承载体上的 n 倍和。 *)
Fixpoint nfold_fn (n : nat) :
  carrier (pow (C:=Sets) (cmon_setoid M) n) → carrier (cmon_setoid M) :=
  match n with
  | 0%nat => λ _, cmon_zero M
  | S k => λ p, cmon_plus M (fst p) (nfold_fn k (snd p))
  end.

Lemma nfold_fn_proper (n : nat) : Proper (equiv ==> equiv) (nfold_fn n).
Proof.
  induction n; simpl.
  - repeat intro.
    reflexivity.
  - intros [a r] [a' r'] [Ha Hr]; simpl.
    apply cmon_plus_respects.
    + exact Ha.
    + now apply IHn.
Qed.

Definition nfold (n : nat) :
  pow (C:=Sets) (cmon_setoid M) n ~{Sets}~> cmon_setoid M := {|
  morphism := nfold_fn n;
  proper_morphism := nfold_fn_proper n
|}.

(* Folding is invariant under boundary reindexing. / 折叠在边界重新索引下是不变的。 *)
Lemma nfold_cast {m n : nat} (e : m = n) :
  nfold n ∘ pow_cast (C:=Sets) (cmon_setoid M) e ≈ nfold m.
Proof.
  destruct e.
  intro x; simpl.
  reflexivity.
Qed.

(* Folding a split context sums the two blocks. / 折叠分割的上下文会将两个块相加。 *)
Lemma nfold_split (d k : nat)
  (x : carrier (pow (C:=Sets) (cmon_setoid M) (d + k))) :
  nfold (d + k) x
    ≈ cmon_plus M
        (nfold d (fst (pow_split (C:=Sets) (cmon_setoid M) d k x)))
        (nfold k (snd (pow_split (C:=Sets) (cmon_setoid M) d k x))).
Proof.
  generalize dependent x.
  induction d as [|d IHd]; intro x; simpl.
  - symmetry; apply cmon_plus_zero_l.
  - destruct x as [a x']; simpl.
    rewrite (IHd x').
    symmetry; apply cmon_plus_assoc.
Qed.

(* Folding through a graft folds the spliced block first. / 通过嫁接折叠首先折叠接合的块。 *)
Lemma nfold_graft (m d k : nat) :
  nfold (m + (d + k))
    ≈ nfold (m + S k) ∘ graft (C:=Sets) (cmon_setoid M) m d k (nfold d).
Proof.
  induction m as [|m IHm]; intro x; simpl.
  - apply nfold_split.
  - destruct x as [a x']; simpl.
    apply cmon_plus_respects.
    + reflexivity.
    + apply (IHm x').
Qed.

(*
Folds are invariant under the permutation action: associativity and
   commutativity, by induction on the witness.

--------
褶皱在置换作用下不变：通过见证的归纳法证明结合性和交换性。
*)
Lemma nfold_perm {Γ Δ : list poly_unit} (q : tperm Γ Δ) :
  nfold (length Γ) ∘ perm_act (C:=Sets) (cmon_setoid M) q ≈ nfold (length Δ).
Proof.
  induction q as [| x Γ0 Δ0 q IH | x y l | Γ0 Δ0 Λ q IHq r IHr].
  - intro z; simpl.
    reflexivity.
  - intros [a v]; simpl.
    apply cmon_plus_respects.
    + reflexivity.
    + apply (IH v).
  - intros [a [b v]]; simpl.
    rewrite <- cmon_plus_assoc.
    rewrite (cmon_plus_comm M b a).
    now rewrite cmon_plus_assoc.
  - intro z; simpl.
    etransitivity.
    + apply (IHq (perm_act (C:=Sets) (cmon_setoid M) r z)).
    + apply (IHr z).
Qed.

Local Obligation Tactic := idtac.

Program Definition CMon_Comm_action :
  OperadAction (C:=Sets) Comm (cmon_setoid M) := {|
  oact := λ n _, nfold n
|}.
Next Obligation.
  intros n f g Hfg.
  reflexivity.
Qed.
Next Obligation.
  intros [a u]; simpl.
  apply cmon_plus_zero_r.
Qed.
Next Obligation.
  intros i j n f g.
  apply nfold_graft.
Qed.
Next Obligation.
  intros n p f.
  rewrite (nfold_cast (len_map_repeat (oalg_obj Comm) (operad_pt Comm) n)).
  rewrite (nfold_perm (perm_map (oalg_obj Comm) p)).
  rewrite (nfold_cast
             (eq_sym (len_map_repeat (oalg_obj Comm) (operad_pt Comm) n))).
  reflexivity.
Qed.

Definition CMon_to_Comm_algebra : OperadAlgebra (C:=Sets) Comm (cmon_setoid M) :=
  Build_OperadAlgebra (C:=Sets) Comm (cmon_setoid M) CMon_Comm_action.

End CMonToComm.

(**
** The two directions, bundled

    The named Comm/CMon connection: a Comm-algebra in [Sets] whose
    carrier setoid has a [PropEquiv] yields a commutative monoid on that
    carrier, and every commutative monoid carries a Comm-algebra
    structure.  (The checklist row asks for the two directions; a full
    categorical equivalence is not claimed here.)

--------
** 这两个方向，捆绑起来

命名的 Comm/CMon 连接：[Sets] 中的 Comm-代数，其承载集合为具有 [PropEquiv] 的集合集合，在该承载集合上产生一个交换幺半群，并且每个交换幺半群都具有 Comm-代数结构。（检查表行要求两个方向；这里并未声称完整的范畴等价。）
*)

(*
AN EARLIER REVISION stated the left component without the [PropEquiv],
   as "a Comm-algebra in [Sets] yields a commutative monoid on its
   carrier".  Since the PR "algebraic carriers are sets" (2026-09-17) a
   [CMonObject] carries [cmon_prop] and a bare [X : Sets] does not supply
   one, so that component now asks for it; see [Comm_algebra_to_CMon]
   above and the strength-change paragraph of the file header.  The right
   component is unchanged: a [CMonObject]'s carrier supplies its own.

--------
早期的修订版将左侧组件表述为没有 [PropEquiv]，即“在 [Sets] 中的交换代数在其载体上产生一个交换幺半群”。由于 PR “代数载体是集合”（2026-09-17），[CMonObject] 承载 [cmon_prop]，而裸 [X : Sets] 不提供，因此现在该组件要求它；参见上文的 [Comm_algebra_to_CMon] 以及文件头的强度变更段落。右侧组件保持不变：[CMonObject] 的载体提供其自身。
*)
Definition Comm_algebra_CMon :
  (∀ (X : Sets) (PX : PropEquiv (is_setoid X))
     (A : OperadAlgebra Comm X), CMonObject)
  * (∀ M : CMonObject, OperadAlgebra (C:=Sets) Comm (cmon_setoid M)) :=
  (λ X PX A, @Comm_algebra_to_CMon X PX A, λ M, CMon_to_Comm_algebra M).
