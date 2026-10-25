Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Category.Construction.Funny.Bifunctor.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(*
   * * Unitors for the funny tensor product

   The terminal category [1] (Instance/One.v) is the unit of the funny
   tensor product: [1 □ C ≅ C ≅ C □ 1], and the isomorphisms are strict —
   they live in [StrictCat], with the round trips equal to the identity
   functor in [Functor_StrictEq_Setoid], not merely naturally isomorphic
   to it.  Through the comparison functor [StrictCat_to_Cat]
   (Instance/StrictCat/ToCat.v) each unitor also yields an isomorphism in
   the weak [Cat] ([Funny_unit_left_cat], [Funny_unit_right_cat]).

   The forward directions are packaged through the separately-functorial
   eliminator [FunnyUP] (Construction/Funny.v): a word in [1 □ C] is
   folded by sending the (identity) [1]-steps to [id] and the [C]-steps to
   themselves.  The backward directions are the injections [FunnyR ttt]
   and [FunnyL ttt] — the injection at the lone object of [1] IS the
   inverse.  One round trip is definitional up to [id_left]; the other
   collapses a word to its composite, which the congruence [feq] proves
   equal to the original word one head step at a time
   ([Funny_strict_eq], StrictEq.v).

   [Funny_unit_left_natural]/[Funny_unit_left_from_natural] (and their
   right-hand duals) are the strict naturality squares of the unitors
   against [FunnyBimap] (Bifunctor.v), in the exact shape consumed by the
   [to_unit_left_natural] (etc.) fields of the [Monoidal] instance on
   [StrictCat] (Instance/StrictCat/Funny.v).

   All coherence statements live in [Functor_StrictEq_Setoid] — the
   hom-setoid of [StrictCat] — because the funny tensor product is not
   invariant under equivalence of categories (see the header of
   Construction/Funny.v). 

   --------
   * * 有趣张量积的单位元

   终范畴  [1]  (Instance/One.v) 是有趣张量积的单位元：  [1 □ C ≅ C ≅ C □ 1] ，且同构是严格的——
   它们存在于  [StrictCat] ，往返等于  [Functor_StrictEq_Setoid] 中的恒等函子，而不仅仅是自然同构。
   通过比较函子  [StrictCat_to_Cat] 
   (Instance/StrictCat/ToCat.v) 每个单位元也在弱  [Cat]  ( [Funny_unit_left_cat] ,  [Funny_unit_right_cat] ) 中产生一个同构。正向方向通过单独函子化的消去器 [FunnyUP]（Construction/Funny.v）进行打包：[1 □ C] 中的一个词通过将（恒等）[1] 步发送到 [id] 并将 [C] 步发送到它们自身来折叠。反向方向是注入 [FunnyR ttt] 和 [FunnyL ttt]——[1] 唯一对象处的注入就是逆映射。一轮往返在 [id_left] 下是定义上的；另一轮则将一个词简化为其复合，恒等关系 [feq] 证明它与原词相等，一次头部步骤处理一条（[Funny_strict_eq], StrictEq.v）。[Funny_unit_left_natural] / [Funny_unit_left_from_natural]（以及它们的右手对偶）是关于 [FunnyBimap]（Bifunctor.v）的单位元的严格自然性方格，其形状正好适用于 [to_unit_left_natural]（等等）字段，这些字段属于 [StrictCat] 上 [Monoidal] 实例（Instance/StrictCat/Funny.v）。

   所有的相干性陈述都存在于 [Functor_StrictEq_Setoid] —— [StrictCat] 的 hom-集合同构中 —— 因为有趣的张量积在范畴等价下不保持不变（参见 Construction/Funny.v 的标题）。
*)

(** ** The left unitor [1 □ C ≅ C] / ** 左单位元 [1 □ C ≅ C] *)

(*
 Forward action as separately functorial data: [1]-steps die, [C]-steps
 pass through. 

 --------
 作为单独函子数据的前向动作：[1] - 步骤消失，[C] - 步骤通过。
*)
Program Definition Funny_unit_left_sep {C : Category} :
  SepFunctorial (C:=1) (D:=C) (E:=C) (fun _ c => c) := {|
  sf_lmap := fun _ _ _ _ => id;
  sf_rmap := fun _ _ _ g => g
|}.

Definition Funny_unit_left_to {C : Category} : (1 □ C) ⟶ C :=
  FunnyUP Funny_unit_left_sep.

(* The injection at the lone object of [1] is the inverse. / [1] 的孤立对象上的注射是逆的。 *)
Definition Funny_unit_left_from {C : Category} : C ⟶ (1 □ C) :=
  FunnyR (C:=1) ttt.

(*
 The object round trip [(ttt, d) = (u, d)] on [1 □ C], definitionally
 [eq_refl] once [u] is destructed; kept transparent so the transports in
 [Funny_strict_eq] vanish by computation.  [poly_unit] has only
 propositional eta ([u] is not convertible to [ttt]), whence the match
 here and in the mirrored [funny_unit_right_obj] below.  (The pair match
 needed because [prod] lacks definitional eta lives inside
 [Funny_strict_eq] itself, StrictEq.v.) 

 --------
 对象 round trip [(ttt, d) = (u, d)] 在 [1 □ C] 上，定义上 [eq_refl] 一旦 [u] 被销毁；保持透明，因此 [Funny_strict_eq] 中的传输通过计算消失。[poly_unit] 只有命题 eta（[u] 不能转换为 [ttt]），因此这里以及下面镜像的 [funny_unit_right_obj] 中的匹配。（需要配对匹配，因为 [prod] 缺乏定义性 eta 存在于 [Funny_strict_eq] 本身，StrictEq.v 中。）
*)
Definition funny_unit_left_obj {C : Category} (u : poly_unit) (d : C) :
  @eq (obj[1 □ C]) (ttt, d) (u, d) :=
  match u as p return (@eq (obj[1 □ C]) (ttt, d) (p, d)) with
  | ttt => eq_refl
  end.

Lemma funny_unit_left_to_from {C : Category} :
  @equiv _ (@Functor_StrictEq_Setoid C C)
    (Funny_unit_left_to ◯ Funny_unit_left_from) Id.
Proof.
  apply (Functor_StrictEq_intro
           (Funny_unit_left_to ◯ Funny_unit_left_from) Id
           (fun _ => eq_refl)).
  intros c c' f.
  (* id ∘ f ≈ f, up to the (trivial) transports / id ∘ f ≈ f，最多只需（平凡的）迁移 *)
  exact (id_left f).
Qed.

(*
 NOTE on proof style below: tactic-level [apply feq_trans] and friends
 choke here, because unification must assign object evars like
 [ttt : poly_unit] against the not-yet-solved [obj[?C]] — the objects and
 homs of [1] reduce to [poly_unit], erasing the projection structure that
 would determine the category.  Explicit [@]-applications supply the
 categories first, and conversion silently discharges the (definitionally
 trivial) transports. 

 --------
 下面关于证明风格的说明：战术级别的 [apply feq_trans] 和相关项在此卡住，因为统一必须将对象占位符（evars）如 [ttt : poly_unit] 分配给尚未解决的 [obj[?C] —— [1] 的对象和同态化为 [poly_unit]，从而消除了原本可以确定类别的投影结构。显式的 [@] 应用先提供类别，而转换会悄然处理（在定义上是平凡的）传输。
*)

Lemma funny_unit_left_from_to {C : Category} :
  @equiv _ (@Functor_StrictEq_Setoid (1 □ C) (1 □ C))
    (Funny_unit_left_from ◯ Funny_unit_left_to) Id.
Proof.
  apply (Funny_strict_eq (Funny_unit_left_from ◯ Funny_unit_left_to) Id
           funny_unit_left_obj).
  - intros u u' f d.
    destruct u, u', f.
    (*
 feq (rstep (id ∘ id)) (lstep ttt); note ttt ≡ id[1] 

 --------
 feq (rstep (id ∘ id)) (lstep ttt); 注意 ttt ≡ id [1]
*)
    exact (@feq_trans _1 C ttt d ttt d
             (@rstep _1 C ttt d d (@compose C d d d (@id C d) (@id C d)))
             (@rstep _1 C ttt d d (@id C d))
             (@lstep _1 C ttt ttt d (@id _1 ttt))
             (@feq_consR _1 C ttt d d
                (@compose C d d d (@id C d) (@id C d)) (@id C d) ttt d
                (@fnil _1 C ttt d) (@fnil _1 C ttt d)
                (@id_left C d d (@id C d))
                (@feq_refl _1 C ttt d ttt d (@fnil _1 C ttt d)))
             (@feq_trans _1 C ttt d ttt d
                (@rstep _1 C ttt d d (@id C d))
                (@fnil _1 C ttt d)
                (@lstep _1 C ttt ttt d (@id _1 ttt))
                (@feq_idR _1 C ttt d ttt d (@fnil _1 C ttt d))
                (@feq_sym _1 C ttt d ttt d
                   (@lstep _1 C ttt ttt d (@id _1 ttt))
                   (@fnil _1 C ttt d)
                   (@feq_idL _1 C ttt d ttt d (@fnil _1 C ttt d))))).
  - intros u d d' g.
    destruct u.
    (* feq (rstep (id ∘ g)) (rstep g) / feq (rstep (id ∘ g)) (rstep g) *)
    exact (@feq_consR _1 C ttt d d'
             (@compose C d d' d' (@id C d') g) g ttt d'
             (@fnil _1 C ttt d') (@fnil _1 C ttt d')
             (@id_left C d d' g)
             (@feq_refl _1 C ttt d' ttt d' (@fnil _1 C ttt d'))).
Qed.

Definition Funny_unit_left {C : Category} : (1 □ C) ≅[StrictCat] C :=
  @Build_Isomorphism StrictCat (1 □ C) C
    Funny_unit_left_to Funny_unit_left_from
    funny_unit_left_to_from funny_unit_left_from_to.

(** ** The right unitor [C □ 1 ≅ C] / ** 右结合子 [C □ 1 ≅ C] *)

(*
 Forward action: [C]-steps pass through, [1]-steps die. 

 --------
 前向动作：[C] - 步骤通过，[1] - 步骤失败。
*)
Program Definition Funny_unit_right_sep {C : Category} :
  SepFunctorial (C:=C) (D:=1) (E:=C) (fun c _ => c) := {|
  sf_lmap := fun _ _ f _ => f;
  sf_rmap := fun _ _ _ _ => id
|}.

Definition Funny_unit_right_to {C : Category} : (C □ 1) ⟶ C :=
  FunnyUP Funny_unit_right_sep.

Definition Funny_unit_right_from {C : Category} : C ⟶ (C □ 1) :=
  FunnyL (D:=1) ttt.

Definition funny_unit_right_obj {C : Category} (c : C) (u : poly_unit) :
  @eq (obj[C □ 1]) (c, ttt) (c, u) :=
  match u as p return (@eq (obj[C □ 1]) (c, ttt) (c, p)) with
  | ttt => eq_refl
  end.

Lemma funny_unit_right_to_from {C : Category} :
  @equiv _ (@Functor_StrictEq_Setoid C C)
    (Funny_unit_right_to ◯ Funny_unit_right_from) Id.
Proof.
  apply (Functor_StrictEq_intro
           (Funny_unit_right_to ◯ Funny_unit_right_from) Id
           (fun _ => eq_refl)).
  intros c c' f.
  (* id ∘ f ≈ f, up to the (trivial) transports / id ∘ f ≈ f，最多只需（平凡的）迁移 *)
  exact (id_left f).
Qed.

Lemma funny_unit_right_from_to {C : Category} :
  @equiv _ (@Functor_StrictEq_Setoid (C □ 1) (C □ 1))
    (Funny_unit_right_from ◯ Funny_unit_right_to) Id.
Proof.
  apply (Funny_strict_eq (Funny_unit_right_from ◯ Funny_unit_right_to) Id
           funny_unit_right_obj).
  - intros c c' f u.
    destruct u.
    (* feq (lstep (id ∘ f)) (lstep f) / feq (lstep (id ∘ f)) (lstep f) *)
    exact (@feq_consL C _1 c c' ttt
             (@compose C c c' c' (@id C c') f) f c' ttt
             (@fnil C _1 c' ttt) (@fnil C _1 c' ttt)
             (@id_left C c c' f)
             (@feq_refl C _1 c' ttt c' ttt (@fnil C _1 c' ttt))).
  - intros c u u' g.
    destruct u, u', g.
    (*
 feq (lstep (id ∘ id)) (rstep ttt); note ttt ≡ id[1] 

 --------
 feq (lstep (id ∘ id)) (rstep ttt); 注意 ttt ≡ id [1]
*)
    exact (@feq_trans C _1 c ttt c ttt
             (@lstep C _1 c c ttt (@compose C c c c (@id C c) (@id C c)))
             (@lstep C _1 c c ttt (@id C c))
             (@rstep C _1 c ttt ttt (@id _1 ttt))
             (@feq_consL C _1 c c ttt
                (@compose C c c c (@id C c) (@id C c)) (@id C c) c ttt
                (@fnil C _1 c ttt) (@fnil C _1 c ttt)
                (@id_left C c c (@id C c))
                (@feq_refl C _1 c ttt c ttt (@fnil C _1 c ttt)))
             (@feq_trans C _1 c ttt c ttt
                (@lstep C _1 c c ttt (@id C c))
                (@fnil C _1 c ttt)
                (@rstep C _1 c ttt ttt (@id _1 ttt))
                (@feq_idL C _1 c ttt c ttt (@fnil C _1 c ttt))
                (@feq_sym C _1 c ttt c ttt
                   (@rstep C _1 c ttt ttt (@id _1 ttt))
                   (@fnil C _1 c ttt)
                   (@feq_idR C _1 c ttt c ttt (@fnil C _1 c ttt))))).
Qed.

Definition Funny_unit_right {C : Category} : (C □ 1) ≅[StrictCat] C :=
  @Build_Isomorphism StrictCat (C □ 1) C
    Funny_unit_right_to Funny_unit_right_from
    funny_unit_right_to_from funny_unit_right_from_to.

(*
   * ** The unitors in the weak [Cat]

   Strict isomorphism refines isomorphism-up-to-natural-isomorphism, so
   the comparison functor transfers both unitors to [Cat] for free. 

   --------
   * ** 在弱 [Cat] 中的单位元同构器

   严格同构精炼了至自然同构的同构，因此比较函子会免费将两个单位元同构器传递到 [Cat]。
*)

Definition Funny_unit_left_cat {C : Category} : (1 □ C) ≅[Cat] C :=
  fobj_iso StrictCat_to_Cat (1 □ C) C Funny_unit_left.

Definition Funny_unit_right_cat {C : Category} : (C □ 1) ≅[Cat] C :=
  fobj_iso StrictCat_to_Cat (C □ 1) C Funny_unit_right.

(*
   * ** Strict naturality of the unitors

   The four squares below are, verbatim, the [to_unit_left_natural],
   [from_unit_left_natural], [to_unit_right_natural] and
   [from_unit_right_natural] fields of the [Monoidal] instance on
   [StrictCat], with [bimap] instantiated at [FunnyBimap].  Both
   composites in each square agree definitionally on objects, and on the
   generating steps up to [id_left]/[fmap_id], so [Funny_strict_eq]
   (resp. [Functor_StrictEq_intro] for the functors out of a plain
   category) closes them without any word induction. 

   --------
   * ** 单元自然性的严格性

   下面的四个方格是 [Monoidal] 实例在 [StrictCat] 上，[bimap] 在 [FunnyBimap] 处实例化时的 [to_unit_left_natural]、[from_unit_left_natural]、[to_unit_right_natural] 和 [from_unit_right_natural] 字段的逐字描述。每个方格中的组合在对象上以及在生成步骤到 [id_left] / [fmap_id] 上在定义上都是一致的，因此 [Funny_strict_eq]（对于来自普通范畴的函子则是 [Functor_StrictEq_intro]）无需任何词诱导就将它们闭合。
*)

Lemma Funny_unit_left_natural {x y : Category} (g : x ⟶ y) :
  @equiv _ (@Functor_StrictEq_Setoid (1 □ x) y)
    (g ◯ Funny_unit_left_to) (Funny_unit_left_to ◯ FunnyBimap Id[1] g).
Proof.
  apply (Funny_strict_eq (g ◯ Funny_unit_left_to)
           (Funny_unit_left_to ◯ FunnyBimap Id[1] g) (fun _ _ => eq_refl)).
  - intros u u' f d; unfold transport_r; simpl.
    (* fmap[g] (id ∘ id) ≈ id ∘ id / fmap [g] (id ∘ id) ≈ id ∘ id *)
    cat.
  - intros u c c' h; unfold transport_r; simpl.
    (* fmap[g] (id ∘ h) ≈ id ∘ fmap[g] h / fmap [g] (id ∘ h) ≈ id ∘ fmap [g] h *)
    cat.
Qed.

Lemma Funny_unit_left_from_natural {x y : Category} (g : x ⟶ y) :
  @equiv _ (@Functor_StrictEq_Setoid x (1 □ y))
    (FunnyBimap Id[1] g ◯ Funny_unit_left_from) (Funny_unit_left_from ◯ g).
Proof.
  apply (Functor_StrictEq_intro
           (FunnyBimap Id[1] g ◯ Funny_unit_left_from)
           (Funny_unit_left_from ◯ g) (fun _ => eq_refl)).
  intros c c' h.
  (* rstep (fmap[g] h) on both sides, definitionally / 在两边定义上，rstep (fmap [g] h) *)
  reflexivity.
Qed.

Lemma Funny_unit_right_natural {x y : Category} (g : x ⟶ y) :
  @equiv _ (@Functor_StrictEq_Setoid (x □ 1) y)
    (g ◯ Funny_unit_right_to) (Funny_unit_right_to ◯ FunnyBimap g Id[1]).
Proof.
  apply (Funny_strict_eq (g ◯ Funny_unit_right_to)
           (Funny_unit_right_to ◯ FunnyBimap g Id[1]) (fun _ _ => eq_refl)).
  - intros c c' f u; unfold transport_r; simpl.
    (* fmap[g] (id ∘ f) ≈ id ∘ fmap[g] f / fmap [g] (id ∘ f) ≈ id ∘ fmap [g] f *)
    cat.
  - intros c u u' f; unfold transport_r; simpl.
    (* fmap[g] (id ∘ id) ≈ id ∘ id / fmap [g] (id ∘ id) ≈ id ∘ id *)
    cat.
Qed.

Lemma Funny_unit_right_from_natural {x y : Category} (g : x ⟶ y) :
  @equiv _ (@Functor_StrictEq_Setoid x (y □ 1))
    (FunnyBimap g Id[1] ◯ Funny_unit_right_from) (Funny_unit_right_from ◯ g).
Proof.
  apply (Functor_StrictEq_intro
           (FunnyBimap g Id[1] ◯ Funny_unit_right_from)
           (Funny_unit_right_from ◯ g) (fun _ => eq_refl)).
  intros c c' h.
  (* lstep (fmap[g] h) on both sides, definitionally / 在两边定义地对 lstep (fmap [g] h) *)
  reflexivity.
Qed.
