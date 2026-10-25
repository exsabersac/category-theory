Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.

Generalizable All Variables.

(*
 Section proofs below draw on class-instance context variables (the monad and
 its idempotency witness) that need not occur in the stated type, so capture
 every section variable rather than the [Default Proof Using "Type"] subset
 inherited from Lib.v. 

 --------
 下面的小节证明使用了类-实例上下文变量（单子及其幂等性证明），这些变量不必出现在声明的类型中，因此应捕获每一个小节变量，而不是继承自 Lib.v 的 [Default Proof Using "Type"] 子集。
*)
Set Default Proof Using "All".

(*
 nLab: https://ncatlab.org/nlab/show/idempotent+monad

 An idempotent monad on a category C is a monad (M, ret, join) whose
 multiplication join (μ) is an isomorphism at every object.  These are
 exactly the monads that arise from (full) reflective subcategories: the
 monad C ⟶ C of a reflector-inclusion adjunction is idempotent, and every
 idempotent monad reflects C onto its subcategory of M-local (fixed-point)
 objects — those x for which the unit ret x : x ~> M x is invertible.

 This file records both directions of that correspondence together with the
 Eilenberg–Moore reading.  The class [IdempotentMonad] packages the
 join-iso data; several equivalent characterizations are given as lemmas —
 in particular join is invertible at x precisely when ret is invertible at
 M x ([join_iso_iff_ret_M_iso]), and then M ret coincides with ret M
 ([join_iso_fmap_ret]).

 STATUS.  All four checklist artifacts are established at full strength with
 the global context closed:

 - [IdempotentMonad]              — the class.
 - [Reflective_IdempotentMonad]   — a reflective subcategory induces an
 idempotent monad (via the
 adjunction-induced monad U ε F, whose
 join is a functor image of the
 counit, invertible because the counit
 of a full reflective subcategory is).
 - [Idempotent_Reflective]        — an idempotent monad yields a full
 reflective subcategory on its M-local
 objects, with reflector x ↦ M x.
 - [Idempotent_EM_Equivalence]    — the Eilenberg–Moore category of M is
 equivalent (a genuine equivalence of
 categories) to that M-local
 subcategory: for an idempotent monad
 every algebra structure map is the
 inverse of its unit, so algebras and
 local objects coincide.

 No axioms, and hom-equality is the setoid ≈ throughout. 

 --------
 nLab: https://ncatlab.org/nlab/show/idempotent+monad

 在一个范畴 C 上的幂等幺半群（monad）是一个幺半群 (M, ret, join)，其乘法 join (μ) 在每个对象上都是同构。这些恰好是由（全）反射子范畴引出的幺半群：一个反射子-包含adjunction的幺半群 C ⟶ C 是幂等的，并且每个幂等幺半群将 C 反映到其 M-局部（固定点）对象的子范畴——即那些对于它们单位箭头 ret x : x ~> M x 可逆的对象。

 该文件记录了这种对应关系的两个方向，以及 Eilenberg–Moore 的解读。类 [IdempotentMonad] 打包了 join-iso 数据；若干等价的刻画作为引理给出——特别地，join 在 x 上可逆当且仅当 ret 在 M x 上可逆（[join_iso_iff_ret_M_iso]），然后 M ret 与 ret M 一致（[join_iso_fmap_ret]）。状态。所有四个清单工件均已完全建立，并且全局上下文已关闭：-  [IdempotentMonad] — 类。 -  [Reflective_IdempotentMonad] — 一个反射子范畴会诱导出一个幂等单子（通过伴随引出的单子 U ε F，其结合是余单位的函子像，由于一个满反射子范畴的余单位是可逆的，因此可逆）。 -  [Idempotent_Reflective] — 一个幂等单子会在其 M-局部对象上产生一个满反射子范畴，反射函子为 x ↦ M x。-  [Idempotent_EM_Equivalence] — M 的 Eilenberg–Moore 范畴与该 M-局部子范畴等价（真正的范畴等价）：对于幂等单子，每个代数结构映射都是其单位的逆映射，因此代数与局部对象重合。

 没有公理，并且同态相等在整个过程中都是集合论 ≈。
*)

(*
 A functor sends isomorphisms to isomorphisms: this is the [IsIsomorphism]
 (predicate) form, whose two-sided inverse is the functor image of the given
 inverse, with the two inverse laws discharged through [fmap_comp]/[fmap_id].
 (Compare [fobj_iso] in Theory/Functor.v, the bundled [Isomorphism] form.) 

 --------
 函子将同构映射到同构：这是 [IsIsomorphism]（谓词）形式，其双向逆是给定逆的函子像，两个逆律通过 [fmap_comp] / [fmap_id] 得到解决。（参见 Theory/Functor.v 中的 [fobj_iso]，打包的 [Isomorphism] 形式。）
*)
Definition fmap_IsIsomorphism {C D : Category} (F : C ⟶ D) {x y : C}
  (f : x ~> y) (Hf : IsIsomorphism f) : IsIsomorphism (fmap[F] f).
Proof.
  destruct Hf as [g Hr Hl].
  refine {| two_sided_inverse := fmap[F] g |}.
  - rewrite <- fmap_comp, Hr; apply fmap_id.
  - rewrite <- fmap_comp, Hl; apply fmap_id.
Defined.

(*
 nLab: https://ncatlab.org/nlab/show/idempotent+monad

 The defining datum: join (μ) is an isomorphism at every object. 

 --------
 nLab：https://ncatlab.org/nlab/show/idempotent+monad

 定义数据：在每个对象上，联结 (μ) 是同构。
*)
Class IdempotentMonad {C : Category} (M : C ⟶ C) `{@Monad C M} := {
  idem_join_iso {x} : IsIsomorphism (@join C M _ x)
}.

Arguments idem_join_iso {C} M {_ _} x.

(* * * Equivalent characterizations of a single invertible join / * * 单一可逆连接的等效表征 *)

(*
 These describe when the multiplication [join] is invertible at one object;
 none of them presupposes [IdempotentMonad], so each is stated over a bare
 monad and consumed pointwise below. 

 --------
 这些描述了当乘法 [join] 在一个对象上是可逆的时候；它们没有一个假设 [IdempotentMonad]，因此每一个都在一个裸摩纳德上陈述，并在下面逐点使用。
*)

Section Characterizations.

Context {C : Category}.
Context {M : C ⟶ C}.
Context `{@Monad C M}.

(*
 If join x is invertible then so is ret (M x); indeed join x is itself the
 two-sided inverse of ret (M x).  The left inverse law is the monad unit law
 [join_ret]; the right inverse law follows because both ret (M x) and the
 chosen inverse of join x are right inverses of the (monic) join x. 

 --------
 如果 join x 可逆，那么 ret (M x) 也是可逆的；实际上，join x 本身就是 ret (M x) 的双边逆。左逆律是单子单位律 [join_ret]；右逆律成立，因为 ret (M x) 和选定的 join x 的逆都是 (单射) join x 的右逆。
*)
Definition join_iso_ret_iso (x : C)
  (Hj : IsIsomorphism (@join C M _ x)) :
  IsIsomorphism (@ret C M _ (M x)).
Proof.
  refine {| two_sided_inverse := @join C M _ x |}.
  - destruct Hj as [k Hk_r Hk_l].
    assert (Hre : @ret C M _ (M x) ≈ k).
    { apply (comp_inverse_unique (@join C M _ x));
        [ apply (@join_ret C M _ x) | exact Hk_l ]. }
    rewrite Hre; exact Hk_l.
  - apply (@join_ret C M _ x).
Defined.

(*
 Conversely, if ret (M x) is invertible then so is join x, with ret (M x)
 as the inverse (the symmetric inverse-uniqueness argument). 

 --------
 相反，如果 ret (M x) 可逆，那么 join x 也可逆，其逆是 ret (M x)（对称逆的唯一性论证）。
*)
Definition ret_iso_join_iso (x : C)
  (Hr : IsIsomorphism (@ret C M _ (M x))) :
  IsIsomorphism (@join C M _ x).
Proof.
  refine {| two_sided_inverse := @ret C M _ (M x) |}.
  - apply (@join_ret C M _ x).
  - destruct Hr as [k Hk_r Hk_l].
    assert (Hkj : k ≈ @join C M _ x).
    { apply (comp_inverse_unique (@ret C M _ (M x)));
        [ exact Hk_r | apply (@join_ret C M _ x) ]. }
    rewrite <- Hkj; exact Hk_r.
Defined.

(*
 Packaged as the two-way characterization (↔ is [iffT], Lib/Foundation.v). 

 --------
 被打包为双向特性（↔ 是 [iffT]，Lib/Foundation.v）。
*)
Definition join_iso_iff_ret_M_iso (x : C) :
  IsIsomorphism (@join C M _ x) ↔ IsIsomorphism (@ret C M _ (M x)) :=
  (join_iso_ret_iso x, ret_iso_join_iso x).

(*
 When join x is invertible the two unit laws force M ret = ret M at x: both
 fmap ret and ret (M x) are right inverses of the invertible (hence monic)
 join x, so they coincide. 

 --------
 当 join x 可逆时，两个单位律迫使 M ret = ret M 在 x 处：fmap ret 和 ret (M x) 都是可逆（因此是单射） join x 的右逆，所以它们相同。
*)
Definition join_iso_fmap_ret (x : C)
  (Hj : IsIsomorphism (@join C M _ x)) :
  fmap[M] (@ret C M _ x) ≈ @ret C M _ (M x).
Proof.
  destruct Hj as [k Hk_r Hk_l].
  transitivity k.
  - rewrite <- id_left.
    rewrite <- Hk_l.
    rewrite <- comp_assoc.
    rewrite (@join_fmap_ret C M _ x).
    now rewrite id_right.
  - symmetry.
    rewrite <- id_left.
    rewrite <- Hk_l.
    rewrite <- comp_assoc.
    rewrite (@join_ret C M _ x).
    now rewrite id_right.
Qed.

End Characterizations.

(* * * A reflective subcategory induces an idempotent monad / * * 一个反射子范畴引入了一个幂等函子 *)

Section ReflectiveInducesIdempotent.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).

(*
 The counit of the reflection adjunction is invertible at every object of
 the subcategory (predicate form).  Its inverse is the unit read back into
 the subcategory by fullness; the two inverse laws are the triangle identity
 [fmap_counit_unit] and, using naturality of the counit, the other triangle
 identity [counit_fmap_unit].  This mirrors [reflective_counit_iso] of
 Construction/Reflective.v but delivers the [IsIsomorphism] witness of the
 counit itself. 

 --------
 反射伴随的余单位在子范畴（谓词形式）的每个对象上都是可逆的。它的逆是通过满性将单位读回到子范畴中；两个逆律是三角恒等式 [fmap_counit_unit]，并且使用余单位的自然性，另一个三角恒等式 [counit_fmap_unit]。这反映了 Construction/Reflective.v 中的 [reflective_counit_iso]，但提供了余单位本身的 [IsIsomorphism] 证明。
*)
Lemma reflective_counit_IsIso (x : Sub C S) :
  IsIsomorphism
    (@Category.Theory.Adjunction.counit
       (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x).
Proof.
  unshelve econstructor.
  - exists (@Category.Theory.Adjunction.unit
              (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
              (Incl C S x)).
    apply (reflective_full R).
  - apply (@Category.Theory.Adjunction.fmap_counit_unit
             (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x).
  - rewrite <- (counit_naturality (reflective_adj R)).
    apply (@Category.Theory.Adjunction.counit_fmap_unit
             (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
             (Incl C S x)).
Qed.

(*
 The monad on C induced by reflector ⊣ Incl, with join = U ε F. 

 --------
 由反射子 ⊣ Incl 诱导的 C 上的单子，联结 = U ε F。
*)
Definition Reflective_Monad : @Monad C (Incl C S ◯ reflector R) :=
  Adjunction_Induced_Monad (reflective_adj R).

(*
 Its join, being fmap[Incl] of the (invertible) counit, is invertible. 

 --------
 它的结合，由（可逆）余单位的 fmap [Incl] 形成，是可逆的。
*)
Definition Reflective_IdempotentMonad :
  @IdempotentMonad C (Incl C S ◯ reflector R) Reflective_Monad.
Proof.
  refine {| idem_join_iso := _ |}.
  intro x.
  apply (fmap_IsIsomorphism (Incl C S)
           (@Category.Theory.Adjunction.counit
              (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
              (reflector R x))).
  apply reflective_counit_IsIso.
Defined.

End ReflectiveInducesIdempotent.

(*
   * * An idempotent monad yields a reflective subcategory (and EM equivalence) 

   --------
   * * 幂等单子产生一个反射子范畴（以及 Eilenberg-Moore 等价）
*)

Section IdempotentInducesReflective.

Context {C : Category}.
Context {M : C ⟶ C}.
Context `{MM : @Monad C M}.
Context `{IM : @IdempotentMonad C M MM}.

(*
 The M-local objects: those x whose unit ret x is invertible.  The
 subcategory is full — every C-morphism between local objects is retained —
 so [shom] is the terminal predicate. 

 --------
 M-局部对象：那些其单位映射 ret x 可逆的 x。子范畴是满的——本地对象之间的每个 C-态射都被保留——所以 [shom] 是终端谓词。
*)
Definition MLocal_Subcategory : Subcategory C :=
  {| sobj  := fun x => IsIsomorphism (@ret C M MM x)
   ; shom  := fun _ _ _ _ _ => True
   ; scomp := fun _ _ _ _ _ _ _ _ _ _ => I
   ; sid   := fun _ _ => I |}.

(*
 Naturality of the unit-inverses over local objects: for local a, b and any
 h : a ~> b, the inverses of ret intertwine h with fmap h.  This is the
 commuting square shared by the reflection counit and the equivalence
 functors below. 

 --------
 局部对象上的单位逆的自然性：对于局部 a、b 以及任意 h : a ~> b，ret 的逆将 h 与 fmap h 交织。这是下方反射余单位与等价函子共享的交换方阵。
*)
Lemma local_inv_natural {a b : C}
  (oa : IsIsomorphism (@ret C M MM a)) (ob : IsIsomorphism (@ret C M MM b))
  (h : a ~> b) :
  h ∘ @two_sided_inverse C a (M a) (@ret C M MM a) oa
    ≈ @two_sided_inverse C b (M b) (@ret C M MM b) ob ∘ fmap[M] h.
Proof.
  destruct oa as [ta Ha_r Ha_l], ob as [tb Hb_r Hb_l]; simpl.
  assert (Hfm : fmap[M] h ≈ @ret C M MM b ∘ h ∘ ta).
  { rewrite <- (id_right (fmap[M] h)).
    rewrite <- Ha_r.
    rewrite comp_assoc.
    rewrite <- fmap_ret.
    reflexivity. }
  rewrite Hfm, !comp_assoc, Hb_l.
  now rewrite id_left.
Qed.

(* * ** The reflector C ⟶ Sub, x ↦ M x / * ** 反射器 C ⟶ Sub，x ↦ M x *)

Definition idem_reflector_fobj (x : C) : Sub C MLocal_Subcategory :=
  (M x; join_iso_ret_iso x (idem_join_iso M x)).

Definition idem_reflector_fmap {x y : C} (f : x ~> y) :
  idem_reflector_fobj x ~{Sub C MLocal_Subcategory}~> idem_reflector_fobj y :=
  (fmap[M] f; I).

Lemma idem_reflector_fmap_respects {x y : C} (f g : x ~> y) (E : f ≈ g) :
  idem_reflector_fmap f ≈ idem_reflector_fmap g.
Proof. simpl; now rewrite E. Qed.

Lemma idem_reflector_fmap_id {x : C} :
  idem_reflector_fmap (@id C x) ≈ id.
Proof. simpl; apply fmap_id. Qed.

Lemma idem_reflector_fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
  idem_reflector_fmap (f ∘ g) ≈ idem_reflector_fmap f ∘ idem_reflector_fmap g.
Proof. simpl; apply fmap_comp. Qed.

Definition idem_reflector : C ⟶ Sub C MLocal_Subcategory :=
  Build_Functor C (Sub C MLocal_Subcategory)
    idem_reflector_fobj
    (fun x y f => idem_reflector_fmap f)
    (fun x y f g E => idem_reflector_fmap_respects f g E)
    (fun x => idem_reflector_fmap_id)
    (fun x y z f g => idem_reflector_fmap_comp f g).

(*
   * ** Unit and counit of reflector ⊣ Incl, and the adjunction 

   --------
   * ** 反射子 ⊣ Incl 的单位和余单位，以及伴随关系
*)

Lemma idem_unit_natural (x y : C) (f : x ~> y) :
  fmap[Incl C MLocal_Subcategory ◯ idem_reflector] f ∘ @ret C M MM x
    ≈ @ret C M MM y ∘ fmap[Id[C]] f.
Proof. simpl; symmetry; apply fmap_ret. Qed.

Definition idem_unit_transform :
  Id[C] ⟹ (Incl C MLocal_Subcategory ◯ idem_reflector) :=
  Build_Transform'
    (F := Id[C]) (G := Incl C MLocal_Subcategory ◯ idem_reflector)
    (fun x => @ret C M MM x) idem_unit_natural.

Definition idem_counit_transform_fun (y : Sub C MLocal_Subcategory) :
  (idem_reflector ◯ Incl C MLocal_Subcategory) y ~> Id y :=
  (@two_sided_inverse C (`1 y) (M (`1 y)) (@ret C M MM (`1 y)) (`2 y); I).

Lemma idem_counit_natural (x y : Sub C MLocal_Subcategory) (f : x ~> y) :
  fmap[Id[Sub C MLocal_Subcategory]] f ∘ idem_counit_transform_fun x
    ≈ idem_counit_transform_fun y
        ∘ fmap[idem_reflector ◯ Incl C MLocal_Subcategory] f.
Proof. simpl; apply local_inv_natural. Qed.

Definition idem_counit_transform :
  (idem_reflector ◯ Incl C MLocal_Subcategory)
    ⟹ Id[Sub C MLocal_Subcategory] :=
  Build_Transform'
    (F := idem_reflector ◯ Incl C MLocal_Subcategory)
    (G := Id[Sub C MLocal_Subcategory])
    idem_counit_transform_fun idem_counit_natural.

(*
 First triangle identity: at reflector X the counit underlies join X, and
 join X ∘ M ret is the unit law [join_fmap_ret]. 

 --------
 第一个三角恒等式：在反射器 X 上，余单位位于 join X 之下，并且 join X ∘ M ret 是单位律 [join_fmap_ret]。
*)
Lemma idem_triangle_counit (X : C) :
  transform[idem_counit_transform] (idem_reflector X)
    ∘ fmap[idem_reflector] (transform[idem_unit_transform] X) ≈ id.
Proof. cbn; apply (@join_fmap_ret C M MM X). Qed.

(*
 Second triangle identity: at a local object the counit underlies the unit
 inverse, and inverse ∘ ret is [is_left_inverse]. 

 --------
 第二三角恒等式：在一个局部对象上，余单元构成了单位的逆元，并且逆元 ∘ ret 是 [is_left_inverse]。
*)
Lemma idem_triangle_unit (X : Sub C MLocal_Subcategory) :
  fmap[Incl C MLocal_Subcategory] (transform[idem_counit_transform] X)
    ∘ transform[idem_unit_transform] (Incl C MLocal_Subcategory X) ≈ id.
Proof.
  cbn.
  apply (@is_left_inverse C (`1 X) (M (`1 X)) (@ret C M MM (`1 X)) (`2 X)).
Qed.

Definition idem_reflection_transform :
  idem_reflector ∹ Incl C MLocal_Subcategory :=
  {| Transformation.unit             := idem_unit_transform
   ; Transformation.counit           := idem_counit_transform
   ; Transformation.counit_fmap_unit := @idem_triangle_counit
   ; Transformation.fmap_counit_unit := @idem_triangle_unit |}.

Definition idem_reflective_adj :
  idem_reflector ⊣ Incl C MLocal_Subcategory :=
  Adjunction_from_Transform idem_reflection_transform.

(*
 The M-local subcategory is full: every C-morphism between local objects is
 retained. 

 --------
 M-本地子范畴是满的：每个局部对象之间的C-态射都被保留。
*)
Definition MLocal_Full : Construction.Subcategory.Full C MLocal_Subcategory :=
  fun _ _ _ _ _ => I.

(*
 The M-local subcategory is a full reflective subcategory of C. 

 --------
 M-局部子范畴是 C 的一个完全反射子范畴。
*)
Definition Idempotent_Reflective : Reflective MLocal_Subcategory :=
  @Build_Reflective C MLocal_Subcategory
    MLocal_Full idem_reflector idem_reflective_adj.

(*
   * ** Eilenberg–Moore algebras coincide with M-local objects 

   --------
   * ** Eilenberg–Moore 代数与 M-局部对象一致
*)

(*
 Every local object carries a canonical M-algebra whose structure map is the
 inverse of its unit; the action law reduces to fmap (ret⁻¹) = join, both
 being the inverse of fmap ret = ret M. 

 --------
 每个局部对象都携带一个典型的 M-代数，其结构映射是其单位的逆；作用律简化为 fmap (ret⁻¹) = join，两者都是 fmap ret = ret M 的逆。
*)
Definition local_algebra {b : C} (ob : IsIsomorphism (@ret C M MM b)) :
  @TAlgebra C M MM b.
Proof.
  refine {| t_alg := @two_sided_inverse C b (M b) (@ret C M MM b) ob |}.
  - exact (@is_left_inverse C b (M b) (@ret C M MM b) ob).
  - assert (Hfj : fmap[M] (@two_sided_inverse C b (M b) (@ret C M MM b) ob)
                    ≈ @join C M MM b).
    { apply (comp_inverse_unique (fmap[M] (@ret C M MM b))).
      - rewrite <- fmap_comp.
        rewrite (@is_right_inverse C b (M b) (@ret C M MM b) ob).
        apply fmap_id.
      - rewrite (join_iso_fmap_ret b (idem_join_iso M b)).
        apply (@join_ret C M MM b). }
    now rewrite Hfj.
Defined.

(*
 Conversely every algebra makes its carrier local: the algebra map is the
 inverse of the unit.  The left inverse law is the algebra unit law [t_id];
 the right inverse law uses M ret = ret M ([join_iso_fmap_ret]) and [t_id]. 

 --------
 相反，每个代数都会使其承载变为局部：代数映射是单位的逆。左逆律是代数单位律 [t_id]；右逆律使用 M ret = ret M ([join_iso_fmap_ret]) 和 [t_id]。
*)
Definition algebra_ret_iso {a : C} (alg : @TAlgebra C M MM a) :
  IsIsomorphism (@ret C M MM a).
Proof.
  refine {| two_sided_inverse := @t_alg C M MM a alg |}.
  - rewrite fmap_ret.
    rewrite <- (join_iso_fmap_ret a (idem_join_iso M a)).
    rewrite <- fmap_comp.
    rewrite (@t_id C M MM a alg).
    apply fmap_id.
  - exact (@t_id C M MM a alg).
Defined.

(* * ** The comparison functor Sub ⟶ EM and its inverse / * ** 比较函子 Sub ⟶ EM 及其逆函子 *)

Definition idem_G_fobj (s : Sub C MLocal_Subcategory) : EilenbergMoore M :=
  (`1 s; local_algebra (`2 s)).

Definition idem_G_fmap {s t : Sub C MLocal_Subcategory} (f : s ~> t) :
  idem_G_fobj s ~{EilenbergMoore M}~> idem_G_fobj t.
Proof.
  refine {| t_alg_hom := `1 f |}.
  simpl.
  apply local_inv_natural.
Defined.

Lemma idem_G_fmap_respects {s t : Sub C MLocal_Subcategory}
  (f g : s ~> t) (E : f ≈ g) : idem_G_fmap f ≈ idem_G_fmap g.
Proof. simpl; exact E. Qed.

Lemma idem_G_fmap_id {s : Sub C MLocal_Subcategory} :
  idem_G_fmap (@id (Sub C MLocal_Subcategory) s) ≈ id.
Proof. simpl; reflexivity. Qed.

Lemma idem_G_fmap_comp {s t u : Sub C MLocal_Subcategory}
  (f : t ~> u) (g : s ~> t) :
  idem_G_fmap (f ∘ g) ≈ idem_G_fmap f ∘ idem_G_fmap g.
Proof. simpl; reflexivity. Qed.

Definition idem_G : Sub C MLocal_Subcategory ⟶ EilenbergMoore M :=
  Build_Functor (Sub C MLocal_Subcategory) (EilenbergMoore M)
    idem_G_fobj
    (fun s t f => idem_G_fmap f)
    (fun s t f g E => idem_G_fmap_respects f g E)
    (fun s => idem_G_fmap_id)
    (fun s t u f g => idem_G_fmap_comp f g).

(*
 [idem_G] is faithful: EM-morphisms are compared on their underlying arrows,
 which are exactly the underlying arrows of the Sub-morphisms. 

 --------
 [idem_G] 是忠实的：EM-态射是在其基础箭头上进行比较的，而这些正是 Sub-态射的基础箭头。
*)
#[local] Instance idem_G_Faithful : Faithful idem_G.
Proof.
  refine {| fmap_inj := _ |}.
  intros x y f g Hfg; exact Hfg.
Defined.

(*
 [idem_G] is full: any algebra homomorphism is (its underlying arrow lifted
 into the full subcategory). 

 --------
 [idem_G] 是满的：任何代数同态都是（其基础箭头提升到满子范畴中）。
*)
Definition idem_G_prefmap {s t : Sub C MLocal_Subcategory}
  (h : idem_G s ~> idem_G t) : s ~> t := (t_alg_hom[h]; I).

Lemma idem_G_fmap_sur {s t : Sub C MLocal_Subcategory}
  (h : idem_G s ~> idem_G t) : fmap[idem_G] (idem_G_prefmap h) ≈ h.
Proof. simpl; reflexivity. Qed.

#[local] Instance idem_G_Full : Functor.Full idem_G :=
  {| prefmap := @idem_G_prefmap; fmap_sur := @idem_G_fmap_sur |}.

(*
 [idem_G] is essentially surjective: an algebra (a, ν) is the image of the
 local object (a, ret a invertible with inverse ν), up to the identity-arrow
 isomorphism (the two algebra records carry the same structure map ν). 

 --------
 [idem_G] 本质上是满射的：一个代数 (a, ν) 是局部对象 (a, ret a 可逆且其逆为 ν) 的像，最多到恒等箭头同构（两个代数记录携带相同的结构映射 ν）。
*)
Definition idem_eso_obj (z : EilenbergMoore M) : Sub C MLocal_Subcategory :=
  (`1 z; algebra_ret_iso (`2 z)).

Definition idem_eso_iso (z : EilenbergMoore M) :
  idem_G (idem_eso_obj z) ≅ z.
Proof.
  unshelve refine (@Build_Isomorphism (EilenbergMoore M)
    (idem_G (idem_eso_obj z)) z
    {| t_alg_hom := id |} {| t_alg_hom := id |} _ _).
  - cbn; rewrite fmap_id; cat.
  - cbn; rewrite fmap_id; cat.
  - cbn; cat.
  - cbn; cat.
Defined.

#[local] Instance idem_G_ESO : EssentiallySurjective idem_G.
Proof.
  refine {| eso_obj := idem_eso_obj; eso_iso := idem_eso_iso |}.
Defined.

(*
 The Eilenberg–Moore category of the idempotent monad is equivalent to its
 subcategory of M-local objects. 

 --------
 幂等单子（idempotent monad）的 Eilenberg–Moore 范畴与其 M-局部对象子范畴是等价的。
*)
Definition Idempotent_EM_Equivalence : EquivalenceOfCategories idem_G :=
  FF_ESO_Equivalence idem_G.

End IdempotentInducesReflective.
