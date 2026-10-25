Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Id.
Require Import Category.Functor.Structure.Monoidal.Compose.

Generalizable All Variables.

(**
* Strict monoidal functors

    nLab: https://ncatlab.org/nlab/show/monoidal+functor
    Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

    A strict monoidal functor is a strong monoidal functor whose comparison
    maps are identities: the unit comparison η : I ≅ F I and the tensor
    comparison μ_{x,y} : F x ⨂ F y ≅ F (x ⨂ y) are not merely invertible but
    equal to [id], so that F preserves the tensor and unit on the nose.

    As with [Structure/Monoidal/Strict.v] (strict monoidal categories), in
    this library's setoid-based setting "strict" requires BOTH:

      (a) object-level Leibniz equalities
            [I = F I]  and  [F x ⨂ F y = F (x ⨂ y)];
      (b) the comparison isomorphisms [pure_iso] and [ap_iso] coincide
          (modulo those equalities) with [id].

    Object-level equality (Leibniz [=]) is required because [obj] in
    [Category] is a [Type], not a setoid; the comparison isos relate
    distinct objects.  The comparisons then transport along those
    equalities to give [id], stated in the explicit
    [match e in _ = T return _ with eq_refl => id end] form — see the
    "Formulation note" at the end of [Structure/Monoidal/Strict.v] for
    the rationale behind this discipline.  The equality directions match
    the [to] directions of [pure_iso : I ≅ F I] and
    [ap_iso : F x ⨂ F y ≅ F (x ⨂ y)].

    Strict monoidal functors compose ([Compose_StrictMonoidalFunctor]) and
    include the identity ([Id_StrictMonoidalFunctor]), forming the wide
    sub-2-category MonCat_strict of MonCat_strong.  They are the morphisms
    of choice between PROPs, whose universal property is stated against
    strict symmetric monoidal targets. 

--------
* 严格幺半群函子

nLab：https://ncatlab.org/nlab/show/monoidal+functor
 维基百科：https://en.wikipedia.org/wiki/Monoidal_functor

严格幺半群函子是强幺半群函子，其比较
 映射是恒等式：单位比较 η : I ≅ F I 和张量
 比较 μ_{x,y} : F x ⨂ F y ≅ F (x ⨂ y) 不仅是可逆的，而且
 等于 [id]，因此 F 保留鼻子上的张量和单位。

与 [Structure/Monoidal/Strict.v]（严格幺半群类别）一样，在
 这个库的基于 setoid 的设置“严格”需要两者：

(a) 对象级莱布尼茨等式
 [I = F I] 和 [F x ⨂ F y = F (x ⨂ y)]；
 (b) 比较同构[pure_iso]和[ap_iso]重合
 （对这些等式取模）与 [id]。

需要对象级相等 (Leibniz [=])，因为 [obj] 在
 [Category] 是 [Type]，而不是 setoid； 比较 iso 相关
 不同的对象。 然后比较沿着那些传输
 给出 [id] 的等式，在显式中说明
 [match e in _ = T return _ with eq_refl => id end] 形式 — 请参阅
 [Structure/Monoidal/Strict.v] 末尾的“配方说明”
 这一纪律背后的基本原理。 相等方向匹配
 [pure_iso : I ≅ F I] 的 [to] 方向和
 [ap_iso : F x ⨂ F y ≅ F (x ⨂ y)]。

严格幺半群函子组成 ([Compose_StrictMonoidalFunctor]) 和
 包括身份（[Id_StrictMonoidalFunctor]），形成宽
 MonCat_strong 的子 2 类别 MonCat_strict。 它们是态射
 PROP 之间的选择，其通用属性受到反对
 严格对称幺半群目标。 
*)

Section StrictMonoidalFunctor.

Context {C D : Category}.
Context `{@Monoidal C}.
Context `{@Monoidal D}.
Context {F : C ⟶ D}.

Class StrictMonoidalFunctor : Type := {
  strict_functor_is_monoidal : @MonoidalFunctor C D _ _ F;

  (** Object-level strictness.  / 对象级严格性。*)
  strict_pure_obj : (@I D _) = F (@I C _);
  strict_ap_obj {x y : C} : (F x ⨂ F y)%object = F (x ⨂ y)%object;

  (** The comparison isomorphisms ARE the identity, transported.  / 比较同构是传输的同一性。*)
  strict_pure_iso_id :
    to (@pure_iso _ _ _ _ F strict_functor_is_monoidal)
      ≈ match strict_pure_obj in _ = T return (@I D _) ~> T
        with eq_refl => id end;

  strict_ap_iso_id {x y : C} :
    to (@ap_iso _ _ _ _ F strict_functor_is_monoidal x y)
      ≈ match @strict_ap_obj x y in _ = T return (F x ⨂ F y)%object ~> T
        with eq_refl => id end
}.
#[export] Existing Instance strict_functor_is_monoidal.

(*
Strict ⇒ strong by field projection; strong ⇒ lax is the library's
   existing [MonoidalFunctor_Is_Lax]. 

--------
场投影严格⇒强； 强⇒宽松是图书馆的
 现有 [MonoidalFunctor_Is_Lax]。 
*)
Coercion strict_functor_is_monoidal : StrictMonoidalFunctor >-> MonoidalFunctor.

End StrictMonoidalFunctor.

Arguments StrictMonoidalFunctor {C D _ _} F.

(**
** Transport helpers

    Composites and images of transported identities are again transported
    identities, along the composite ([eq_trans]) and image ([f_equal])
    equalities respectively.  These discharge the [Compose] instance below
    and are reusable by downstream strictness proofs. 

--------
** 运输帮手

 传输身份的复合材料和图像再次传输
 沿合成 ([eq_trans]) 和图像 ([f_equal]) 的身份
 分别相等。 这些释放了下面的 [Compose] 实例
 并且可以通过下游严格性证明重用。 
*)

Lemma fmap_match_id {C D : Category} (F : C ⟶ D) {x y : C} (e : x = y) :
  fmap[F] (match e in _ = T return x ~> T with eq_refl => id end)
    ≈ match f_equal F e in _ = T return F x ~> T with eq_refl => id end.
Proof. destruct e; simpl; apply fmap_id. Qed.

Lemma match_id_trans {C : Category} {x y z : C} (e1 : x = y) (e2 : y = z) :
  (match e2 in _ = T return y ~> T with eq_refl => id end)
    ∘ (match e1 in _ = T return x ~> T with eq_refl => id end)
    ≈ match eq_trans e1 e2 in _ = T return x ~> T with eq_refl => id end.
Proof. destruct e2, e1; simpl; cat. Qed.

(**
** Closed-form [from] corollaries

    As in [Structure/Monoidal/Strict.v], the [from] direction of each
    comparison iso is the transported identity along the symmetric
    equality; this is forced by uniqueness of inverses
    ([transported_iso_from]), not extra structure. 

--------
** 封闭式 [from] 推论

 与 [Structure/Monoidal/Strict.v] 一样，每个 [from] 方向
 比较 iso 是沿对称轴传输的恒等式
 平等； 这是由逆的唯一性所迫使的
 ([transported_iso_from])，不是额外的结构。 
*)

Section StrictMonoidalFunctorFrom.

Context {C D : Category}.
Context `{@Monoidal C}.
Context `{@Monoidal D}.
Context {F : C ⟶ D}.
Context `{S : @StrictMonoidalFunctor C D _ _ F}.

Corollary strict_pure_iso_from :
  from (@pure_iso _ _ _ _ F strict_functor_is_monoidal)
    ≈ match strict_pure_obj in _ = T return T ~> (@I D _)
      with eq_refl => id end.
Proof.
  apply (transported_iso_from
           strict_pure_obj
           (@pure_iso _ _ _ _ F strict_functor_is_monoidal)).
  apply strict_pure_iso_id.
Qed.

Corollary strict_ap_iso_from {x y : C} :
  from (@ap_iso _ _ _ _ F strict_functor_is_monoidal x y)
    ≈ match @strict_ap_obj _ _ _ _ F S x y in _ = T
        return T ~> (F x ⨂ F y)%object
      with eq_refl => id end.
Proof.
  apply (transported_iso_from
           (@strict_ap_obj _ _ _ _ F S x y)
           (@ap_iso _ _ _ _ F strict_functor_is_monoidal x y)).
  apply strict_ap_iso_id.
Qed.

End StrictMonoidalFunctorFrom.

(**
** Instances

    The identity functor is strict (both object equalities are [eq_refl]
    and the comparisons of [Id_MonoidalFunctor] are identities), and
    strict monoidal functors compose (object equalities by
    [eq_trans]/[f_equal]; the composite comparisons reduce with
    [fmap_match_id] and [match_id_trans]).  These mirror the obligation
    style of [Functor/Structure/Monoidal/{Id,Compose}.v]. 

--------
** 实例

 恒等函子是严格的（两个对象相等性都是 [eq_refl]
 [Id_MonoidalFunctor] 的比较是恒等式），并且
 严格的幺半群函子组成（对象相等性由
 [eq_trans]/[f_equal]； 综合比较减少
 [fmap_match_id] 和 [match_id_trans]）。 这些反映了义务
 [Functor/Structure/Monoidal/{Id,Compose}.v] 的风格。 
*)

#[local] Obligation Tactic := program_simpl.

#[export] Program Instance Id_StrictMonoidalFunctor `{@Monoidal C} :
  StrictMonoidalFunctor (Id[C]) := {
  strict_functor_is_monoidal := Id_MonoidalFunctor;
  strict_pure_obj := eq_refl;
  strict_ap_obj := fun _ _ => eq_refl
}.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

#[export] Program Instance Compose_StrictMonoidalFunctor
  {C D E : Category}
  `{@Monoidal C} `{@Monoidal D} `{@Monoidal E}
  {G : D ⟶ E} {F : C ⟶ D}
  `{SG : @StrictMonoidalFunctor D E _ _ G}
  `{SF : @StrictMonoidalFunctor C D _ _ F} :
  StrictMonoidalFunctor (G ◯ F) := {
  strict_functor_is_monoidal :=
    Compose_MonoidalFunctor
      (@strict_functor_is_monoidal _ _ _ _ G SG)
      (@strict_functor_is_monoidal _ _ _ _ F SF);
  strict_pure_obj :=
    eq_trans (@strict_pure_obj _ _ _ _ G SG)
             (f_equal G (@strict_pure_obj _ _ _ _ F SF));
  strict_ap_obj := fun x y =>
    eq_trans (@strict_ap_obj _ _ _ _ G SG (F x) (F y))
             (f_equal G (@strict_ap_obj _ _ _ _ F SF x y))
}.
Next Obligation.
  unfold fobj_iso; simpl.
  rewrite (@strict_pure_iso_id _ _ _ _ F SF).
  rewrite (@strict_pure_iso_id _ _ _ _ G SG).
  rewrite fmap_match_id.
  apply match_id_trans.
Qed.
Next Obligation.
  simpl.
  pose proof (@strict_ap_iso_id _ _ _ _ F SF x y) as HF; simpl in HF.
  pose proof (@strict_ap_iso_id _ _ _ _ G SG (F x) (F y)) as HG; simpl in HG.
  rewrite HF, HG.
  rewrite fmap_match_id.
  apply match_id_trans.
Qed.
