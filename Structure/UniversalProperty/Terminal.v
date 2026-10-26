Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.UniversalProperty.

Generalizable All Variables.

(* * * Initiality and terminality as universal properties / * * 初始性与终端性作为普遍性质 *)

(*
 Seven Sketches, Remark 6.9: the “unique up to unique isomorphism” slogan is
 not a family of ad-hoc arguments but one theorem about representable
 functors, applied to whatever universal property is at hand.  This block
 makes terminality and initiality instances of the library's generic
 packaging [IsUniversalProperty] (Structure/UniversalProperty.v), so that
 [univ_property_unique_up_to_unique_iso] applies to them literally.

 Orientation.  [IsUniversalProperty] is stated against the COVARIANT
 hom-functor `[Hom c,─] = Hom(c, −)`, so an object satisfying the predicate
 is a representing object for a covariant functor `C ⟶ Sets`.  That is the
 INITIAL shape: `c` is initial exactly when `Hom(c, −) ≅ 1`, the constant
 functor at the singleton setoid.  (Two of the three existing instances
 confirm the reading: Structure/UniversalProperty/Cartesian.v and
 Structure/UniversalProperty/Limit.v both instantiate the class at `C^op`,
 because products and limits are LIMIT-shaped.  The third,
 Structure/UniversalProperty/Universal/Arrow.v, instantiates at `D` rather
 than `D^op`, a universal arrow being colimit-shaped, so it agrees with the
 initial reading taken here.)  Terminality is therefore
 obtained here by instantiating at `C^op`, exactly as Structure/Initial.v
 defines `Initial C := Terminal (C^op)` -- only in the other direction. 

 --------
 七个草图，注释 6.9：“唯一性至唯一同构”的口号不是一系列临时论证，而是关于可表示函子的一条定理，应用于手头的任何普遍性质。这个模块使终对象性和始对象性成为库中通用封装 [IsUniversalProperty]（Structure/UniversalProperty.v）的实例，从而 [univ_property_unique_up_to_unique_iso] 可以字面上应用于它们。方向。[IsUniversalProperty] 是相对于 COVARIANT 同态函子 ` [Hom c,─]ZZ  = Hom(c, −)` 陈述的，因此满足该谓词的对象是协变函子 `C ⟶ Sets` 的表示对象。这就是初始形状：`c` 正好在 `Hom(c, −) ≅ 1` 时是初始的，即单元素集同构的恒等函子。（现有的三个实例中有两个确认了这种理解：Structure/UniversalProperty/Cartesian.v 和 Structure/UniversalProperty/Limit.v 都在 `C^op` 实例化了该类，因为积与极限都是极限形状。第三，Structure/UniversalProperty/Universal/Arrow.v 在 `D` 实例化，而不是在 `D^op` 实例化，通用箭头是余极限形状的，因此它与此处的初始读取一致。因此，通过在 `C^op` 实例化，达到了终端性，正如 Structure/Initial.v 定义 `Initial C := Terminal (C^op)` 一样——只是方向相反。
*)

Lemma poly_unit_uniq (u : poly_unit) : u = ttt.
Proof. now destruct u. Qed.

(*
 The object-level predicates [IsInitialObj] / [IsTerminalObj] now live in
 Structure/Initial.v and Structure/Terminal.v respectively, alongside the
 bundled classes they abstract; this file consumes them. 

 --------
 对象级谓词 [IsInitialObj] / [IsTerminalObj] 现在分别位于 Structure/Initial.v 和 Structure/Terminal.v 中，与它们抽象的捆绑类一起；该文件使用它们。
*)

(*
 [IsUniversalProperty] demands a setoid on the predicate.  The honest choice
 is not the indiscrete relation but the pointwise comparison of the chosen
 arrows; it happens to be total ([IsInitialObj_irrelevant] below), but that
 is a theorem here, not a definition. 

 --------
 [IsUniversalProperty] 要求对谓词使用等价关系。诚实的选择不是不离散的关系，而是对所选箭头的逐点比较；它恰好是总的（见下文的 [IsInitialObj_irrelevant]），但这在这里是一个定理，而不是定义。
*)
#[export]
Program Instance IsInitialObj_Setoid {C : Category} (c : C) :
  Setoid (IsInitialObj c) := {|
  equiv := fun u v => ∀ x : C, unique_obj (u x) ≈ unique_obj (v x)
|}.
Next Obligation.
  equivalence.
  now transitivity (unique_obj (y x0)).
Qed.

(* Any two proofs of initiality agree: the chosen arrows are forced. / 任何两个初始性的证明都是一致的：所选择的箭头是被迫的。 *)
Lemma IsInitialObj_irrelevant {C : Category} (c : C) (u v : IsInitialObj c) :
  u ≈ v.
Proof. intro x; symmetry; apply (uniqueness (v x)); exact I. Qed.

(*
 The functor being represented: the constant functor at the singleton
 setoid, i.e. the terminal object of [Sets] read as a diagram over C. 

 --------
 所表示的函子：单元集合等价类上的常数函子，即作为 C 上的图阅读时 [Sets] 的终对象。
*)
Program Definition ConstOne (C : Category) : C ⟶ Sets := {|
  fobj := fun _ => {| carrier := poly_unit ; is_setoid := Unit_Setoid |};
  fmap := fun _ _ _ => {| morphism := fun u => u |}
|}.

Section InitialUP.
Context (C : Category).

(* Hom(c, −) ⟹ 1: the only thing a map into the singleton can be. / Hom(c, −) ⟹ 1：映射到单元素集的唯一可能。 *)
Program Definition hom_to_one (c : C) :
  @Transform C Sets [Hom c,─] (ConstOne C) :=
  @Build_Transform' C Sets [Hom c,─] (ConstOne C)
    (fun x => {| morphism := fun _ => ttt |}) _.

(*
 1 ⟹ Hom(c, −): pick out the canonical arrow `c ~> x`.  Naturality is
 precisely uniqueness -- `f ∘ !ₓ ≈ !_y` because both are arrows out of an
 initial object. 

 --------
 1 ⟹ Hom(c, −)：选出规范箭头 `c ~> x`。自然性正是唯一性——`f ∘ !ₓ ≈ !_y`，因为它们都是从一个初始对象出发的箭头。
*)
Program Definition one_to_hom (c : C) (u : IsInitialObj c) :
  @Transform C Sets (ConstOne C) [Hom c,─] :=
  @Build_Transform' C Sets (ConstOne C) [Hom c,─]
    (fun x => {| morphism := fun _ => unique_obj (u x) |}) _.
Next Obligation. simpl; intros; symmetry; now apply (uniqueness (u y)). Qed.

(* Initiality of `c` yields the representation Hom(c, −) ≅ 1. / `c` 的初始性产生了表示 Hom(c, −) ≅ 1。 *)
Program Definition initial_to_repr (c : C) (u : IsInitialObj c) :
  @Isomorphism ([C, Sets]) [Hom c,─] (ConstOne C) := {|
  to   := hom_to_one c ;
  from := one_to_hom c u
|}.
Next Obligation. simpl; intros; symmetry; apply poly_unit_uniq. Qed.
Next Obligation. simpl; intros; now apply (uniqueness (u x)). Qed.

(*
 ... and conversely: a representation Hom(c, −) ≅ 1 makes `c` initial.  The
 arrow is the image of the point, and any competitor `v` is pinned by the
 round trip `from ∘ to ≈ id`, since `to _ v` is the point. 

 --------
 ... 相反：一个表示 Hom(c, −) ≅ 1 使 `c` 成为初始对象。箭头是点的像，任何竞争者 `v` 都被往返 `from ∘ to ≈ id` 固定，因为 `to _ v` 是点。
*)
Program Definition repr_to_initial (c : C)
  (t : @Isomorphism ([C, Sets]) [Hom c,─] (ConstOne C)) : IsInitialObj c :=
  fun x => {| unique_obj := from t x ttt ; unique_property := I |}.
Next Obligation.
  assert (K := iso_from_to t x v).
  simpl in K.
  rewrite (poly_unit_uniq (to t x v)) in K.
  rewrite id_left in K; exact K.
Qed.

(*
 The instance.  Being initial IS representing the constant-singleton
 functor, as an isomorphism of setoids in [Sets]. 

 --------
 这个实例。作为初始对象，它表示常量单例函子，作为 [Sets] 中集合子作为同构。
*)
Definition InitialIsUniversalProperty :
  IsUniversalProperty C (@IsInitialObj C) (@IsInitialObj_Setoid C).
Proof.
  unshelve econstructor; [ exact (ConstOne C) | ].
  intro c; unshelve econstructor.
  - unshelve econstructor.
    + exact (initial_to_repr c).
    + (* both representations have the same `to`, and inverses are unique / 两个表示都有相同的 `to`，并且逆元是唯一的 *)
      abstract (repeat intro; apply to_equiv_implies_iso_equiv;
                intros ? ?; reflexivity).
  - unshelve econstructor.
    + exact (repr_to_initial c).
    + abstract (intros t t' Heq x; exact (snd Heq x ttt)).
  - abstract (simpl; intro t; apply to_equiv_implies_iso_equiv;
              intros ? ?; symmetry; apply poly_unit_uniq).
  - abstract (simpl; intros u x; reflexivity).
Defined.

(*
 The payoff, and the proof that the instance is usable: the generic
 Remark-6.9 theorem [univ_property_unique_up_to_unique_iso] applied at this
 instance, with its side condition discharged by
 [IsInitialObj_irrelevant].  Two initial objects are joined by exactly one
 isomorphism -- Remark 3.85 obtained from Remark 6.9 rather than proved
 again. 

 --------
 回报，以及该实例可用的证明：将通用 Remark-6.9 定理 [univ_property_unique_up_to_unique_iso] 应用于该实例，其附带条件由 [IsInitialObj_irrelevant] 解除。两个初始对象通过唯一的同构连接——Remark 3.85 是从 Remark 6.9 得到的，而不是再次证明的。
*)
Program Definition initial_obj_unique_up_to_unique_iso (c d : C)
  (Hc : IsInitialObj c) (Hd : IsInitialObj d) :
  Unique (fun _ : c ≅ d => True) := {|
  unique_obj := unique_obj (univ_property_unique_up_to_unique_iso
                              C (@IsInitialObj C) (@IsInitialObj_Setoid C)
                              InitialIsUniversalProperty c d Hc Hd);
  unique_property := I
|}.
Next Obligation.
  apply (uniqueness (univ_property_unique_up_to_unique_iso
                       C (@IsInitialObj C) (@IsInitialObj_Setoid C)
                       InitialIsUniversalProperty c d Hc Hd)).
  apply IsInitialObj_irrelevant.
Qed.

End InitialUP.

(* ---- the terminal case, by instantiation at C^op ---- / ---- 通过在 C^op 的实例化，终端情况 ---- *)

(*
 [IsTerminalObj] in C and [IsInitialObj] in C^op are the same type: the
 opposite category is defined with `hom x y := hom y x` and
 `homset x y := homset y x`, so even the [Setoid] argument of [Unique]
 matches definitionally.  Both directions are the identity function. 

 --------
 在 C 中的 [IsTerminalObj] 和在 C^op 中的 [IsInitialObj] 是相同的类型：对偶范畴是用 `hom x y := hom y x` 和 `homset x y := homset y x` 定义的，因此即使是 [Unique] 的 [Setoid] 参数在定义上也是匹配的。两个方向都是恒等函数。
*)
Definition IsTerminalObj_op {C : Category} (c : C) :
  IsTerminalObj c -> @IsInitialObj (C^op) c := fun u => u.

Definition op_IsTerminalObj {C : Category} (c : C) :
  @IsInitialObj (C^op) c -> IsTerminalObj c := fun u => u.

(*
 Terminality is a universal property: literally the initial instance,
 instantiated at the opposite category. 

 --------
 终端性是一种普遍属性：字面意思是初始实例，在对偶范畴中实例化。
*)
Definition TerminalIsUniversalProperty (C : Category) :
  IsUniversalProperty (C^op) (@IsInitialObj (C^op)) (@IsInitialObj_Setoid (C^op))
  := InitialIsUniversalProperty (C^op).

(*
 Reading an isomorphism of C^op back as an isomorphism of C.  Both round-trip
 laws are the same terms, since composition in C^op is composition in C with
 the arguments swapped.  (The other direction is [Isomorphism_Opposite] of
 Construction/Opposite.v.) 

 --------
 将 C^op 的同构重新作为 C 的同构进行阅读。两个往返定律是相同的项，因为 C^op 中的组合是在 C 中交换参数的组合。（另一个方向在 Construction/Opposite.v 中是 [Isomorphism_Opposite]。）
*)
Program Definition iso_from_op {C : Category} {x y : C}
  (i : @Isomorphism (C^op) x y) : @Isomorphism C x y := {|
  to   := from i ;
  from := to i
|}.
Next Obligation. exact (iso_to_from i). Qed.
Next Obligation. exact (iso_from_to i). Qed.

(*
 The terminal corollary, routed through the instance: exactly one
 isomorphism between any two objects that are terminal.  Transporting from
 C^op is a pure relabelling -- the `to` of the C-isomorphism is the `from`
 of the C^op-isomorphism -- so uniqueness transports componentwise. 

 --------
 终极推论，通过实例传递：在任何两个终端对象之间恰好有一个同构。从 C^op 传输只是纯粹的重新标记 —— C-同构的 `to` 是 C^op-同构的 `from` —— 因此唯一性按组件传递。
*)
Program Definition terminal_obj_unique_up_to_unique_iso {C : Category} (c d : C)
  (Hc : IsTerminalObj c) (Hd : IsTerminalObj d) :
  Unique (fun _ : c ≅ d => True) := {|
  unique_obj :=
    iso_from_op (unique_obj (initial_obj_unique_up_to_unique_iso
                               (C^op) c d (IsTerminalObj_op c Hc)
                                          (IsTerminalObj_op d Hd)));
  unique_property := I
|}.
Next Obligation.
  assert (K := uniqueness (initial_obj_unique_up_to_unique_iso
                             (C^op) c d (IsTerminalObj_op c Hc)
                                        (IsTerminalObj_op d Hd))
                          (Isomorphism_Opposite v) I).
  destruct K as [K1 K2].
  split; [ exact K2 | exact K1 ].
Qed.

(* ---- the bundled structures satisfy the object-level predicates ---- / ---- 捆绑的结构满足对象级谓词 ---- *)

Program Definition Terminal_IsTerminalObj {C : Category} (T : @Terminal C) :
  IsTerminalObj (@terminal_obj C T) :=
  fun x => {| unique_obj := @one C T x ; unique_property := I |}.
Next Obligation. apply (@one_unique C T). Qed.

Program Definition Initial_IsInitialObj {C : Category} (I0 : @Initial C) :
  IsInitialObj (@initial_obj C I0) :=
  fun x => {| unique_obj := @zero C I0 x ; unique_property := I |}.
Next Obligation. apply (@zero_unique C I0). Qed.

(*
 Finally, Block A and Block B recovered from Block C: the SAME statements as
 [terminal_unique_up_to_unique_iso] / [initial_unique_up_to_unique_iso],
 now derived from the [IsUniversalProperty] instance instead of from
 [one_unique] / [zero_unique] directly.  This is the demonstration that the
 instance is genuinely usable at terminality and initiality. 

 --------
 最后，Block A 和 Block B 从 Block C 恢复了：与 [terminal_unique_up_to_unique_iso] / [initial_unique_up_to_unique_iso] 相同的语句，现在是从 [IsUniversalProperty] 实例中得出，而不是直接从 [one_unique] / [zero_unique] 得出。这证明了该实例在终端性和初始性上确实可用。
*)
Definition terminal_unique_up_to_unique_iso_via_UP {C : Category}
  (T1 T2 : @Terminal C) :
  Unique (fun _ : @terminal_obj C T1 ≅ @terminal_obj C T2 => True) :=
  terminal_obj_unique_up_to_unique_iso _ _
    (Terminal_IsTerminalObj T1) (Terminal_IsTerminalObj T2).

Definition initial_unique_up_to_unique_iso_via_UP {C : Category}
  (I1 I2 : @Initial C) :
  Unique (fun _ : @initial_obj C I1 ≅ @initial_obj C I2 => True) :=
  initial_obj_unique_up_to_unique_iso C _ _
    (Initial_IsInitialObj I1) (Initial_IsInitialObj I2).

(** ------------------------------------------------------------------------ *)