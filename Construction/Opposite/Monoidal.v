Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Comonoid.Hom.

Generalizable All Variables.

(* * * Monoidal structure on the opposite category / * * 对偶范畴上的幺半群结构 *)

(*
 nLab: https://ncatlab.org/nlab/show/opposite+category
 nLab: https://ncatlab.org/nlab/show/monoidal+category

 A monoidal structure (I, ⨂, λ, ρ, α) on C induces one on C^op: the tensor
 acts the same way on objects, morphisms are tensored by reading the same
 [bimap] against the reversed hom-sets, and the structural isomorphisms are
 the original ones read in the opposite category (so their [to] components
 are the original [from] components, via [Isomorphism_Opposite]).  Every
 coherence obligation is discharged by the corresponding law of C in the
 opposite orientation: the library records both directions of each
 naturality square, and the inverse-direction triangle and pentagon are
 already derived in Structure/Monoidal/Proofs.v, precisely so that this
 dualization is cheap.  A braiding or symmetry likewise transports, with
 the two hexagon identities exchanging roles — the reason Braided.v
 carries both hexagons as data.

 [Monoidal_op], [Braided_op] and [Symmetric_op] are Definitions rather
 than global Instances: registering them would let resolution silently
 equip C^op with a monoidal structure whenever C has one, which is rarely
 what an unannotated goal means (cf. the deferral rationale in
 Theory/Algebra/Comonoid.v).  Callers select them explicitly.

 The payoff is duality transfer for internal algebra: a comonoid in C is
 exactly a monoid in (C^op, Monoidal_op) and vice versa, on the nose (the
 round trips are definitional), and comonoid homomorphisms in C are
 exactly monoid homomorphisms in C^op with source and target exchanged.
 This is packaged both pointwise ([Comonoid_to_op_Monoid] and companions)
 and functorially, as functors Mon(C^op) ⟶ Comon(C)^op and back.

 No involution claim is made for [Monoidal_op]: although (C ∏ C)^op and
 C^op ∏ C^op are convertible, [Opposite_Tensor] and the [Monoidal_op]
 obligations rebuild the functor-law and coherence fields as fresh
 Qed-opaque proof terms, so [Monoidal_op (Monoidal_op M)] is not
 definitionally M even though (C^op)^op = C holds by reflexivity. 

 --------
 nLab: https://ncatlab.org/nlab/show/opposite+category
 nLab: https://ncatlab.org/nlab/show/monoidal+categoryC 上的单模结构 (I, ⨂, λ, ρ, α) 会在 C^op 上诱导出一个单模结构：张量在对象上以相同方式作用，对态射的张量作用通过在反向 Hom 集上阅读相同的 [bimap] 来实现，而结构同构是在对偶范畴中读取的原始同构（因此它们的 [to] 分量是原始 [from] 分量，通过 [Isomorphism_Opposite] 进行转换）。每个相容性义务都通过 C 中相应法律以相反方向解决：库记录了每个自然性方格的两个方向，逆向三角形和五边形已经在 Structure/Monoidal/Proofs.v 中导出，正是为了使得这种对偶化成本低廉。编辫或对称同样可以传输，两条六边形恒等式交换角色——这也是 Braided.v 包含两条六边形作为数据的原因。[Monoidal_op]、[Braided_op] 和 [Symmetric_op] 是定义而非全局实例：注册它们会使得每当 C 拥有一个单态结构时，求解可以自动地为 C^op 配备一个单态结构，而这通常不是未标注目标所想要的（参见 Theory/Algebra/Comonoid.v 中的延迟理由）。调用者需要显式选择它们。

 其好处在于内部代数的对偶性转移：C 中的余单体恰好是 (C^op, Monoidal_op) 中的单体，反之亦然，精确对应（循环操作是定义上的），C 中的余单体同态恰好是 C^op 中的单体同态，且交换了源与目标。此过程既可以点态打包（[Comonoid_to_op_Monoid] 及其相关函数），也可以函子化表示，作为函子 Mon(C^op) ⟶ Comon(C)^op 及其逆。对于 [Monoidal_op] 没有提出任何内卷主张：尽管 (C ∏ C)^op 和 C^op ∏ C^op 可以互换，[Opposite_Tensor] 和 [Monoidal_op] 的约束将函子律和相容性域重建为新的 Qed-opaque 证明项，因此 [Monoidal_op (Monoidal_op M)] 并不是定义上的 M，即使 (C^op)^op = C 由自反性成立。
*)

Section OppositeMonoidal.

Context {C : Category}.

#[local] Obligation Tactic := intros.

(*
 The tensor on C^op: the same object action, with the morphism action
 given componentwise by the tensor of C read against the reversed
 hom-sets.  Note that the domain is the product category C^op ∏ C^op —
 we do not route through a mediating (C ∏ C)^op. 

 --------
 C^op 上的张量：相同的对象作用，其态射作用由组件逐点地给出，通过对逆向同态集读取 C 的张量。注意其定义域是乘积范畴 C^op ∏ C^op——我们不通过中介的 (C ∏ C)^op。
*)
Program Definition Opposite_Tensor `{M : @Monoidal C} :
  C^op ∏ C^op ⟶ C^op := {|
  fobj := fun p => (fst p ⨂[M] snd p)%object;
  fmap := fun x y f => (fst f ⨂[M] snd f)
|}.
Next Obligation.
  (* fmap respects ≈, componentwise. / fmap 在每个组件上尊重 ≈。 *)
  intros f g e; destruct e as [e1 e2]; simpl.
  apply bimap_respects; assumption.
Qed.
Next Obligation.
  simpl.
  apply bimap_id_id.
Qed.
Next Obligation.
  simpl.
  apply bimap_comp.
Qed.

(*
 The monoidal structure on C^op.  The unit is that of C; the unitors and
 associator are those of C read in the opposite category.  Each law of the
 [Monoidal] class then dualizes to a law of C: the to/from naturality
 squares trade places, and the triangle and pentagon become their
 inverse-direction forms from Structure/Monoidal/Proofs.v.

 A Definition, NOT an Instance — callers select it explicitly. 

 --------
 C^op 上的幺半结构。单位是 C 的单位；单元子和结合子是 C 在对偶范畴中的对应。[Monoidal] 类别的每条律则会对偶化为 C 的一条律：正向/反向的自然性方块互换位置，三角形和五边形则变成 Structure/Monoidal/Proofs.v 中的反向形式。

 一个定义，而不是一个实例——调用者需要显式选择它。
*)
Program Definition Monoidal_op `{M : @Monoidal C} : @Monoidal (C^op) := {|
  I            := @I C M;
  tensor       := Opposite_Tensor;
  unit_left    := fun x => Isomorphism_Opposite (@unit_left C M x);
  unit_right   := fun x => Isomorphism_Opposite (@unit_right C M x);
  tensor_assoc := fun x y z => Isomorphism_Opposite (@tensor_assoc C M x y z)
|}.
Next Obligation.
  (*
 to_unit_left_natural in C^op = from_unit_left_natural in C 

 --------
 C^op 中的 to_unit_left_natural = C 中的 from_unit_left_natural
*)
  simpl; symmetry; apply from_unit_left_natural.
Qed.
Next Obligation.
  (*
 from_unit_left_natural in C^op = to_unit_left_natural in C 

 --------
 C^op 中的 from_unit_left_natural = C 中的 to_unit_left_natural
*)
  simpl; symmetry; apply to_unit_left_natural.
Qed.
Next Obligation.
  simpl; symmetry; apply from_unit_right_natural.
Qed.
Next Obligation.
  simpl; symmetry; apply to_unit_right_natural.
Qed.
Next Obligation.
  simpl; symmetry; apply from_tensor_assoc_natural.
Qed.
Next Obligation.
  simpl; symmetry; apply to_tensor_assoc_natural.
Qed.
Next Obligation.
  (*
 Triangle in C^op: ρ⁻¹ ⨂ id ≈ α⁻¹ ∘ (id ⨂ λ⁻¹) in C, the triangle
 identity of C solved for the inverse unitors. 

 --------
 C^op 中的三角形：ρ⁻¹ ⨂ id ≈ α⁻¹ ∘ (id ⨂ λ⁻¹) 在 C 中，C 的三角形恒等式对于逆单位元求解。
*)
  simpl.
  assert (X : (@unit_right C M x)⁻¹ ⨂ to (@unit_left C M y)
                ≈ (@tensor_assoc C M x I y)⁻¹).
  { symmetry.
    rewrite <- (bimap_id_right_left
                  ((@unit_right C M x)⁻¹) (to (@unit_left C M y))).
    rewrite inverse_triangle_identity.
    rewrite comp_assoc.
    rewrite <- bimap_comp.
    rewrite iso_from_to.
    cat. }
  rewrite <- X.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  cat.
Qed.
Next Obligation.
  (* Pentagon in C^op = the inverse pentagon of C. / C^op 中的五边形 = C 的逆五边形。 *)
  simpl.
  rewrite comp_assoc.
  apply inverse_pentagon_identity.
Qed.

(*
 A braiding on C transports to C^op: the braid at (x, y) in C^op is the
 braid at (y, x) in C.  Naturality dualizes to naturality, and the two
 hexagon identities exchange roles. 

 --------
 C 上的编织可以传递到 C^op：C^op 中 (x, y) 的编织是 C 中 (y, x) 的编织。自然性对偶化为自然性，而两个六边形恒等式交换作用。
*)
Program Definition Braided_op `{B : @BraidedMonoidal C} :
  @BraidedMonoidal (C^op) := {|
  braided_is_monoidal := Monoidal_op;
  braid := fun x y => @braid C B y x
|}.
Next Obligation.
  (*
 braid_natural in C^op = braid_natural in C, sides exchanged. 

 --------
 C^op 中的自然编织 = C 中的自然编织，交换了两边。
*)
  intros; simpl.
  symmetry.
  rewrite !comp_assoc.
  exact (@braid_natural C B w z h y x g).
Qed.
Next Obligation.
  (*
 hexagon_identity in C^op = hexagon_identity_sym in C. 

 --------
 C^op 中的六边形恒等式 = C 中的六边形恒等式对称。
*)
  simpl.
  rewrite !comp_assoc.
  exact (@hexagon_identity_sym C B y z x).
Qed.
Next Obligation.
  (*
 hexagon_identity_sym in C^op = hexagon_identity in C. 

 --------
 C^op 中的 hexagon_identity_sym = C 中的 hexagon_identity。
*)
  simpl.
  rewrite !comp_assoc.
  exact (@hexagon_identity C B z x y).
Qed.

(*
 A symmetry on C transports to C^op: the involution law at (x, y) in C^op
 is literally the involution law at (x, y) in C. 

 --------
 C 上的对称性传递到 C^op：在 C^op 中 (x, y) 上的反演律，字面上就是 C 中 (x, y) 上的反演律。
*)
Program Definition Symmetric_op `{S : @SymmetricMonoidal C} :
  @SymmetricMonoidal (C^op) := {|
  symmetric_is_braided := Braided_op
|}.
Next Obligation.
  simpl.
  apply braid_invol.
Qed.

(*
   * ** Duality transfer for internal (co)monoids

   A comonoid on x in C is exactly a monoid on x in (C^op, Monoidal_op):
   the comultiplication reads as a multiplication against the reversed
   hom-sets, coassociativity as associativity, and the counit laws as the
   unit laws.  All four passages below are definitional on the underlying
   data, and the round trips are literal (proved by reflexivity). 

   --------
   * ** 内部（共）幺半群的对偶传递

   在 C 中的 x 上的共幺半群正好是在 (C^op, Monoidal_op) 中 x 上的幺半群：
   对合映射在反转的 Hom 集上被解读为乘法，对结合律的要求对应于结合律，而对余单位律的要求对应于单位律。下面的四种转换在底层数据上都是定义性的，并且往返转换是字面上的（通过自反性证明）。
*)

Program Definition Comonoid_to_op_Monoid `{M : @Monoidal C} {x : C}
  (Cm : @Comonoid C M x) : @Monoid (C^op) Monoidal_op x := {|
  mu  := delta[Cm];
  eta := epsilon[Cm]
|}.
Next Obligation.
  (*
 mu_assoc in C^op unfolds to delta_coassoc in C. 

 --------
 C^op 中的 mu_assoc 展开为 C 中的 delta_coassoc。
*)
  simpl.
  rewrite comp_assoc.
  apply delta_coassoc.
Qed.
Next Obligation.
  simpl.
  apply delta_counit_left.
Qed.
Next Obligation.
  simpl.
  apply delta_counit_right.
Qed.

Program Definition Monoid_to_op_Comonoid `{M : @Monoidal C} {x : C}
  (Mn : @Monoid C M x) : @Comonoid (C^op) Monoidal_op x := {|
  delta   := mu[Mn];
  epsilon := eta[Mn]
|}.
Next Obligation.
  (*
 delta_coassoc in C^op unfolds to mu_assoc in C. 

 --------
 C^op 中的 delta_coassoc 展开为 C 中的 mu_assoc。
*)
  simpl.
  rewrite comp_assoc.
  apply mu_assoc.
Qed.
Next Obligation.
  simpl.
  apply mu_unit_left.
Qed.
Next Obligation.
  simpl.
  apply mu_unit_right.
Qed.

Program Definition op_Monoid_to_Comonoid `{M : @Monoidal C} {x : C}
  (Mn : @Monoid (C^op) Monoidal_op x) : @Comonoid C M x := {|
  delta   := mu[Mn];
  epsilon := eta[Mn]
|}.
Next Obligation.
  spose (@mu_assoc (C^op) Monoidal_op x Mn) as X.
  rewrite <- comp_assoc.
  apply X.
Qed.
Next Obligation.
  spose (@mu_unit_left (C^op) Monoidal_op x Mn) as X.
  apply X.
Qed.
Next Obligation.
  spose (@mu_unit_right (C^op) Monoidal_op x Mn) as X.
  apply X.
Qed.

Program Definition op_Comonoid_to_Monoid `{M : @Monoidal C} {x : C}
  (Cm : @Comonoid (C^op) Monoidal_op x) : @Monoid C M x := {|
  mu  := delta[Cm];
  eta := epsilon[Cm]
|}.
Next Obligation.
  spose (@delta_coassoc (C^op) Monoidal_op x Cm) as X.
  rewrite <- comp_assoc.
  apply X.
Qed.
Next Obligation.
  spose (@delta_counit_left (C^op) Monoidal_op x Cm) as X.
  apply X.
Qed.
Next Obligation.
  spose (@delta_counit_right (C^op) Monoidal_op x Cm) as X.
  apply X.
Qed.

(* Both round trips are definitional on the underlying data. / 两次往返都是基于底层数据的定义性的。 *)

Lemma Comonoid_op_roundtrip `{M : @Monoidal C} {x : C}
  (Cm : @Comonoid C M x) :
  delta[op_Monoid_to_Comonoid (Comonoid_to_op_Monoid Cm)] ≈ delta[Cm]
    ∧ epsilon[op_Monoid_to_Comonoid (Comonoid_to_op_Monoid Cm)] ≈ epsilon[Cm].
Proof. split; reflexivity. Qed.

Lemma Monoid_op_roundtrip `{M : @Monoidal C} {x : C}
  (Mn : @Monoid C M x) :
  mu[op_Comonoid_to_Monoid (Monoid_to_op_Comonoid Mn)] ≈ mu[Mn]
    ∧ eta[op_Comonoid_to_Monoid (Monoid_to_op_Comonoid Mn)] ≈ eta[Mn].
Proof. split; reflexivity. Qed.

(*
   * ** Duality transfer for homomorphisms

   A comonoid homomorphism in C is exactly a monoid homomorphism in C^op
   between the transported monoids, with source and target exchanged (and
   vice versa): the preservation squares are the same equations read
   against the reversed hom-sets. 

   --------
   * ** 同态的对偶传递

   C 中的余单子同态恰好是 C^op 中的单子同态，
   作用于被传递的单子，交换源与目标（反之亦然）：保持性的方块是相同的方程式，
   只是作用于逆向的 Hom 集上。
*)

Lemma ComonoidHom_to_op_MonoidHom `{M : @Monoidal C} {x y : C}
      {Cx : @Comonoid C M x} {Cy : @Comonoid C M y} {f : x ~{C}~> y} :
  ComonoidHom Cx Cy f →
  MonoidHom (Comonoid_to_op_Monoid Cy) (Comonoid_to_op_Monoid Cx) f.
Proof.
  intros F; destruct F as [Fd Fe].
  split; simpl.
  - apply Fd.
  - apply Fe.
Qed.

Lemma op_MonoidHom_to_ComonoidHom `{M : @Monoidal C} {x y : C}
      {Mx : @Monoid (C^op) Monoidal_op x} {My : @Monoid (C^op) Monoidal_op y}
      {f : x ~{C^op}~> y} :
  MonoidHom Mx My f →
  ComonoidHom (op_Monoid_to_Comonoid My) (op_Monoid_to_Comonoid Mx) f.
Proof.
  intros F; destruct F as [Fm Fe].
  split; simpl.
  - apply Fm.
  - apply Fe.
Qed.

#[local] Obligation Tactic := cat_simpl.

(*
 Functorially: Mon(C^op) and Comon(C)^op agree up to the identity on
 underlying data.  The two functors below are mutually inverse on that
 underlying data — the mu/eta/delta/epsilon components and the carrier
 morphisms round-trip definitionally (fmap is the identity on the
 underlying C-morphism) — but NOT on the nose at the record level: each
 object round trip rebuilds the law fields (delta_coassoc etc.) as fresh
 Qed-opaque proof terms, so the round-tripped sigma objects are not
 definitionally equal to the originals (proof-irrelevant, but opaque).
 No isomorphism-of-categories lemma is claimed here; nothing downstream
 needs one. 

 --------
 函子论：Mon(C^op) 和 Comon(C)^op 在底层数据上是相同的。下面的两个函子在底层数据上是相互逆的——mu/eta/delta/epsilon 组件和承载态射定义上可以往返（fmap 在底层 C-态射上是恒等的）——但在记录级别上并不完全相同：每个对象往返转换时会重新构建法律字段（delta_coassoc 等）为新的 Qed-opaque 证明项，所以往返转换后的 sigma 对象在定义上并不等于原始对象（证明不可影响，但不可见）。这里没有声称任何范畴同构引理；下游也不需要。
*)

Program Definition Mon_op_to_Comon_op `{M : @Monoidal C} :
  @Mon (C^op) Monoidal_op ⟶ (@Comon C M)^op := {|
  fobj := fun X => (`1 X; op_Monoid_to_Comonoid `2 X);
  fmap := fun X Y f => (`1 f; op_MonoidHom_to_ComonoidHom `2 f)
|}.

Program Definition Comon_op_to_Mon_op `{M : @Monoidal C} :
  (@Comon C M)^op ⟶ @Mon (C^op) Monoidal_op := {|
  fobj := fun X => (`1 X; Comonoid_to_op_Monoid `2 X);
  fmap := fun X Y f => (`1 f; ComonoidHom_to_op_MonoidHom `2 f)
|}.

End OppositeMonoidal.
