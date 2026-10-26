Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.

Generalizable All Variables.

(*
nLab: https://ncatlab.org/nlab/show/equivalence+of+categories

   The bundled notion of equivalence of categories.  Where
   [EquivalenceOfCategories F] (Theory/Equivalence.v) is a structure carried
   by a *given* functor F, the bundle [C ≃ D] defined here packages the
   functor together with that structure — a sigma type, in the same split,
   choice-carrying house style as the unbundled classes — so that “C and D
   are equivalent” becomes a single proof-relevant statement about the two
   categories themselves.

   Being equivalent is reflexive ([Equivalence_refl], the identity functor
   quasi-inverted by itself), symmetric ([Equivalence_sym], the
   quasi-inverse with the two cells swapped — [EquivalenceOfCategories_sym]
   of Theory/Equivalence.v), and transitive ([Equivalence_trans], carried
   by the composite functor).  The composite's witness,
   [EquivalenceOfCategories_Compose] below, is proved at the unbundled
   level: the composite of two equivalences is quasi-inverted by the
   composite of the quasi-inverses in the opposite order, its two cells
   obtained by reassociating with [fun_equiv_comp_assoc] and cancelling
   the inner counit/unit cell.

   Naming and hygiene: nothing here is called bare “Equivalence” (that
   name belongs to the standard library's class of equivalence relations);
   the [≃] notation is guarded in [category_theory_scope]; and, as
   everywhere in this development, nothing is registered for instance
   resolution — a quasi-inverse is a choice, so all constructions below
   are plain Definitions, passed explicitly at use sites.

--------
nLab：https://ncatlab.org/nlab/show/equivalence+of+categories

范畴等价的捆绑概念。对于由 *给定* 函子 F 所携带的结构 [EquivalenceOfCategories F]（Theory/Equivalence.v），这里定义的捆绑 [C ≃ D] 将函子与该结构打包在一起——一种 sigma 类型，与非捆绑类的拆分、带选择性的风格相同——因此“C 和 D 是等价的”成为关于这两个范畴本身的单一带有证明信息的陈述。

等价关系是自反的（[Equivalence_refl]，恒等函子由自身准逆元化），对称的（[Equivalence_sym]，将两个单元交换的准逆元 — Theory/Equivalence.v 中的 [EquivalenceOfCategories_sym]），并且是传递的（[Equivalence_trans]，由复合函子承载）。复合的证明者 [EquivalenceOfCategories_Compose] 在非组合级别上被证明：两个等价的复合由准逆元复合的逆序准逆元化，它的两个单元通过 [fun_equiv_comp_assoc] 重新联结并取消内部的余单位/单位单元得到。

命名与卫生：这里没有任何东西被称为裸的“Equivalence”（该名称属于标准库的等价关系类）；[≃] 表示法在 [category_theory_scope] 中受到保护；并且在本开发的各处，实例解析没有任何注册 —— 一个准逆是一个选择，因此下面的所有构造都是普通的定义，在使用时明确传递。
*)

Definition CategoryEquivalence (C D : Category) : Type :=
  ∃ F : C ⟶ D, EquivalenceOfCategories F.

Notation "C ≃ D" := (CategoryEquivalence C%category D%category)
  (at level 91) : category_theory_scope.

(*
Covariant accessors: the underlying functor, its equivalence structure,
   and the chosen quasi-inverse.

--------
协变访问器：底层函子、其等价结构，以及所选择的拟逆元。
*)

Definition equivalence_functor {C D : Category} (E : C ≃ D) : C ⟶ D :=
  `1 E.

Definition equivalence_witness {C D : Category} (E : C ≃ D) :
  EquivalenceOfCategories (`1 E) :=
  `2 E.

Definition equivalence_quasi_inverse {C D : Category} (E : C ≃ D) :
  D ⟶ C :=
  @quasi_inverse C D (`1 E) (`2 E).

(*
Composition of equivalences, at the unbundled level.  The composite
   G ◯ F is quasi-inverted by F′ ◯ G′ (primes denoting the chosen
   quasi-inverses): each cell collapses by reassociation followed by the
   corresponding cell of the inner equivalence, then of the outer one.

--------
在解耦层次上的等价构成。复合 G ◯ F 被 F′ ◯ G′ 准逆（撇号表示所选准逆）准逆化：每个单元通过重新结合后，先经过内部等价的相应单元，再经过外部等价的相应单元而塌缩。
*)

Section Compose.

Context {C D E : Category}.
Context {F : C ⟶ D}.
Context {G : D ⟶ E}.
Context (HF : @EquivalenceOfCategories C D F).
Context (HG : @EquivalenceOfCategories D E G).

Local Notation F' := (@quasi_inverse C D F HF).
Local Notation G' := (@quasi_inverse D E G HG).

Lemma EquivalenceOfCategories_Compose_counit :
  (G ◯ F) ◯ (F' ◯ G') ≈ Id[E].
Proof.
  rewrite <- (fun_equiv_comp_assoc G F (F' ◯ G')).
  rewrite (fun_equiv_comp_assoc F F' G').
  (* the inner counit cell F ◯ F′ ≈ Id[D] cancels the middle / 内余单位单元 F ◯ F′ ≈ Id[D] 抵消了中间部分 *)
  rewrite (@equivalence_counit C D F HF).
  rewrite (fun_equiv_id_left G').
  exact (@equivalence_counit D E G HG).
Qed.

Lemma EquivalenceOfCategories_Compose_unit :
  Id[C] ≈ (F' ◯ G') ◯ (G ◯ F).
Proof.
  rewrite <- (fun_equiv_comp_assoc F' G' (G ◯ F)).
  rewrite (fun_equiv_comp_assoc G' G F).
  (* the inner unit cell Id[D] ≈ G′ ◯ G cancels the middle / 内单元格 Id[D] ≈ G′ ◯ G 抵消中间部分 *)
  rewrite <- (@equivalence_unit D E G HG).
  rewrite (fun_equiv_id_left F).
  exact (@equivalence_unit C D F HF).
Qed.

Definition EquivalenceOfCategories_Compose :
  EquivalenceOfCategories (G ◯ F) :=
  @Build_EquivalenceOfCategories C E (G ◯ F) (F' ◯ G')
    EquivalenceOfCategories_Compose_counit
    EquivalenceOfCategories_Compose_unit.

End Compose.

(*
Equivalence of categories is reflexive, symmetric and transitive.
   These are data-carrying Definitions at the bundled level, not instances
   of the standard library's Reflexive/Symmetric/Transitive classes: the
   bundle is Type-valued and choice-carrying, and must never be conjured
   by resolution.

--------
范畴的等价是自反的、对称的和传递的。这些是在捆绑层次上的承载数据的定义，而不是标准库中自反/对称/传递类的实例：该捆绑是类型值的且承载选择的，绝不能通过解析来凭空生成。
*)

Definition Equivalence_refl (C : Category) : C ≃ C :=
  (Id[C]; @EquivalenceOfCategories_Id C).

Definition Equivalence_sym {C D : Category} (E : C ≃ D) : D ≃ C :=
  (@quasi_inverse C D (`1 E) (`2 E);
   @EquivalenceOfCategories_sym C D (`1 E) (`2 E)).

Definition Equivalence_trans {C D E : Category}
  (E1 : C ≃ D) (E2 : D ≃ E) : C ≃ E :=
  (`1 E2 ◯ `1 E1; EquivalenceOfCategories_Compose (`2 E1) (`2 E2)).

(*
Two sanity corollaries, definitional on the functor components: symmetry
   is involutive on the underlying data, and the functor carried by a
   composite is the composite of the carried functors.

--------
两个理智的推论，在函子组件上是定义性的：对称性在底层数据上是自反的，并且复合所携带的函子是所携带函子的复合。
*)

Corollary Equivalence_sym_involutive {C D : Category} (E : C ≃ D) :
  `1 (Equivalence_sym (Equivalence_sym E)) ≈ `1 E.
Proof. reflexivity. Qed.

Corollary Equivalence_trans_functor {C D E : Category}
  (E1 : C ≃ D) (E2 : D ≃ E) :
  `1 (Equivalence_trans E1 E2) ≈ `1 E2 ◯ `1 E1.
Proof. reflexivity. Qed.
