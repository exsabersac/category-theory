Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Identity and composition of hom-set adjunctions  / * 同组附加词的同一性和组成*)

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   Adjunctions compose. Given F ⊣ U with F : D ⟶ C (the convention of
   Theory/Adjunction.v: F is the left adjoint) and F' ⊣ U' with F' : C ⟶ E,
   the composite functors are again adjoint: F' ◯ F ⊣ U ◯ U'. In the hom-set
   presentation this is literally composition of the two adjunction
   isomorphisms in Sets,

       (F' (F x) ~{E}~> y)  ≊  (F x ~{C}~> U' y)  ≊  (x ~{D}~> U (U' y)),

   pasted by [iso_compose]; each naturality field of the composite is the
   corresponding field of one constituent placed under the transpose of the
   other (the transposes are setoid morphisms, so they respect ≈ — this is
   [to_adj_respects]/[from_adj_respects]).

   The identity functor is self-adjoint via the identity isomorphism of each
   hom-setoid, giving Id ⊣ Id, the unit for this composition. Alongside the
   two constructions we record the definitional characterization of the
   composite's transposes and the standard whiskering formulas for its unit
   and counit:

       η″ ≈ fmap[U] η′ ∘ η          (unit of the composite)
       ε″ ≈ ε′ ∘ fmap[F'] ε         (counit of the composite)

   Both nLab (adjoint functor, “basic properties”) and Wikipedia
   (“composition” under properties of adjoints) state this composition law.

   Relation to Instance/Adjoints.v: that pre-existing module already
   carries both witnesses — [adj_id], an exported instance, and
   [adj_comp] with its ⊚ notation — as the identity and the composition
   of its category [Adjoints] of categories and adjunctions.
   [Adjunction_Id] below therefore reuses [adj_id] rather than re-deriving
   it, and the corollaries [Adjunction_Compose_adj_comp_to]/[_from] record
   that [Adjunction_Compose A A'] and [adj_comp F' U' F U A' A] — which
   have the identical type (F' ◯ F) ⊣ (U ◯ U') — agree definitionally on
   both transposes.  Integration decision (for the maintainer): pick a
   single canonical home for adjunction composition — either refactor
   Instance/Adjoints.v's [adj_comp] to consume [Adjunction_Compose], or
   derive this file's composite from [adj_comp] — before later phases
   standardize on one of the two names; until then the agreement
   corollaries keep the two APIs interchangeable. *)

(** ** The identity adjunction  / ** 身份附加*)

(*
Id[C] ⊣ Id[C]: the transposing isomorphism is the identity isomorphism
   on each hom-setoid, both transposes are the identity function, and all
   four naturality squares hold by reflexivity.  The witness is [adj_id]
   from Instance/Adjoints.v — reused, not re-derived, so the corollaries
   below speak about the very witness that typeclass resolution produces
   for Id ⊣ Id goals (adj_id is an exported instance there). 

--------
Id[C] ⊣ Id[C]：转置同构是恒同同构
 在每个 hom-setoid 上，两个转置都是恒等函数，并且所有
 四个自然性方格通过自反性成立。 见证人是[adj_id]
 来自 Instance/Adjoints.v — 重用，而不是重新派生，因此推论
 下面谈谈类型类解析产生的见证
 对于 Id ⊣ Id 目标（adj_id 是那里的导出实例）。 
*)

Definition Adjunction_Id {C : Category} : Id[C] ⊣ Id[C] := adj_id.

Corollary Adjunction_Id_unit {C : Category} {x : C} :
  @unit _ _ _ _ (@Adjunction_Id C) x ≈ id[x].
Proof. reflexivity. Qed.

Corollary Adjunction_Id_counit {C : Category} {x : C} :
  @counit _ _ _ _ (@Adjunction_Id C) x ≈ id[x].
Proof. reflexivity. Qed.

(*
The same two equations, stated syntactically about [adj_id] itself, for
   proof scripts whose goals mention the resolved instance rather than the
   [Adjunction_Id] alias (the two are definitionally equal). 

--------
相同的两个方程，从语法上讲关于 [adj_id] 本身，对于
 其目标提及已解析实例而不是实例的证明脚本
 [Adjunction_Id] 别名（两者定义相同）。 
*)

Corollary adj_id_unit {C : Category} {x : C} :
  @unit _ _ _ _ (@adj_id C) x ≈ id[x].
Proof. reflexivity. Qed.

Corollary adj_id_counit {C : Category} {x : C} :
  @counit _ _ _ _ (@adj_id C) x ≈ id[x].
Proof. reflexivity. Qed.

(** ** Composition of adjunctions  / ** 附加语的构成*)

Section AdjunctionCompose.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context {F' : C ⟶ E}.
Context {U' : E ⟶ C}.
Context (A : F ⊣ U).
Context (A' : F' ⊣ U').

(*
The composite transposing isomorphism: paste the two hom-setoid
   isomorphisms in Sets. Its [to] transposes through A' and then A; its
   [from] transposes back through A and then A'. 

--------
复合转置同构：粘贴两个hom-setoid
 集合中的同构。 它的 [to] 通过 A' 转置，然后是 A； 它的
 [from] 通过 A 然后 A' 转回。 
*)

Definition adj_compose_iso (x : D) (y : E) :
  @Isomorphism Sets
    {| carrier := @hom E (F' (F x)) y  ; is_setoid := @homset E (F' (F x)) y  |}
    {| carrier := @hom D x (U (U' y)) ; is_setoid := @homset D x (U (U' y)) |} :=
  iso_compose (@adj _ _ _ _ A x (U' y)) (@adj _ _ _ _ A' (F x) y).

(*
Naturality of the composite's forward transpose in the source argument:
   inner step by A''s [to_adj_nat_l], outer step by A's. 

--------
源参数中复合材料前向转置的自然性：
 内部步骤由 A 的 [to_adj_nat_l] 执行，外部步骤由 A 的执行。 
*)
Lemma adj_compose_to_nat_l (x y : D) (z : E)
      (f : F' (F y) ~> z) (g : x ~> y) :
  to (adj_compose_iso x z) (f ∘ fmap[F'] (fmap[F] g))
    ≈ to (adj_compose_iso y z) f ∘ g.
Proof.
  simpl.
  transitivity (to (@adj _ _ _ _ A x (U' z))
                  (to (@adj _ _ _ _ A' (F y) z) f ∘ fmap[F] g)).
  - apply to_adj_respects.
    apply to_adj_nat_l.
  - apply to_adj_nat_l.
Qed.

(*
Naturality of the composite's forward transpose in the target argument:
   inner step by A''s [to_adj_nat_r], outer step by A's. 

--------
目标参数中复合材料前向转置的自然性：
 内部步骤由 A 的 [to_adj_nat_r] 执行，外部步骤由 A 的执行。 
*)
Lemma adj_compose_to_nat_r (x : D) (y z : E)
      (f : y ~> z) (g : F' (F x) ~> y) :
  to (adj_compose_iso x z) (f ∘ g)
    ≈ fmap[U] (fmap[U'] f) ∘ to (adj_compose_iso x y) g.
Proof.
  simpl.
  transitivity (to (@adj _ _ _ _ A x (U' z))
                  (fmap[U'] f ∘ to (@adj _ _ _ _ A' (F x) y) g)).
  - apply to_adj_respects.
    apply to_adj_nat_r.
  - apply to_adj_nat_r.
Qed.

(*
The two inverse-transpose fields, dually: inner step by A's law under
   A''s inverse transpose, outer step by A''s law. 

--------
两个反转置场，对偶：根据 A 定律的内步
 A' 的逆转置，按 A 定律进行外步。 
*)
Lemma adj_compose_from_nat_l (x y : D) (z : E)
      (f : y ~> U (U' z)) (g : x ~> y) :
  from (adj_compose_iso x z) (f ∘ g)
    ≈ from (adj_compose_iso y z) f ∘ fmap[F'] (fmap[F] g).
Proof.
  simpl.
  transitivity (from (@adj _ _ _ _ A' (F x) z)
                  (from (@adj _ _ _ _ A y (U' z)) f ∘ fmap[F] g)).
  - apply from_adj_respects.
    apply from_adj_nat_l.
  - apply from_adj_nat_l.
Qed.

Lemma adj_compose_from_nat_r (x : D) (y z : E)
      (f : y ~> z) (g : x ~> U (U' y)) :
  from (adj_compose_iso x z) (fmap[U] (fmap[U'] f) ∘ g)
    ≈ f ∘ from (adj_compose_iso x y) g.
Proof.
  simpl.
  transitivity (from (@adj _ _ _ _ A' (F x) z)
                  (fmap[U'] f ∘ from (@adj _ _ _ _ A x (U' y)) g)).
  - apply from_adj_respects.
    apply from_adj_nat_r.
  - apply from_adj_nat_r.
Qed.

(*
Assemble the composite adjunction. All four naturality fields are
   populated explicitly (the standalone-lemma-then-record pattern), so the
   dual-side laws are available without re-derivation. 

--------
组装复合附件。 所有四个自然场都是
 显式填充（独立引理然后记录模式），因此
 无需重新推导即可获得双边定律。 
*)

Definition Adjunction_Compose : (F' ◯ F) ⊣ (U ◯ U') :=
  @Build_Adjunction E D (F' ◯ F) (U ◯ U')
    adj_compose_iso
    adj_compose_to_nat_l
    adj_compose_to_nat_r
    adj_compose_from_nat_l
    adj_compose_from_nat_r.

(*
The transposes of the composite are the pasted transposes, definitionally:
   the forward transpose goes through A' and then A, the inverse transpose
   back through A and then A'. 

--------
复合的转置是粘贴的转置，定义为：
 正向转置经过 A'，然后经过 A，即逆转置
 返回A，然后A'。 
*)

Corollary Adjunction_Compose_to {x : D} {y : E} (f : F' (F x) ~> y) :
  to (@adj _ _ _ _ Adjunction_Compose x y) f
    ≈ to (@adj _ _ _ _ A x (U' y)) (to (@adj _ _ _ _ A' (F x) y) f).
Proof. reflexivity. Qed.

Corollary Adjunction_Compose_from {x : D} {y : E} (g : x ~> U (U' y)) :
  from (@adj _ _ _ _ Adjunction_Compose x y) g
    ≈ from (@adj _ _ _ _ A' (F x) y) (from (@adj _ _ _ _ A x (U' y)) g).
Proof. reflexivity. Qed.

(*
Agreement with [adj_comp] from Instance/Adjoints.v: composing the same
   two adjunctions there (with the arguments in its convention's order)
   yields the identical composite type (F' ◯ F) ⊣ (U ◯ U'), and the two
   constructions have definitionally equal transposes, in both
   directions. 

--------
与 Instance/Adjoints.v 中的 [adj_comp] 达成一致：组成相同的内容
 那里有两个附加词（参数按约定的顺序排列）
 产生相同的复合类型 (F' ◯ F) ⊣ (U ◯ U')，并且两个
 结构在定义上具有相等的转置
 方向。 
*)

Corollary Adjunction_Compose_adj_comp_to {x : D} {y : E}
  (f : F' (F x) ~> y) :
  to (@adj _ _ _ _ Adjunction_Compose x y) f
    ≈ to (@adj _ _ _ _ (adj_comp F' U' F U A' A) x y) f.
Proof. reflexivity. Qed.

Corollary Adjunction_Compose_adj_comp_from {x : D} {y : E}
  (g : x ~> U (U' y)) :
  from (@adj _ _ _ _ Adjunction_Compose x y) g
    ≈ from (@adj _ _ _ _ (adj_comp F' U' F U A' A) x y) g.
Proof. reflexivity. Qed.

(*
The unit of the composite is A''s unit whiskered by U, after A's unit;
   dually the counit is A''s counit after A's counit whiskered by F'. 

--------
复合材料的单元是A'的单元，在A的单元之后加上U；
 对偶，该单位是 A' 的单位，在 A 的单位被 F' 胡须标记之后。 
*)

Corollary Adjunction_Compose_unit {x : D} :
  @unit _ _ _ _ Adjunction_Compose x
    ≈ fmap[U] (@unit _ _ _ _ A' (F x)) ∘ @unit _ _ _ _ A x.
Proof.
  unfold unit; simpl.
  apply to_adj_unit.
Qed.

Corollary Adjunction_Compose_counit {y : E} :
  @counit _ _ _ _ Adjunction_Compose y
    ≈ @counit _ _ _ _ A' y ∘ fmap[F'] (@counit _ _ _ _ A (U' y)).
Proof.
  unfold counit; simpl.
  apply from_adj_counit.
Qed.

End AdjunctionCompose.
