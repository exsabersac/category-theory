Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)
   nLab:      https://ncatlab.org/nlab/show/cone+(in+category+theory)

   到图 F : J ⟶ C 的锥 = 顶点（apex）c + 腿族 vertex_map x : c ~> F x，
   使对 J 的每个箭头 f，有 fmap[F] f ∘ vertex_map x ≈ vertex_map y（连贯性）。
   A cone over F is an apex with legs commuting with F's actions.
*)

(*
   关于锥 / On cones

   Haskell 直觉：一组「从同一来源发出的、彼此相容的投影」。
   极限 = 「最好的」这种锥（终锥）；余锥/余极限对偶。
   Haskell intuition: a compatible family of projections from one source.
*)

(*
   【Class ACone / Cone 语法与字段展开】/ Syntax & field walkthrough

   1) ACone c F：固定顶点 c 的锥（腿 + 连贯性）。
      Cone F：打包 vertex_obj + ACone（完整锥）。
      ACone = cone at fixed apex; Cone packages apex + ACone.

   2) 字段 / Fields
      - vertex_map x : c ~> F x     —— 腿 / leg at x
      - cone_coherence              —— 腿与 F(f) 交换 / legs commute with F(f)
      - vertex_obj（仅 Cone）        —— 顶点对象 / apex

   3) Cocone F := Cone (F^op) —— 余锥。
      Cocone = cone on the opposite diagram.

   阅读：本文件 → Limit.v（终锥）→ Equalizer/Pullback 特例。
   Read here → Limit → special cases.
*)

Class ACone@{u0 u1 u2 u3 u4 u5} {J : Category@{u0 u1 u2}}
  {C : Category@{u3 u4 u5}} (c : obj[C]) (F : J ⟶ C) := {
    (* 腿：c ~> F x / leg at x *)
    vertex_map (x : J) : c ~{C}~> F x;
    (* 连贯性：腿与 F(f) 交换 / coherence *)
    cone_coherence {x y : J} (f : x ~{J}~> y) :
    fmap[F] f ∘ vertex_map x ≈ vertex_map y
  }.

(* 同顶点两锥：腿点态 ≈ 即等价 / cones equal iff legs agree pointwise *)
#[export]
  Program Instance AConeEquiv@{u0 u1 u2 u3 u4 u5 +}
  {J: Category@{u0 u1 u2}} {C: Category@{u3 u4 u5}}
  c (F : C ⟶ J) : Setoid (ACone c F) :=
  {| equiv := fun cone1 cone2 =>
                forall j, @vertex_map _ _ _ _ cone1 j ≈ @vertex_map _ _ _ _ cone2 j |}.
Next Obligation.
  equivalence.
  specialize X with j. specialize X0 with j.
  exact (Equivalence_Transitive _ _ _ X X0).
Qed.

(* Cone = 顶点 + ACone / Cone = apex + ACone *)
Class Cone@{u0 u1 u2 u3 u4 u5}
  {J : Category@{u0 u1 u2}}
  {C : Category@{u3 u4 u5}}
  (F : J ⟶ C) := {
  vertex_obj : C;                  (* the apex (vertex) object *)
  coneFrom : ACone vertex_obj F    (* 从顶点发出的锥 / cone from apex *)
}.

Coercion vertex_obj : Cone >-> obj.
#[export] Existing Instance coneFrom.

Notation "vertex_obj[ C ]" := (@vertex_obj _ _ _ C)
  (at level 9, format "vertex_obj[ C ]") : category_scope.
Notation "vertex_map[ L ]" := (@vertex_map _ _ _ _ (@coneFrom _ _ _ L) _)
  (at level 9, format "vertex_map[ L ]") : category_scope.

Notation "Cone[ N ] F" := (ACone N F)(* . { ψ : Cone F | vertex_obj[ψ] = N } *)
  (at level 9, format "Cone[ N ] F") : category_scope.

(* 余锥 = 对偶图上的锥 / Cocone = Cone on F^op *)
Definition Cocone `(F : J ⟶ C) := Cone (F^op).

(* 锥预层：c ↦ Cone[c] F / Cone presheaf *)
#[export]
Instance ConePresheaf@{u0 u1 u2 u3 u4 u5 +}
   {J : Category@{u0 u1 u2}} {C : Category@{u3 u4 u5}} (F : @Functor J C) :
   @Functor C^op Sets.
Proof.
  unshelve eapply Build_Functor.
  - change obj[C^op] with obj[C].
    exact (fun c => {| carrier := Cone[c]F ; is_setoid := AConeEquiv _ _ |}).
  - change obj[C^op] with obj[C] in *; intros c c'.
    intro f; simpl in f.
    unshelve eapply Build_SetoidMorphism.
    + simpl; intro λ1. unshelve eapply Build_ACone.
      * exact (fun x => compose (@vertex_map _ _ _ _ λ1 x) f).
      * abstract(simpl; intros x y g; now rewrite comp_assoc, (cone_coherence g)).
    + abstract(simpl; intros a b t j; specialize t with j; cbn;
      rewrite t; reflexivity).
  - abstract(proper).
  - abstract(intro x; cbn; intros y j; now apply id_right).
  - abstract(cbn; intros; now apply comp_assoc).
Defined.
