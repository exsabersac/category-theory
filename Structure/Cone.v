Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/cone
 Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)

 A cone over a diagram F : J ⟶ C is an apex object c : C together with a
 family of legs ψx : c ~> F x, one for each object x of J, that is natural
 in x: for every f : x ~> y in J we have F(f) ∘ ψx ≈ ψy. The apex sits
 "above" the diagram with arrows pointing down into each F x, compatibly
 with all of the diagram's morphisms. The terminal cone over F (the cone
 through which every other cone factors uniquely) is the limit of F.

 [ACone] fixes the apex [c] and records just the leg family and its
 coherence; [Cone] below bundles the apex together with such an [ACone].
 A cocone over F is dually a cone over F^op (see [Cocone]). 

 --------
 nLab:  https://ncatlab.org/nlab/show/cone 
 维基百科:  https://en.wikipedia.org/wiki/Cone_(category_theory) 

 对于一个图 F : J ⟶ C 的圆锥是一个顶点对象 c : C 以及一族腿 ψx : c ~> F x，每个 J 的对象 x 对应一个，这在 x 上是自然的：对于 J 中的每个 f : x ~> y，我们有 F(f) ∘ ψx ≈ ψy。顶点位于图的“上方”，箭头向下指向每个 F x，并且与图的所有态射兼容。F 的终端圆锥（通过它每个其他圆锥都可以唯一分解的圆锥）是 F 的极限。

 [ACone] 固定顶点 [c] 并仅记录腿族及其一致性；下方的 [Cone] 将顶点与这样的 [ACone] 一起捆绑。F 的余圆锥对偶地是 F^op 的圆锥（见 [Cocone]）。
*)

Class ACone@{u0 u1 u2 u3 u4 u5} {J : Category@{u0 u1 u2}}
  {C : Category@{u3 u4 u5}} (c : obj[C]) (F : J ⟶ C) := {
    (* The leg (component) at x: a morphism from the apex c into F x. / 在 x 的腿（组件）：从顶点 c 到 F x 的一个态射。 *)
    vertex_map (x : J) : c ~{C}~> F x;
    (* Naturality of the legs: pushing the leg at x along F f lands on the leg at y, i.e. F(f) ∘ ψx ≈ ψy, so every diagram triangle commutes. / 腿的自然性：沿着 F f 在 x 推动腿会落在 y 的腿上，即 F(f) ∘ ψx ≈ ψy，因此每个图形三角形都是交换的。 *)
    cone_coherence {x y : J} (f : x ~{J}~> y) :
    fmap[F] f ∘ vertex_map x ≈ vertex_map y
  }.

(*
 Two cones with the same apex are identified when their legs agree
 pointwise (up to ≈); the coherence proof is irrelevant to this equivalence. 

 --------
 当两个具有相同顶点的锥体其边逐点一致（最多相差 ≈）时，它们被认为是相同的；一致性证明与这种等价无关。
*)
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

(*
 A [Cone] over F packages an apex with a leg family over that apex,
 matching the nLab/Wikipedia definition of a cone as an apex object
 together with its commuting legs. 

 --------
 一个 [Cone] 在 F 上为一个顶点打包一个顶点的腿族，匹配 nLab/Wikipedia 对锥的定义，即作为顶点对象及其交换腿。
*)
Class Cone@{u0 u1 u2 u3 u4 u5}
  {J : Category@{u0 u1 u2}}
  {C : Category@{u3 u4 u5}}
  (F : J ⟶ C) := {
  vertex_obj : C;                  (* the apex (vertex) object / 顶点对象 *)
  coneFrom : ACone vertex_obj F    (* the legs over that apex, with coherence / 腿越过那个顶点，保持连贯 *)
}.

Coercion vertex_obj : Cone >-> obj.
#[export] Existing Instance coneFrom.

Notation "vertex_obj[ C ]" := (@vertex_obj _ _ _ C)
  (at level 9, format "vertex_obj[ C ]") : category_scope.
Notation "vertex_map[ L ]" := (@vertex_map _ _ _ _ (@coneFrom _ _ _ L) _)
  (at level 9, format "vertex_map[ L ]") : category_scope.

Notation "Cone[ N ] F" := (ACone N F)(* . { ψ : Cone F | vertex_obj[ψ] = N } / . { ψ : 锥 F | 顶点对象 [ψ] = N } *)
  (at level 9, format "Cone[ N ] F") : category_scope.

(* A cocone over F is the dual notion: a cone over the opposite diagram F^op, whose legs run F x ~> apex (see nLab: cocone). / F 的余锥是对偶概念：在相反图 F^op 上的锥，其边从 F x 运行到顶点（参见 nLab: cocone）。 *)
Definition Cocone `(F : J ⟶ C) := Cone (F^op).

(*
 The presheaf of cones over F: each object c is sent to the setoid of
 cones with apex c, and a morphism f : c' ~> c in C (i.e. c ~> c' in C^op)
 precomposes every leg with f, reindexing a c-cone to a c'-cone. Its
 representing object, when one exists, is the limit of F. 

 --------
 F 上的圆锥预层：每个对象 c 被映射到顶点为 c 的圆锥的集合族，而一个态射 f : c' ~> c 在 C 中（即在 C^op 中 c ~> c'）会将每条腿与 f 预合成，将一个 c-圆锥重新索引为 c'-圆锥。当存在它的表示对象时，该对象就是 F 的极限。
*)
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
