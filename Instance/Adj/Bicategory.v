Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Bicategory.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Square.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Cat.Bicategory.

Generalizable All Variables.

(* * * Adj two-dimensional: horizontal 复合 conjugate pairs （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/bicategory

   本文件给出双范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section HorizontalCompose.

Context {C D E : Category}.
Context {F  : D ⟶ C} {U  : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context {G  : C ⟶ E} {V  : E ⟶ C}.
Context {G' : C ⟶ E} {V' : E ⟶ C}.
Context (A  : F ⊣ U)  (A' : F' ⊣ U').
Context (B  : G ⊣ V)  (B' : G' ⊣ V').

(* Mac Lane's diagram read left right. Nothing here appeals the
 自然性 tau: [nat_hcompose]'s own factorisation Godement
 square exactly one goal produces. （已译） *)
Theorem conjugate_hcompose (s : F' ⟹ F) (t : U ⟹ U')
                           (sb : G' ⟹ G) (tb : V ⟹ V') :
  Conjugate A A' s t → Conjugate B B' sb tb →
  Conjugate (Adjunction_Compose A B) (Adjunction_Compose A' B')
            (nat_hcompose sb s) (nat_hcompose t tb).
Proof.
  intros H1 H2 x e k; simpl.
  rewrite comp_assoc.
  rewrite to_adj_nat_l.
  rewrite H1.
  rewrite H2.
  rewrite to_adj_nat_r.
  now rewrite comp_assoc.
Qed.

End HorizontalCompose.

(* * ** (B) The same 定理 through Adjunction/Square.v's vertical paste （已译） *)

(*
   本节说明伴随、函子、双范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition conj_padL {X Y : Category} {P P' : X ⟶ Y} (s : P' ⟹ P)
  : P' ◯ Id[X] ⟹ Id[Y] ◯ P := {| transform := fun x => s x |}.
Next Obligation. apply (naturality s). Qed.
Next Obligation. apply (naturality_sym s). Qed.

Program Definition conj_padR {X Y : Category} {P P' : X ⟶ Y} (t : P ⟹ P')
  : Id[Y] ◯ P ⟹ P' ◯ Id[X] := {| transform := fun a => t a |}.
Next Obligation. apply (naturality t). Qed.
Next Obligation. apply (naturality_sym t). Qed.

Section RouteB.

Context {C D E : Category}.
Context {F  : D ⟶ C} {U  : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context {G  : C ⟶ E} {V  : E ⟶ C}.
Context {G' : C ⟶ E} {V' : E ⟶ C}.
Context (A  : F ⊣ U)  (A' : F' ⊣ U').
Context (B  : G ⊣ V)  (B' : G' ⊣ V').

(* The hypothesis transfer is a Leibniz equality of TYPES. *)
Example routeb_hyp (s : F' ⟹ F) (t : U ⟹ U') :
  AdjointSquareT A A' Id[C] Id[D] (conj_padL s) (conj_padR t)
    = Conjugate A A' s t := eq_refl.

(* 相关说明。 （已译） *)
Example routeb_sigma (s : F' ⟹ F) (sb : G' ⟹ G) (x : D) :
  transform (paste_v_sigma (D:=D) (C:=C) (E:=E) (D':=D) (C':=C) (E':=E)
               (F:=F) (G:=G) (F':=F') (G':=G')
               Id[D] Id[C] Id[E] (conj_padL s) (conj_padL sb)) x
    = transform (nat_hcompose sb s) x := eq_refl.

(* The tau leg not: [paste_v_tau] takes other factorisation the
 Godement square, two differ one 自然性 t. （已译） *)
Lemma routeb_tau (t : U ⟹ U') (tb : V ⟹ V') (e : E) :
  transform (paste_v_tau (D:=D) (C:=C) (E:=E) (D':=D) (C':=C) (E':=E)
               (U:=U) (V:=V) (U':=U') (V':=V')
               Id[D] Id[C] Id[E] (conj_padR t) (conj_padR tb)) e
    ≈ transform (nat_hcompose t tb) e.
Proof. simpl; apply naturality. Qed.

Theorem conjugate_hcompose_via_square
        (s : F' ⟹ F) (t : U ⟹ U') (sb : G' ⟹ G) (tb : V ⟹ V') :
  Conjugate A A' s t → Conjugate B B' sb tb →
  Conjugate (Adjunction_Compose A B) (Adjunction_Compose A' B')
            (nat_hcompose sb s) (nat_hcompose t tb).
Proof.
  intros H1 H2.
  pose proof (adjoint_square_paste_v A B A' B' Id[D] Id[C] Id[E]
                (conj_padL s) (conj_padR t) (conj_padL sb) (conj_padR tb)
                H1 H2) as Hp.
  intros x e k.
  etransitivity; [ exact (Hp x e k) | ].
  apply compose_respects; [ | reflexivity ].
  apply routeb_tau.
Qed.

End RouteB.

(* * ** (C) Horizontal 复合 bifunctor （已译） *)

(* 相关说明。 （已译） *)
Definition nat_hcompose_interchange {C D E : Category}
  {P1 P2 P3 : C ⟶ D} {Q1 Q2 Q3 : D ⟶ E}
  (a1 : Q1 ⟹ Q2) (a2 : Q2 ⟹ Q3) (b1 : P1 ⟹ P2) (b2 : P2 ⟹ P3) :
  nat_hcompose (a2 ∙ a1) (b2 ∙ b1)
    ≈ nat_hcompose a2 b2 ∙ nat_hcompose a1 b1
  := @fmap_comp _ _ (@Cat_Hcompose C D E)
       (Q1, P1) (Q2, P2) (Q3, P3) (a2, b2) (a1, b1).

(* The 恒等 1-cell 范畴: 恒等 伴随. （已译） *)
Definition AdjIdObj (X : Category) : AdjObj X X :=
  (Id[X]; (Id[X]; @Adjunction_Id X)).

(* Composition of 1-cells.  Left adjoints compose in the opposite order to
   right adjoints, which is Mac Lane's <F- F, G G->. *)
Definition adjobj_hcompose {x y z : Category}
  (p : AdjObj y z) (q : AdjObj x y) : AdjObj x z :=
  (adjobj_left q ◯ adjobj_left p;
   (adjobj_right p ◯ adjobj_right q;
    Adjunction_Compose (adjobj_adj p) (adjobj_adj q))).

(* 相关说明。 （已译） *)
Program Definition conj_pair_hcompose {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : @ConjPair y z p p') (et : @ConjPair x y q q') :
  @ConjPair x z (adjobj_hcompose p q) (adjobj_hcompose p' q') := {|
  conj_left  := nat_hcompose (conj_left et) (conj_left th);
  conj_right := nat_hcompose (conj_right th) (conj_right et)
|}.
Next Obligation.
  exact (conjugate_hcompose (adjobj_adj p') (adjobj_adj p)
           (adjobj_adj q') (adjobj_adj q)
           (conj_left th) (conj_right th) (conj_left et) (conj_right et)
           (conj_pair_law th) (conj_pair_law et)).
Qed.

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)
Program Definition Adj_Hcompose {x y z : Category} :
  (Adj y z ∏ Adj x y) ⟶ Adj x z := {|
  fobj := fun pq => adjobj_hcompose (fst pq) (snd pq);
  fmap := fun pq pq' m => conj_pair_hcompose (fst m) (snd m)
|}.
Next Obligation.
  intros x y z [p q] [p' q'] [th et] [th' et'] [[H1 H2] [H3 H4]];
  split; simpl; intro o.
  - now rewrite (H3 _), (H1 o).
  - now rewrite (H2 _), (H4 o).
Qed.
Next Obligation. intros x y z [p q]; split; simpl; intros; cat. Qed.
(* Each leg is Cat's own interchange, applied. *)
Next Obligation.
  intros x y z [p q] [p' q'] [p'' q''] [th et] [th' et']; split.
  - exact (nat_hcompose_interchange (conj_left et') (conj_left et)
             (conj_left th') (conj_left th)).
  - exact (nat_hcompose_interchange (conj_right th) (conj_right th')
             (conj_right et) (conj_right et')).
Qed.

#[local] Obligation Tactic := program_simpl.

(* 相关说明。 （已译） *)
Example Adj_Hcompose_shape :
  ∀ x y z : Category, (Adj y z ∏ Adj x y) ⟶ Adj x z := @Adj_Hcompose.

(* The two reviewer checks, at Leibniz equality. *)
Example hcomp_obj_adj {x y z : Category}
  (p : AdjObj y z) (q : AdjObj x y) :
  adjobj_adj (adjobj_hcompose p q)
    = Adjunction_Compose (adjobj_adj p) (adjobj_adj q) := eq_refl.

Example hcomp_obj_left {x y z : Category}
  (p : AdjObj y z) (q : AdjObj x y) :
  adjobj_left (adjobj_hcompose p q)
    = adjobj_left q ◯ adjobj_left p := eq_refl.

Example hcomp_obj_right {x y z : Category}
  (p : AdjObj y z) (q : AdjObj x y) :
  adjobj_right (adjobj_hcompose p q)
    = adjobj_right p ◯ adjobj_right q := eq_refl.

Example hcomp_left_is_nat_hcompose {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : @ConjPair y z p p') (et : @ConjPair x y q q') :
  conj_left (conj_pair_hcompose th et)
    = nat_hcompose (conj_left et) (conj_left th) := eq_refl.

Example hcomp_right_is_nat_hcompose {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : @ConjPair y z p p') (et : @ConjPair x y q q') :
  conj_right (conj_pair_hcompose th et)
    = nat_hcompose (conj_right th) (conj_right et) := eq_refl.

(* 相关说明。 （已译） *)

(* One [exact] of the bifunctor's own [fmap_comp]. *)
Theorem conj_interchange {x y z : Category}
  {a b c : Adj y z ∏ Adj x y} (f : b ~> c) (g : a ~> b) :
  fmap[@Adj_Hcompose x y z] (f ∘ g)
    ≈ fmap[Adj_Hcompose] f ∘ fmap[Adj_Hcompose] g.
Proof. exact (@fmap_comp _ _ (@Adj_Hcompose x y z) a b c f g). Qed.

Corollary conj_interchange_left {x y z : Category}
  {a b c : Adj y z ∏ Adj x y} (f : b ~> c) (g : a ~> b) :
  conj_left (fmap[@Adj_Hcompose x y z] (f ∘ g))
    ≈ conj_left (fmap[Adj_Hcompose] f ∘ fmap[Adj_Hcompose] g).
Proof. exact (fst (conj_interchange f g)). Qed.

Corollary conj_interchange_right {x y z : Category}
  {a b c : Adj y z ∏ Adj x y} (f : b ~> c) (g : a ~> b) :
  conj_right (fmap[@Adj_Hcompose x y z] (f ∘ g))
    ≈ conj_right (fmap[Adj_Hcompose] f ∘ fmap[Adj_Hcompose] g).
Proof. exact (snd (conj_interchange f g)). Qed.

(* 相关说明。 （已译） *)
Corollary conj_interchange_sigma {x y z : Category}
  {p p' p'' : AdjObj y z} {q q' q'' : AdjObj x y}
  (th : p' ~{Adj y z}~> p'') (th' : p ~{Adj y z}~> p')
  (et : q' ~{Adj x y}~> q'') (et' : q ~{Adj x y}~> q') :
  nat_hcompose (conj_left et ∙ conj_left et')
               (conj_left th ∙ conj_left th')
    ≈ nat_hcompose (conj_left et) (conj_left th)
        ∙ nat_hcompose (conj_left et') (conj_left th').
Proof.
  exact (fst (@conj_interchange x y z (p, q) (p', q') (p'', q'')
                (th, et) (th', et'))).
Qed.

Corollary conj_interchange_tau {x y z : Category}
  {p p' p'' : AdjObj y z} {q q' q'' : AdjObj x y}
  (th : p' ~{Adj y z}~> p'') (th' : p ~{Adj y z}~> p')
  (et : q' ~{Adj x y}~> q'') (et' : q ~{Adj x y}~> q') :
  nat_hcompose (conj_right th' ∙ conj_right th)
               (conj_right et' ∙ conj_right et)
    ≈ nat_hcompose (conj_right th') (conj_right et')
        ∙ nat_hcompose (conj_right th) (conj_right et).
Proof.
  exact (snd (@conj_interchange x y z (p, q) (p', q') (p'', q'')
                (th, et) (th', et'))).
Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Program Definition Adj_hunit_left {x y : Category} (f : AdjObj x y) :
  @Isomorphism (Adj x y) (adjobj_hcompose (AdjIdObj y) f) f := {|
  to   := {| conj_left  := to   (nat_λ (adjobj_left  f))
           ; conj_right := from (nat_ρ (adjobj_right f)) |};
  from := {| conj_left  := from (nat_λ (adjobj_left  f))
           ; conj_right := to   (nat_ρ (adjobj_right f)) |}
|}.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.

Program Definition Adj_hunit_right {x y : Category} (f : AdjObj x y) :
  @Isomorphism (Adj x y) (adjobj_hcompose f (AdjIdObj x)) f := {|
  to   := {| conj_left  := to   (nat_ρ (adjobj_left  f))
           ; conj_right := from (nat_λ (adjobj_right f)) |};
  from := {| conj_left  := from (nat_ρ (adjobj_left  f))
           ; conj_right := to   (nat_λ (adjobj_right f)) |}
|}.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.

(* Both legs [to] direction, they take nat_α's three 函子
 arguments opposite orders. （已译） *)
Program Definition Adj_hassoc {w x y z : Category}
  (h : AdjObj y z) (g : AdjObj x y) (f : AdjObj w x) :
  @Isomorphism (Adj w z)
    (adjobj_hcompose (adjobj_hcompose h g) f)
    (adjobj_hcompose h (adjobj_hcompose g f)) := {|
  to   := {| conj_left  := to (nat_α (adjobj_left  h) (adjobj_left  g)
                                     (adjobj_left  f))
           ; conj_right := to (nat_α (adjobj_right f) (adjobj_right g)
                                     (adjobj_right h)) |};
  from := {| conj_left  := from (nat_α (adjobj_left  h) (adjobj_left  g)
                                       (adjobj_left  f))
           ; conj_right := from (nat_α (adjobj_right f) (adjobj_right g)
                                       (adjobj_right h)) |}
|}.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. intros a b k; simpl; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.

(* 相关说明。 （已译） *)
Example hunit_left_obj_left {x y : Category} (f : AdjObj x y) :
  adjobj_left (adjobj_hcompose (AdjIdObj y) f)
    = adjobj_left f ◯ Id[y] := eq_refl.

Example hunit_left_obj_right {x y : Category} (f : AdjObj x y) :
  adjobj_right (adjobj_hcompose (AdjIdObj y) f)
    = Id[y] ◯ adjobj_right f := eq_refl.

Example hunit_right_obj_left {x y : Category} (f : AdjObj x y) :
  adjobj_left (adjobj_hcompose f (AdjIdObj x))
    = Id[x] ◯ adjobj_left f := eq_refl.

Example hunit_right_obj_right {x y : Category} (f : AdjObj x y) :
  adjobj_right (adjobj_hcompose f (AdjIdObj x))
    = adjobj_right f ◯ Id[x] := eq_refl.

(** ** (F) The five coherence laws *)

(* 相关说明。 （已译） *)
Definition adj_hcomp2 {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q')
  : adjobj_hcompose p q ~{Adj x z}~> adjobj_hcompose p' q'
  := @fmap _ _ (@Adj_Hcompose x y z) (p, q) (p', q') (th, et).

Example adj_hcomp2_is_conj_pair_hcompose {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q') :
  adj_hcomp2 th et = conj_pair_hcompose th et := eq_refl.

Theorem Adj_hunit_left_natural {x y : Category} {f f' : AdjObj x y}
  (et : f ~{Adj x y}~> f') :
  et ∘ to (Adj_hunit_left f)
    ≈ to (Adj_hunit_left f') ∘ adj_hcomp2 (@id (Adj y y) (AdjIdObj y)) et.
Proof. split; simpl; intros; cat. Qed.

Theorem Adj_hunit_right_natural {x y : Category} {f f' : AdjObj x y}
  (et : f ~{Adj x y}~> f') :
  et ∘ to (Adj_hunit_right f)
    ≈ to (Adj_hunit_right f') ∘ adj_hcomp2 et (@id (Adj x x) (AdjIdObj x)).
Proof. split; simpl; intros; cat. Qed.

Theorem Adj_hassoc_natural {w x y z : Category}
  {h h' : AdjObj y z} {g g' : AdjObj x y} {f f' : AdjObj w x}
  (th : h ~{Adj y z}~> h') (ga : g ~{Adj x y}~> g')
  (et : f ~{Adj w x}~> f') :
  adj_hcomp2 th (adj_hcomp2 ga et) ∘ to (Adj_hassoc h g f)
    ≈ to (Adj_hassoc h' g' f') ∘ adj_hcomp2 (adj_hcomp2 th ga) et.
Proof. split; simpl; intros; rewrite !fmap_id, fmap_comp; cat. Qed.

Theorem Adj_triangle {x y z : Category}
  (g : AdjObj y z) (f : AdjObj x y) :
  adj_hcomp2 (to (Adj_hunit_right g)) (@id (Adj x y) f)
    ≈ adj_hcomp2 (@id (Adj y z) g) (to (Adj_hunit_left f))
        ∘ to (Adj_hassoc g (AdjIdObj y) f).
Proof. split; simpl; intros; cat. Qed.

Theorem Adj_pentagon {v w x y z : Category}
  (k : AdjObj y z) (h : AdjObj x y) (g : AdjObj w x) (f : AdjObj v w) :
  adj_hcomp2 (@id (Adj y z) k) (to (Adj_hassoc h g f))
    ∘ to (Adj_hassoc k (adjobj_hcompose h g) f)
    ∘ adj_hcomp2 (to (Adj_hassoc k h g)) (@id (Adj v w) f)
  ≈ to (Adj_hassoc k h (adjobj_hcompose g f))
    ∘ to (Adj_hassoc (adjobj_hcompose k h) g f).
Proof. split; simpl; intros; cat. Qed.

(** ** (G) Adj as a bicategory *)

(* The raw constructor, never [Build_Bicategory']: feeding [Adj]'s own ten
   projections keeps record eta, so [bicat C D] is definitionally
   [Adj C D] and [hcompose] typechecks against [Adj_Hcompose].  A plain
   [Definition], not an [Instance], following [Cat_Bicategory].（标题）（已译） *)
Definition Adj_Bicategory : Bicategory :=
  Build_Bicategory
    Category
    (fun C D => @obj (Adj C D))
    (fun C D => @hom (Adj C D))
    (@AdjIdObj)
    (fun C D => @homset (Adj C D))
    (fun C D => @id (Adj C D))
    (fun C D => @compose (Adj C D))
    (fun C D => @compose_respects (Adj C D))
    (fun C D => @id_left (Adj C D))
    (fun C D => @id_right (Adj C D))
    (fun C D => @comp_assoc (Adj C D))
    (fun C D => @comp_assoc_sym (Adj C D))
    (@Adj_Hcompose)
    (fun C D f => Adj_hunit_left f)
    (fun C D f => Adj_hunit_right f)
    (@Adj_hassoc)
    (@Adj_hunit_left_natural)
    (@Adj_hunit_right_natural)
    (@Adj_hassoc_natural)
    (@Adj_triangle)
    (@Adj_pentagon).

Example Adj_bicat_is_Adj (C D : Category) :
  @bicat Adj_Bicategory C D = Adj C D := eq_refl.

Example Adj_hcompose_readback (x y z : Category) :
  @hcompose Adj_Bicategory x y z = @Adj_Hcompose x y z := eq_refl.

Example Adj_bi1id_readback (C : Category) :
  @bi1id Adj_Bicategory C = AdjIdObj C := eq_refl.

Example Adj_hcomp2_readback {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q') :
  @hcomp2 Adj_Bicategory x y z p p' q q' th et
    = conj_pair_hcompose th et := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Adj_hcomp2_left_is_Cat_hcomp2 {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q') :
  conj_left (@hcomp2 Adj_Bicategory x y z p p' q q' th et)
    = @hcomp2 Cat_Bicategory z y x
        (adjobj_left q) (adjobj_left q')
        (adjobj_left p) (adjobj_left p')
        (conj_left et) (conj_left th) := eq_refl.

Example Adj_hcomp2_right_is_Cat_hcomp2 {x y z : Category}
  {p p' : AdjObj y z} {q q' : AdjObj x y}
  (th : p ~{Adj y z}~> p') (et : q ~{Adj x y}~> q') :
  conj_right (@hcomp2 Adj_Bicategory x y z p p' q q' th et)
    = @hcomp2 Cat_Bicategory x y z
        (adjobj_right p') (adjobj_right p)
        (adjobj_right q') (adjobj_right q)
        (conj_right th) (conj_right et) := eq_refl.

(* 相关说明。 （已译） *)

Definition adjobj_of_morphism {C D : Category}
  (m : C ~{Adjoints}~> D) : AdjObj C D :=
  (free_functor m; (forgetful_functor m; adjunction m)).

Definition morphism_of_adjobj {C D : Category}
  (x : AdjObj C D) : C ~{Adjoints}~> D := {|
  free_functor      := adjobj_left  x;
  forgetful_functor := adjobj_right x;
  adjunction        := adjobj_adj   x
|}.

(* 相关说明。 （已译） *)
Example adjoints_round_record {C D : Category} (m : C ~{Adjoints}~> D) :
  morphism_of_adjobj (adjobj_of_morphism m) = m := eq_refl.
