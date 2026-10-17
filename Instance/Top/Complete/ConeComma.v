Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Complete.

Generalizable All Variables.

(** * Limits of spaces through categories of cones: §V.9 Exercise 3 *)

(*
 nLab: https://ncatlab.org/nlab/show/cone
 nLab: https://ncatlab.org/nlab/show/comma+category
 nLab: https://ncatlab.org/nlab/show/initial+topology

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(** ** G_* : the functor a functor induces on categories of cones *)

Section ConeImage.

Context {J C D : Category} (G : C ⟶ D) (T : J ⟶ C).

(* Mac Lane's G_* : (Δ ↓ T) → (Δ' ↓ GT), ⟨τ : c → T⟩ ↦ ⟨Gτ : Gc → GT⟩, on
   Instance/Cones.v's [Cones]; its object action is Structure/Limit/
   Preservation.v's [FCone]. *)
Definition ConeImage : Cones T ⟶ Cones (G ◯ T).
Proof.
  unshelve refine (@Build_Functor (Cones T) (Cones (G ◯ T))
    (fun N => FCone G N) (fun N M u => (fmap[G] (`1 u); _)) _ _ _).
  - intro j. simpl. unfold fcone_leg. simpl.
    rewrite <- fmap_comp. apply fmap_respects. exact (`2 u j).
  - intros N M u v H; simpl in *. now rewrite H.
  - intros N; simpl. apply fmap_id.
  - intros N M P u v; simpl. apply fmap_comp.
Defined.

Example ConeImage_obj (N : Cone T) : fobj[ConeImage] N = FCone G N := eq_refl.

End ConeImage.

(** ** Exercise 3(a), in the form that holds: G_* with a RIGHT adjoint *)

(* A right adjoint carries a terminal object to a terminal object. *)
Definition terminal_of_right_adjoint {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (t : @Terminal C) : @Terminal D.
Proof.
  unshelve refine {| terminal_obj := U (@terminal_obj _ t) |}.
  - intro x. exact (to (@adj _ _ _ _ A x _) (@one _ t (F x))).
  - intros x f g.
    transitivity (to (@adj _ _ _ _ A x _) (from (@adj _ _ _ _ A x _) f)).
    + symmetry. exact (iso_to_from (@adj _ _ _ _ A x _) f).
    + transitivity (to (@adj _ _ _ _ A x _) (from (@adj _ _ _ _ A x _) g)).
      * apply proper_morphism. apply one_unique.
      * exact (iso_to_from (@adj _ _ _ _ A x _) g).
Defined.

(* If G_* has a right adjoint and GT has a limit, T has a limit: the right
   adjoint carries the terminal cone over GT to a terminal cone over T. *)
Definition limit_from_cone_right_adjoint {J C D : Category}
  (G : C ⟶ D) (T : J ⟶ C) (W : Cones (G ◯ T) ⟶ Cones T)
  (A : ConeImage G T ⊣ W) (L : Limit (G ◯ T)) : Limit T :=
  @Limit_Cones _ _ T (terminal_of_right_adjoint A (Cones_Limit (G ◯ T) L)).

(** ** Exercise 3(b), at every shape: the weakest topology on a Sets-cone *)

Section InitialCone.

Universes j o so.
Constraint o < so.

Context {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so}).

Local Notation G := PForget@{o so}.

(* The right adjoint: a cone over the underlying diagram goes to the same
   cone with its apex given the initial topology for its legs,
   Instance/Top/Complete.v's [pinit_cone]. *)
Definition PInitCone : Cones (G ◯ T) ⟶ Cones T.
Proof.
  unshelve refine (@Build_Functor (Cones (G ◯ T)) (Cones T)
    (fun N => pinit_cone T N)
    (fun N M u => (@Build_PMor (pinit_top T N) (pinit_top T M) (`1 u) _; _))
    _ _ _).
  - apply (proj2 (pinit_universal _ _ _ _ (pinit_top T N) (`1 u))).
    intro k.
    apply (@pcont_respects (pinit_top T N) (fobj[T] k) (cone_leg N k)).
    + intro s. symmetry. exact (`2 u k s).
    + exact (pinit_leg_cont _ _ _ _ k).
  - intros k s; simpl. exact (`2 u k s).
  - intros N M u v H s; simpl in *. exact (H s).
  - intros N s; simpl. reflexivity.
  - intros N M P u v s; simpl. reflexivity.
Defined.

Example PInitCone_obj (N : Cone (G ◯ T)) : fobj[PInitCone] N = pinit_cone T N :=
  eq_refl.

Program Definition pcone_adj_iso (x : Cones T) (y : Cones (G ◯ T)) :
  @Isomorphism Sets
    {| carrier := @hom (Cones (G ◯ T)) (ConeImage G T x) y
     ; is_setoid := @homset (Cones (G ◯ T)) (ConeImage G T x) y |}
    {| carrier := @hom (Cones T) x (PInitCone y)
     ; is_setoid := @homset (Cones T) x (PInitCone y) |} := {|
  to   := {| morphism := fun k =>
               (@Build_PMor (vertex_obj[x]) (pinit_top T y) (`1 k) _; _) |};
  from := {| morphism := fun k => (pmap (`1 k); _) |}
|}.
Next Obligation.
  intros x y [k Hk]; simpl in *.
  apply (proj2 (pinit_universal _ _ _ _ (vertex_obj[x]) k)).
  intro j.
  apply (pcont_respects (pmap (cone_leg x j))).
  - intro s. symmetry. exact (Hk j s).
  - exact (pcont (cone_leg x j)).
Qed.
Next Obligation. intros x y [k Hk] j s; simpl in *. exact (Hk j s). Qed.
Next Obligation. intros x y k k' H s; simpl in *. exact (H s). Qed.
Next Obligation. intros x y [k Hk] j s; simpl in *. exact (Hk j s). Qed.
Next Obligation. intros x y k k' H s; simpl in *. exact (H s). Qed.
Next Obligation. intros x y k s; simpl. reflexivity. Qed.
Next Obligation. intros x y k s; simpl. reflexivity. Qed.

Definition pcone_adjunction : ConeImage G T ⊣ PInitCone.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ (ConeImage G T) PInitCone
                     pcone_adj_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(* Exercise 3(c)'s engine, at every shape: a limit of the underlying
   diagram, carried across the adjunction. *)
Definition PTop_limit_via_cones (L : Limit (G ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint G T PInitCone pcone_adjunction L.

End InitialCone.

Definition PTop_Complete_via_cones@{r s o so +| s <= o, o < so, o <= r +} :
  @Complete@{r s o so} PTopCat@{o so} :=
  fun J T => PTop_limit_via_cones T (Sets_Limit (PForget ◯ T)).

(* The two routes of Instance/Top/Complete.v's recipe and of the cone
   adjunction build the same space. *)
Example PTop_via_cones_apex@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete_via_cones J T)]
    = vertex_obj[@limit_cone _ _ _ (@PTop_Complete J T)] := eq_refl.

(* Not only the apex: the whole limiting cone, legs included. *)
Example PTop_via_cones_cone@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  @limit_cone _ _ _ (@PTop_Complete_via_cones@{o s o so _ _ _} J T)
    = @limit_cone _ _ _ (@PTop_Complete@{o s o so _ _} J T) := eq_refl.

(* Exercise 3(c): Top has all products, J discrete.  The limit of the
   discrete diagram on [X], through the cone adjunction. *)
Definition PTop_iprod_cone@{i o so +| i <= o, o < so +}
  (A : Type@{i}) (X : A → PTop@{o}) :
  Limit (@DiscreteCat_Functor' A PTopCat@{o so} X) :=
  PTop_limit_via_cones (@DiscreteCat_Functor' A PTopCat@{o so} X)
    (Sets_Limit (PForget ◯ @DiscreteCat_Functor' A PTopCat@{o so} X)).

Definition PTop_iprod_via_cones@{i o so +| i <= o, o < so +}
  (A : Type@{i}) (X : A → PTop@{o}) :
  @IsIndexedProduct PTopCat@{o so} A X
    (vertex_obj[@limit_cone _ _ _ (PTop_iprod_cone A X)])
    (cone_leg (@limit_cone _ _ _ (PTop_iprod_cone A X))) :=
  discrete_IsIndexedProduct_of_IsLimitCone
    (@DiscreteCat_Functor' A PTopCat@{o so} X) _
    (limit_limitcone (PTop_iprod_cone A X)).

Definition PTop_products_via_cone_comma@{i o so +| i <= o, o < so +} :
  @HasIndexedProducts@{i i i o so o} PTopCat@{o so} :=
  @Build_HasIndexedProducts PTopCat@{o so}
    (fun A X => vertex_obj[@limit_cone _ _ _ (PTop_iprod_cone A X)])
    (fun A X => cone_leg (@limit_cone _ _ _ (PTop_iprod_cone A X)))
    (@PTop_iprod_via_cones).

(** ** The LEFT adjoint of G_* at [PForget]: the discrete topology *)

Section DiscreteCone.

Universes j o so.
Constraint o < so.

Context {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so}).

Local Notation G := PForget@{o so}.

(* A cone over the underlying diagram, its apex given the discrete
   topology: every leg is continuous out of a discrete space. *)
Definition pdisc_cone (N : Cone (G ◯ T)) : Cone T.
Proof.
  unshelve refine (@Build_Cone J PTopCat@{o so} T (PDiscrete (vertex_obj[N]))
    (@Build_ACone J PTopCat@{o so} (PDiscrete (vertex_obj[N])) T
       (fun k => pdisc_mor (vertex_obj[N]) (fobj[T] k) (cone_leg N k)) _)).
  intros x y f s; simpl.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f s).
Defined.

Definition PDiscCone : Cones (G ◯ T) ⟶ Cones T.
Proof.
  unshelve refine (@Build_Functor (Cones (G ◯ T)) (Cones T)
    (fun N => pdisc_cone N)
    (fun N M u => (pdisc_mor (vertex_obj[N]) (PDiscrete (vertex_obj[M])) (`1 u); _))
    _ _ _).
  - intros k s; simpl. exact (`2 u k s).
  - intros N M u v H s; simpl in *. exact (H s).
  - intros N s; simpl. reflexivity.
  - intros N M P u v s; simpl. reflexivity.
Defined.

Example PDiscCone_open (N : Cone (G ◯ T)) (V : vertex_obj[N] → Prop) :
  POpen (vertex_obj[fobj[PDiscCone] N]) V = pdisc_open (vertex_obj[N]) V :=
  eq_refl.

Program Definition pdisc_cone_adj_iso (x : Cones (G ◯ T)) (y : Cones T) :
  @Isomorphism Sets
    {| carrier := @hom (Cones T) (PDiscCone x) y
     ; is_setoid := @homset (Cones T) (PDiscCone x) y |}
    {| carrier := @hom (Cones (G ◯ T)) x (ConeImage G T y)
     ; is_setoid := @homset (Cones (G ◯ T)) x (ConeImage G T y) |} := {|
  to   := {| morphism := fun k => (pmap (`1 k); _) |};
  from := {| morphism := fun k =>
               (pdisc_mor (vertex_obj[x]) (vertex_obj[y]) (`1 k); _) |}
|}.
Next Obligation. intros x y [k Hk] j s; simpl in *. exact (Hk j s). Qed.
Next Obligation. intros x y k k' H s; simpl in *. exact (H s). Qed.
Next Obligation. intros x y [k Hk] j s; simpl in *. exact (Hk j s). Qed.
Next Obligation. intros x y k k' H s; simpl in *. exact (H s). Qed.
Next Obligation. intros x y k s; simpl. reflexivity. Qed.
Next Obligation. intros x y k s; simpl. reflexivity. Qed.

Definition pdisc_cone_adjunction : PDiscCone ⊣ ConeImage G T.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ PDiscCone (ConeImage G T)
                     pdisc_cone_adj_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

End DiscreteCone.

(* At the empty shape the two adjoints of G_* part company: on the
   two-point set, the left adjoint makes [{true}] open and the right
   adjoint, the weakest topology for the empty family of maps, does not. *)
Section EmptyShape.

Universes o so.
Constraint o < so.

(* The empty shape at the category's own levels: Instance/Zero.v's [_0]
   is unannotated and sits at homs [Set]. *)
Definition pempty_diagram : DiscreteCat@{o o o} False ⟶ PTopCat@{o so} :=
  @DiscreteCat_Functor' False PTopCat@{o so} (fun x : False => match x with end).

Definition pbool_cone : Cone (PForget@{o so} ◯ pempty_diagram).
Proof.
  unshelve refine (@Build_Cone _ Sets@{o so} (PForget ◯ pempty_diagram)
    bool_setoid_object@{o o} (@Build_ACone _ Sets@{o so}
       bool_setoid_object@{o o} (PForget ◯ pempty_diagram) _ _)).
  - intro x; destruct x.
  - intro x; destruct x.
Defined.

Lemma puniform_topology (S : SetoidObject@{o o}) :
  PIsTopology S (fun W => ∀ x y : S, W x → W y).
Proof.
  split; [|split; [|split]].
  - intros U V H HU x y v. apply (proj1 (H y)), (HU x y), (proj2 (H x)), v.
  - intros F HF x y [U [FU u]]. exists U. split; [exact FU|].
    exact (HF U FU x y u).
  - intros x y w; exact w.
  - intros U V HU HV x y [u v]. exact (conj (HU x y u) (HV x y v)).
Qed.

Theorem cone_adjoints_differ_at_empty_shape :
  POpen (vertex_obj[fobj[PDiscCone pempty_diagram] pbool_cone])
        (fun b : bool => b = true) /\
  (POpen (vertex_obj[fobj[PInitCone pempty_diagram] pbool_cone])
         (fun b : bool => b = true) → False).
Proof.
  split.
  - intros x y e H. simpl in e. rewrite <- e. exact H.
  - intro H.
    assert (U : ∀ x y : bool, x = true → y = true).
    { apply (H _ (puniform_topology bool_setoid_object@{o o})).
      intros W [k _]. destruct k. }
    discriminate (U true false eq_refl).
Qed.

End EmptyShape.

(** ** The book's Exercise 3(a) as printed, refuted *)

(* "If G_* has a LEFT adjoint and GT has a limit in D, prove that T has a
   limit in C."  Counterexample: the empty shape, C the walking span
   (an initial apex, no terminal object), D the point. *)

Local Ltac ex3_lit_tac :=
  intros; simpl in *; repeat intro; simpl in *;
  repeat match goal with
         | [ H : False |- _ ] => destruct H
         | [ H : poly_unit |- _ ] => destruct H
         end;
  try exact I; try reflexivity;
  try (match goal with
       | [ |- @eq poly_unit ?a ?b ] => destruct a; destruct b; reflexivity
       end).

(* The empty shape, [DiscreteCat False], at the universes of its use: no
   level of it is fixed. *)
Definition ex3_T0 : DiscreteCat False ⟶ Roof :=
  @DiscreteCat_Functor' False Roof (fun x : False => match x with end).
Definition ex3_G1 : Roof ⟶ _1 := Erase Roof.

Definition ex3_roof_cone (c : Roof) : Cone ex3_T0.
Proof.
  unshelve econstructor; [exact c|].
  unshelve econstructor; intros x; destruct x.
Defined.

Definition ex3_point_cone : Cone (ex3_G1 ◯ ex3_T0).
Proof.
  unshelve econstructor; [exact ttt|].
  unshelve econstructor; intros x; destruct x.
Defined.

Definition ex3_roof_from_apex (c : RoofObj) : RoofHom RZero c :=
  match c with RNeg => ZeroNeg | RZero => IdZero | RPos => ZeroPos end.

Program Definition ex3_LeftAdj : Cones (ex3_G1 ◯ ex3_T0) ⟶ Cones ex3_T0 := {|
  fobj := fun _ => ex3_roof_cone RZero;
  fmap := fun _ _ _ => (IdZero; _)
|}.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.

Program Definition ex3_left_adj_iso (x : Cones (ex3_G1 ◯ ex3_T0))
  (y : Cones ex3_T0) :
  @Isomorphism Sets
    {| carrier := @hom (Cones ex3_T0) (ex3_LeftAdj x) y
     ; is_setoid := @homset (Cones ex3_T0) (ex3_LeftAdj x) y |}
    {| carrier := @hom (Cones (ex3_G1 ◯ ex3_T0)) x (ConeImage ex3_G1 ex3_T0 y)
     ; is_setoid := @homset (Cones (ex3_G1 ◯ ex3_T0)) x
                      (ConeImage ex3_G1 ex3_T0 y) |} := {|
  to   := {| morphism := fun _ => (ttt; _) |};
  from := {| morphism := fun _ => (ex3_roof_from_apex (vertex_obj[y]); _) |}
|}.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.

Definition ex3_left_adj : ex3_LeftAdj ⊣ ConeImage ex3_G1 ex3_T0.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ ex3_LeftAdj (ConeImage ex3_G1 ex3_T0)
                     ex3_left_adj_iso).
  - ex3_lit_tac.
  - ex3_lit_tac.
Defined.

Program Definition ex3_point_terminal : @Terminal (Cones (ex3_G1 ◯ ex3_T0)) := {|
  terminal_obj := ex3_point_cone;
  one := fun N => (ttt; _)
|}.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.

Definition ex3_point_limit : Limit (ex3_G1 ◯ ex3_T0) :=
  @Limit_Cones _ _ (ex3_G1 ◯ ex3_T0) ex3_point_terminal.

Theorem ex3_roof_no_limit (L : Limit ex3_T0) : False.
Proof.
  generalize (unique_obj (@ump_limits _ _ _ L (ex3_roof_cone RNeg)))
             (unique_obj (@ump_limits _ _ _ L (ex3_roof_cone RPos))).
  simpl. intros a b.
  revert a b. generalize (@vertex_obj _ _ _ (@limit_cone _ _ _ L)).
  intros v a b. destruct v; inversion a; inversion b.
Qed.

(* The book's claim (a) at one pair [G], [T], with "left", and the three
   facts that refute it there, each stated about the same [G] and [T]. *)
Definition Ex3a_left_literal {J C D : Category} (G : C ⟶ D) (T : J ⟶ C) :
  Type := ∀ F : Cones (G ◯ T) ⟶ Cones T,
            F ⊣ ConeImage G T → Limit (G ◯ T) → Limit T.

Definition Ex3a_left_refuting_data {J C D : Category} (G : C ⟶ D)
  (T : J ⟶ C) : Type :=
  { F : Cones (G ◯ T) ⟶ Cones T & F ⊣ ConeImage G T } *
  Limit (G ◯ T) * (Limit T → False).

Definition ex3a_left_counterexample :
  Ex3a_left_refuting_data ex3_G1 ex3_T0 :=
  ((ex3_LeftAdj; ex3_left_adj), ex3_point_limit, ex3_roof_no_limit).

Theorem ex3a_left_adjoint_literal_refuted :
  Ex3a_left_literal ex3_G1 ex3_T0 → False.
Proof.
  intro H.
  exact (ex3_roof_no_limit (H ex3_LeftAdj ex3_left_adj ex3_point_limit)).
Qed.
