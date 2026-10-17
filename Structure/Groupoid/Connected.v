Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.

Generalizable All Variables.

(** * Connected categories, and the structure of a connected groupoid *)

(*
   nLab:      https://ncatlab.org/nlab/show/groupoid
   Wikipedia: https://en.wikipedia.org/wiki/Groupoid
   Book:      Riehl, "Category Theory in Context", §1.5, printed p. 35 (the
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出连通性相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/fundamental+groupoid
   Paper: Brown, "From groups to groupoids: a brief survey", Bulletin of the

   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Zig-zags *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive ZigZag {C : Category} : C → C → Type :=
  | zz_nil (x : C) : ZigZag x x
  | zz_fwd (x y z : C) (f : x ~> y) (s : ZigZag y z) : ZigZag x z
  | zz_bwd (x y z : C) (f : y ~> x) (s : ZigZag y z) : ZigZag x z.

Arguments zz_nil {C} x.
Arguments zz_fwd {C x y z} f s.
Arguments zz_bwd {C x y z} f s.

(* Riehl §1.5: C is connected when every pair of objects is joined by a
   zig-zag. *)
Definition Connected (C : Category) : Type := ∀ x y : C, ZigZag x y.

(* A single arrow is a one-step zig-zag, so the one-arrow form implies the
   zig-zag form in ANY category. *)
Definition hom_zigzag {C : Category} {x y : C} (f : x ~> y) : ZigZag x y :=
  zz_fwd f (zz_nil y).

Definition arrow_connected {C : Category} (H : ∀ x y : C, x ~> y) :
  Connected C := fun x y => hom_zigzag (H x y).

(*
   本节说明（余）端、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint zigzag_trans {C : Category} {x y z : C}
  (s : ZigZag x y) : ZigZag y z → ZigZag x z :=
  match s in ZigZag a b return ZigZag b z → ZigZag a z with
  | zz_nil _     => fun t => t
  | zz_fwd f s'  => fun t => zz_fwd f (zigzag_trans s' t)
  | zz_bwd f s'  => fun t => zz_bwd f (zigzag_trans s' t)
  end.

(* Reversal, by turning every forward step into a backward one and vice
   versa.  Stated through [zigzag_trans] because a reversed chain is built
   from the tail outwards. *)
Fixpoint zigzag_sym {C : Category} {x y : C} (s : ZigZag x y) : ZigZag y x :=
  match s in ZigZag a b return ZigZag b a with
  | zz_nil w    => zz_nil w
  | zz_fwd f s' => zigzag_trans (zigzag_sym s') (zz_bwd f (zz_nil _))
  | zz_bwd f s' => zigzag_trans (zigzag_sym s') (zz_fwd f (zz_nil _))
  end.

(** ** The strictly alternating form *)

(* A fence: a chain of spans x --> m <-- y, each step alternating forwards
   then backwards by construction.  This is Riehl's "alternating directions"
   read literally. *)
Inductive Fence {C : Category} : C → C → Type :=
  | fence_nil (x : C) : Fence x x
  | fence_cons (x m y z : C) (f : x ~> m) (g : y ~> m) (t : Fence y z) :
      Fence x z.

Arguments fence_nil {C} x.
Arguments fence_cons {C x} m {y z} f g t.

(* A fence is a zig-zag: expand each span into a forward step followed by a
   backward one. *)
Fixpoint fence_zigzag {C : Category} {x y : C} (t : Fence x y) : ZigZag x y :=
  match t with
  | fence_nil w             => zz_nil w
  | fence_cons _ f g t'     => zz_fwd f (zz_bwd g (fence_zigzag t'))
  end.

(*
   本节说明 Connected 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint zigzag_fence {C : Category} {x y : C} (s : ZigZag x y) : Fence x y :=
  match s with
  | zz_nil w      => fence_nil w
  | zz_fwd f s'   => fence_cons _ f id (zigzag_fence s')
  | zz_bwd f s'   => fence_cons _ id f (zigzag_fence s')
  end.

(** ** Collapse to the one-arrow form in a groupoid *)

(*
   本节说明 Connected 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint zigzag_hom {C : Category} (G : IsGroupoid C) {x y : C}
  (s : ZigZag x y) : x ~> y :=
  match s in ZigZag a b return a ~> b with
  | zz_nil w    => id[w]
  | zz_fwd f s' => zigzag_hom G s' ∘ f
  | zz_bwd f s' => zigzag_hom G s' ∘ ginv G f
  end.

Definition connected_arrow {C : Category} (G : IsGroupoid C) (K : Connected C)
  (x y : C) : x ~> y := zigzag_hom G (K x y).

(* And therefore any two objects of a connected groupoid are isomorphic —
   the form the structure theorem consumes. *)
Definition connected_iso {C : Category} (G : IsGroupoid C) (K : Connected C)
  (x y : C) : x ≅ y := giso G (connected_arrow G K x y).

(** ** The structure theorem *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition vertex_incl {C : Category} (G : IsGroupoid C) (x : C) :
  Deloop (vertex_group G x) ⟶ C := {|
  fobj := fun _ => x;
  fmap := fun _ _ f => f
|}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition vertex_incl_Full {C : Category} (G : IsGroupoid C) (x : C) :
  Full (vertex_incl G x) :=
  @Build_Full _ _ (vertex_incl G x)
    (fun _ _ g => g) (fun _ _ g => reflexivity g).

Definition vertex_incl_Faithful {C : Category} (G : IsGroupoid C) (x : C) :
  Faithful (vertex_incl G x) :=
  @Build_Faithful _ _ (vertex_incl G x) (fun _ _ _ _ H => H).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition vertex_incl_ESO {C : Category} (G : IsGroupoid C) (K : Connected C)
  (x : C) : EssentiallySurjective (vertex_incl G x) :=
  @Build_EssentiallySurjective _ _ (vertex_incl G x)
    (fun _ => ttt) (fun d => connected_iso G K x d).

(*
   本节说明 Connected 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem connected_deloop_equiv {C : Category} (G : IsGroupoid C)
  (K : Connected C) (x : C) : EquivalenceOfCategories (vertex_incl G x).
Proof.
  exact (@FF_ESO_Equivalence _ _ (vertex_incl G x)
           (vertex_incl_Full G x) (vertex_incl_Faithful G x)
           (vertex_incl_ESO G K x)).
Defined.

(* The quasi-inverse, extracted: it sends every object of C to the single
   object of the delooping, and an arrow to its conjugate into hom(x, x). *)
Definition connected_deloop_inverse {C : Category} (G : IsGroupoid C)
  (K : Connected C) (x : C) : C ⟶ Deloop (vertex_group G x) :=
  @quasi_inverse _ _ _ (connected_deloop_equiv G K x).

(** ** Connectedness is necessary, not merely sufficient *)

(* [vertex_incl G x] sends EVERY object to x, so an essential-surjectivity
   witness for it is exactly a family of isomorphisms x ≅ d — the chosen
   preimage object carries no information, there being only one to choose. *)
Definition vertex_incl_ESO_iso {C : Category} (G : IsGroupoid C) (x : C)
  (E : EssentiallySurjective (vertex_incl G x)) (d : C) : x ≅ d :=
  @eso_iso _ _ (vertex_incl G x) E d.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem deloop_equiv_connected {C : Category} (G : IsGroupoid C) (x : C)
  (E : EquivalenceOfCategories (vertex_incl G x)) : Connected C.
Proof.
  pose proof (Equivalence_EssSurj E) as Eso.
  intros y z.
  apply hom_zigzag.
  exact (to (vertex_incl_ESO_iso G x Eso z)
           ∘ from (vertex_incl_ESO_iso G x Eso y)).
Defined.

(* The two directions together.  For a groupoid with a chosen object, being
   connected and being equivalent to the delooping of the vertex group at
   that object are interderivable. *)
Theorem connected_iff_deloop_equiv {C : Category} (G : IsGroupoid C) (x : C) :
  Connected C ↔ EquivalenceOfCategories (vertex_incl G x).
Proof.
  split.
  - intro K.
    exact (connected_deloop_equiv G K x).
  - intro E.
    exact (deloop_equiv_connected G x E).
Defined.

(** ** A concrete connected groupoid *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition WideDeloop (M : MonObject) (A : Type) : Category := {|
  obj     := A;
  hom     := fun _ _ => carrier M;
  homset  := fun _ _ => is_setoid M;
  id      := fun _ => mon_unit;
  compose := fun _ _ _ f g => mon_op f g;

  compose_respects := fun _ _ _ => mon_op_respects M;

  id_left  := fun _ _ => mon_op_unit_l;
  id_right := fun _ _ => mon_op_unit_r;

  comp_assoc     := fun _ _ _ _ => mon_op_assoc;
  comp_assoc_sym := fun _ _ _ _ => mon_op_assoc_sym M
|}.

(*
   本节说明 Connected 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example WideDeloop_Deloop (M : MonObject) : WideDeloop M poly_unit = Deloop M
  := eq_refl.

(* Its endomorphism monoid at every object is M itself, on the nose — the
   [hom_monoid_Deloop] round trip of Construction/Deloop.v, widened. *)
Example WideDeloop_hom_monoid (M : MonObject) (A : Type) (a : A) :
  hom_monoid (WideDeloop M A) a = M := eq_refl.

(* If M is a group then [WideDeloop M A] is a groupoid: the inverse of an
   arrow is the inverse of the element, at any pair of objects. *)
Definition WideDeloop_IsGroupoid (G : GrpObject) (A : Type) :
  IsGroupoid (WideDeloop G A).
Proof.
  intros x y f.
  refine (@Build_IsIsomorphism (WideDeloop G A) x y f (grp_inv f) _ _).
  - apply grp_inv_r.
  - apply grp_inv_l.
Defined.

(* And it is connected, by the one-step zig-zag carrying the unit of M —
   every hom-set is inhabited, whatever A is. *)
Definition WideDeloop_Connected (M : MonObject) (A : Type) :
  Connected (WideDeloop M A) :=
  @arrow_connected (WideDeloop M A) (fun _ _ => mon_unit).

(** ** The structure theorem, exercised *)

(* Two objects, eight arrows, vertex group Z/2 at each of them. *)
Definition Bool_Wide : Category := WideDeloop Bool_Xor_Grp bool.

Definition Bool_Wide_IsGroupoid : IsGroupoid Bool_Wide :=
  WideDeloop_IsGroupoid Bool_Xor_Grp bool.

Definition Bool_Wide_Connected : Connected Bool_Wide :=
  WideDeloop_Connected Bool_Xor_Grp bool.

(* Its vertex group at [true] really is Z/2: both data fields agree with
   [Bool_Xor_Grp] on the nose. *)
Example Bool_Wide_vertex_monoid :
  grp_monoid (vertex_group Bool_Wide_IsGroupoid true) = grp_monoid Bool_Xor_Grp
  := eq_refl.

Example Bool_Wide_vertex_inv :
  @grp_inv (vertex_group Bool_Wide_IsGroupoid true) = @grp_inv Bool_Xor_Grp
  := eq_refl.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Bool_Wide_structure :
  EquivalenceOfCategories (vertex_incl Bool_Wide_IsGroupoid true) :=
  connected_deloop_equiv Bool_Wide_IsGroupoid Bool_Wide_Connected true.

(* The same statement at the other object, to exhibit the "any one vertex
   group" clause with a second choice actually made. *)
Definition Bool_Wide_structure_false :
  EquivalenceOfCategories (vertex_incl Bool_Wide_IsGroupoid false) :=
  connected_deloop_equiv Bool_Wide_IsGroupoid Bool_Wide_Connected false.

(* And the conjugation isomorphism between the two vertex groups, which is
   what makes the two statements above compatible. *)
Definition Bool_Wide_conjugation :
  MonIso (vertex_group Bool_Wide_IsGroupoid true)
         (vertex_group Bool_Wide_IsGroupoid false) :=
  conjugation_iso Bool_Wide_IsGroupoid
    (connected_arrow Bool_Wide_IsGroupoid Bool_Wide_Connected true false).

(** ** Connected does not mean "joined by an arrow" *)

(* [Roof] (Instance/Roof.v) is the walking span RNeg <-- RZero --> RPos.  It
   is connected: every pair of objects is joined by a zig-zag through RZero. *)
Definition Roof_Connected : Connected Roof.
Proof.
  intros x y.
  (* [destruct] replaces the objects by bare [RoofObj] constructors, which no
     longer carry the category in their type, so each chain names [Roof]
     explicitly. *)
  destruct x, y.
  - exact (@zz_nil Roof RNeg).
  - exact (@zz_bwd Roof RNeg RZero RZero ZeroNeg (@zz_nil Roof RZero)).
  - exact (@zz_bwd Roof RNeg RZero RPos ZeroNeg
             (@zz_fwd Roof RZero RPos RPos ZeroPos (@zz_nil Roof RPos))).
  - exact (@zz_fwd Roof RZero RNeg RNeg ZeroNeg (@zz_nil Roof RNeg)).
  - exact (@zz_nil Roof RZero).
  - exact (@zz_fwd Roof RZero RPos RPos ZeroPos (@zz_nil Roof RPos)).
  - exact (@zz_bwd Roof RPos RZero RNeg ZeroPos
             (@zz_fwd Roof RZero RNeg RNeg ZeroNeg (@zz_nil Roof RNeg))).
  - exact (@zz_bwd Roof RPos RZero RZero ZeroPos (@zz_nil Roof RZero)).
  - exact (@zz_nil Roof RPos).
Defined.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Roof_no_arrow_neg_pos : (RNeg ~{Roof}~> RPos) → False.
Proof. exact RNeg_RPos_absurd. Qed.

Corollary Roof_not_arrow_connected : (∀ x y : Roof, x ~> y) → False.
Proof. intro H. exact (Roof_no_arrow_neg_pos (H RNeg RPos)). Qed.

(* The two forms can come apart only outside groupoids, since [zigzag_hom]
   collapses them inside one.  [Roof] is indeed not a groupoid: the arrow
   ZeroNeg has no inverse, there being no arrow RNeg ~> RZero. *)
Theorem Roof_not_groupoid : IsGroupoid Roof → False.
Proof.
  intro G.
  exact (RNeg_RZero_absurd (ginv G ZeroNeg)).
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary Roof_not_groupoid_via_collapse : IsGroupoid Roof → False.
Proof.
  intro G.
  exact (Roof_no_arrow_neg_pos (zigzag_hom G (Roof_Connected RNeg RPos))).
Qed.

(** ** A groupoid that is not connected, and for which the theorem's
       conclusion is false *)

(*
   本节说明 Connected 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Two_Discrete_IsGroupoid : IsGroupoid Two_Discrete.
Proof.
  intros x y f.
  destruct f.
  - refine (@Build_IsIsomorphism Two_Discrete TwoDX TwoDX TwoDIdX TwoDIdX _ _);
      reflexivity.
  - refine (@Build_IsIsomorphism Two_Discrete TwoDY TwoDY TwoDIdY TwoDIdY _ _);
      reflexivity.
Defined.

(* Every arrow of a discrete category has equal endpoints, so every zig-zag
   does too — a chain cannot leave the object it starts at. *)
Lemma TwoDHom_endpoints {x y : TwoDObj} (f : TwoDHom x y) : x = y.
Proof. now destruct f. Qed.

Lemma Two_Discrete_zigzag_endpoints {x y : Two_Discrete} (s : ZigZag x y) :
  x = y.
Proof.
  induction s as [ w | a b c f s' IH | a b c f s' IH ].
  - reflexivity.
  - transitivity b; [ exact (TwoDHom_endpoints f) | exact IH ].
  - transitivity b; [ symmetry; exact (TwoDHom_endpoints f) | exact IH ].
Qed.

Theorem Two_Discrete_not_connected : Connected Two_Discrete → False.
Proof.
  intro K.
  pose proof (Two_Discrete_zigzag_endpoints (K TwoDX TwoDY)) as H.
  discriminate H.
Qed.

(*
   本节说明 Connected 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Two_Discrete_no_deloop_equivalence :
  EquivalenceOfCategories (vertex_incl Two_Discrete_IsGroupoid TwoDX) → False.
Proof.
  intro E.
  exact (Two_Discrete_not_connected
           (deloop_equiv_connected Two_Discrete_IsGroupoid TwoDX E)).
Qed.
