Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Natural.Transformation.Opposite.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Two.

Generalizable All Variables.

(** * Transport of colimits, and the induced map between (co)limits *)

(*
 nLab: https://ncatlab.org/nlab/show/colimit
 nLab: https://ncatlab.org/nlab/show/opposite+functor

   本文件给出余极限相关等价/构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** (A) Oppositization respects the functor setoid *)

(*
   Given e : G ≈ G' — which, for [函子_Setoid], is a 自然

   本节说明相关定义、性质与动机。 同构 bundled its coherence — 反 函子 are equivalent, taking each component's INVERSE.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Opposite_Functor_respects {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') : Opposite_Functor G ≈ Opposite_Functor G'.
Proof.
  exists (fun x => Isomorphism_Opposite (`1 e x)).
  intros x y f; simpl.
  rewrite comp_assoc.
  exact (`2 e y x f).
Defined.

(* The same fact registered for setoid rewriting, which is what a
   consumer dualizing a limit result actually reaches for. *)

#[export]
Instance Opposite_Functor_Proper {J C : Category} :
  Proper (equiv ==> equiv) (@Opposite_Functor J C) :=
  fun _ _ e => Opposite_Functor_respects e.

(*
   本节说明相关定义、性质与动机。 The inverse passage costs nothing, reason is tree's own.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Opposite_Functor_reflects {J C : Category} {G G' : J ⟶ C}
  (e : Opposite_Functor G ≈ Opposite_Functor G') : G ≈ G' :=
  Opposite_Functor_respects e.

(*
   本节说明相关定义、性质与动机。 The two passages return ISOMORPHISM FAMILY nose, both. 复合 orders — [同构] has primitive projections eta, so [同构_反] applied twice is identity definitionally.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example Opposite_Functor_reflects_respects {J C : Category}
  {G G' : J ⟶ C} (e : G ≈ G') (x : J) :
  `1 (Opposite_Functor_reflects (Opposite_Functor_respects e)) x
  = `1 e x := eq_refl.

Example Opposite_Functor_respects_reflects {J C : Category}
  {G G' : J ⟶ C} (e : Opposite_Functor G ≈ Opposite_Functor G') (x : J) :
  `1 (Opposite_Functor_respects (Opposite_Functor_reflects e)) x
  = `1 e x := eq_refl.

(** ** (B) Transport of colimits along a natural isomorphism *)

(*
   The duals of Theory/等价/极限.v's [cone_transport],

   本节说明相关定义、性质与动机。 [cone_transport_inv], [isalimit_transport] [极限_transport], obtained riding (A) rather than second proof.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition cocone_transport {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cocone G) : Cocone G' :=
  cone_transport (Opposite_Functor_respects e) N.

Definition cocone_transport_inv {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cocone G') : Cocone G :=
  cone_transport_inv (Opposite_Functor_respects e) N.

Definition isacolimit_transport {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (H : IsAColimit G c) : IsAColimit G' c :=
  isalimit_transport (Opposite_Functor_respects e) H.

Definition colimit_transport {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (L : Colimit G) : Colimit G' :=
  limit_transport (Opposite_Functor_respects e) L.

(*
   本节说明相关定义、性质与动机。 Covariant readbacks. A cocone's injections run INTO apex, so.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cocone_transport_inj {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cocone G) (x : J) :
  cocone_inj (cocone_transport e N) x ≈ cocone_inj N x ∘ from (`1 e x).
Proof. reflexivity. Qed.

Lemma cocone_transport_inv_inj {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cocone G') (x : J) :
  cocone_inj (cocone_transport_inv e N) x ≈ cocone_inj N x ∘ to (`1 e x).
Proof. reflexivity. Qed.

Lemma isacolimit_transport_inj {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (H : IsAColimit G c) (x : J) :
  colimit_inj (isacolimit_transport e H) x
    ≈ colimit_inj H x ∘ from (`1 e x).
Proof. reflexivity. Qed.

Lemma isacolimit_transport_med {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (H : IsAColimit G c) (N : Cocone G') :
  colimit_med (isacolimit_transport e H) N
    ≈ colimit_med H (cocone_transport_inv e N).
Proof. reflexivity. Qed.

(* The strict forms.  Each names the constant it is about on one side and
   a genuinely different expression — built from the donor accessors — on
   the other, so none is a tautology. *)

Example cocone_transport_inj_strict {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cocone G) (x : J) :
  cocone_inj (cocone_transport e N) x = cocone_inj N x ∘ from (`1 e x)
  := eq_refl.

Example cocone_transport_inv_inj_strict {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cocone G') (x : J) :
  cocone_inj (cocone_transport_inv e N) x = cocone_inj N x ∘ to (`1 e x)
  := eq_refl.

Example isacolimit_transport_inj_strict {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (H : IsAColimit G c) (x : J) :
  colimit_inj (isacolimit_transport e H) x
  = colimit_inj H x ∘ from (`1 e x) := eq_refl.

Example isacolimit_transport_med_strict {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (H : IsAColimit G c) (N : Cocone G') :
  colimit_med (isacolimit_transport e H) N
  = colimit_med H (cocone_transport_inv e N) := eq_refl.

(* The apex is untouched: transport moves the injections, never the
   object they land in.  This is the clause the induced-map statement of
   section (C) below cannot make. *)

Example colimit_transport_apex {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (L : Colimit G) :
  colimit_apex (colimit_transport e L) = colimit_apex L := eq_refl.

(** ** (C) The induced map, without invertibility *)

(*
   A bundled 极限 witness, read as a cone.  (Theory/等价/极限.v

   本节说明相关定义、性质与动机。 has [isalimit_to_极限] [极限] packaging; [Cone]-level repackaging is not tree, two constructions below need it.)

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition isalimit_cone {J C : Category} {G : J ⟶ C} {c : C}
  (H : IsALimit G c) : Cone G :=
  @Build_Cone J C G c (@limit_acone _ _ _ _ H).

Section Induced.

Context {J : Category}.
Context {C : Category}.
Context {G G' : J ⟶ C}.
Context (a : G ⟹ G').

(*
   本节：Push cone over G along α: postcompose each leg component.. This generalizes Theory/等价/极限.v's [cone_transport], which is this construction at 正向 components 同构 (see [cone_along_is_cone_transport] below);

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition cone_along_leg (N : Cone G) (x : J) :
  vertex_obj[N] ~{C}~> G' x :=
  transform[a] x ∘ cone_leg N x.

Lemma cone_along_coherence (N : Cone G) {x y : J} (f : x ~{J}~> y) :
  fmap[G'] f ∘ cone_along_leg N x ≈ cone_along_leg N y.
Proof using a.
  unfold cone_along_leg.
  rewrite comp_assoc.
  rewrite (@naturality _ _ _ _ a x y f).
  rewrite <- comp_assoc.
  now rewrite (cone_leg_coherence N f).
Qed.

Definition cone_along (N : Cone G) : Cone G' :=
  @Build_Cone J C G' (vertex_obj[N])
    (@Build_ACone J C (vertex_obj[N]) G' (cone_along_leg N)
       (fun x y f => cone_along_coherence N f)).

Section AtWitnesses.

Context {c c' : C}.
Context (HL : IsALimit G c).
Context (HL' : IsALimit G' c').

(*
   The comparison: push the 极限 cone of G along α and mediate through

   本节说明相关定义、性质与动机。 the 极限 G'. NOTE hypotheses — two 极限, handed explicitly;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition limit_induced : c ~{C}~> c' :=
  limit_med HL' (cone_along (isalimit_cone HL)).

Lemma limit_induced_commutes (x : J) :
  limit_leg HL' x ∘ limit_induced ≈ transform[a] x ∘ limit_leg HL x.
Proof using a HL HL'.
  exact (limit_med_commutes HL' (cone_along (isalimit_cone HL)) x).
Qed.

Lemma limit_induced_unique (v : c ~{C}~> c') :
  (∀ x : J, limit_leg HL' x ∘ v ≈ transform[a] x ∘ limit_leg HL x) →
  limit_induced ≈ v.
Proof using a HL HL'.
  intro Hv.
  exact (limit_med_unique HL' (cone_along (isalimit_cone HL)) v Hv).
Qed.

End AtWitnesses.

End Induced.

Arguments limit_induced {J C G G'} a {c c'} HL HL'.
Arguments limit_induced_commutes {J C G G'} a {c c'} HL HL' x.
Arguments limit_induced_unique {J C G G'} a {c c'} HL HL' v _.

(*
   The comparison at the identity 变换 is the identity, and it

   本节说明相关定义、性质与动机。 composes. These are 对象-level shadows functoriality [lim]; no 极限 FUNCTOR is built here.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma limit_induced_id {J C : Category} {G : J ⟶ C} {c : C}
  (HL : IsALimit G c) : limit_induced nat_id HL HL ≈ id.
Proof.
  apply limit_induced_unique.
  intro x; simpl.
  rewrite fmap_id, id_left, id_right.
  reflexivity.
Qed.

Lemma limit_induced_comp {J C : Category} {G G' G'' : J ⟶ C}
  (a : G ⟹ G') (b : G' ⟹ G'') {c c' c'' : C}
  (HL : IsALimit G c) (HL' : IsALimit G' c') (HL'' : IsALimit G'' c'') :
  limit_induced (b ∙ a) HL HL''
    ≈ limit_induced b HL' HL'' ∘ limit_induced a HL HL'.
Proof.
  apply limit_induced_unique.
  intro x; simpl.
  rewrite comp_assoc.
  rewrite (limit_induced_commutes b HL' HL'' x).
  rewrite <- comp_assoc.
  rewrite (limit_induced_commutes a HL HL' x).
  now rewrite comp_assoc.
Qed.

(** *** The colimit dual, covariantly *)

(*
   本节：[反_Transform] sends α : G ⟹ G' G'^op ⟹ G^op, so roles of. two 余极限 witnesses are exchanged when 极限 statement is instantiated — which is exactly what makes induced arrow run from 余极限 G 余极限 G'.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition colimit_induced {J C : Category} {G G' : J ⟶ C} (a : G ⟹ G')
  {c c' : C} (HC : IsAColimit G c) (HC' : IsAColimit G' c') :
  c ~{C}~> c' :=
  limit_induced (Opposite_Transform a) HC' HC.

Lemma colimit_induced_commutes {J C : Category} {G G' : J ⟶ C}
  (a : G ⟹ G') {c c' : C}
  (HC : IsAColimit G c) (HC' : IsAColimit G' c') (x : J) :
  colimit_induced a HC HC' ∘ colimit_inj HC x
    ≈ colimit_inj HC' x ∘ transform[a] x.
Proof. exact (limit_induced_commutes (Opposite_Transform a) HC' HC x). Qed.

Lemma colimit_induced_unique {J C : Category} {G G' : J ⟶ C}
  (a : G ⟹ G') {c c' : C}
  (HC : IsAColimit G c) (HC' : IsAColimit G' c') (v : c ~{C}~> c') :
  (∀ x : J, v ∘ colimit_inj HC x ≈ colimit_inj HC' x ∘ transform[a] x) →
  colimit_induced a HC HC' ≈ v.
Proof.
  intro Hv.
  exact (limit_induced_unique (Opposite_Transform a) HC' HC v Hv).
Qed.

Lemma colimit_induced_id {J C : Category} {G : J ⟶ C} {c : C}
  (HC : IsAColimit G c) : colimit_induced nat_id HC HC ≈ id.
Proof.
  apply colimit_induced_unique.
  intro x; simpl.
  rewrite fmap_id, id_left, id_right.
  reflexivity.
Qed.

Lemma colimit_induced_comp {J C : Category} {G G' G'' : J ⟶ C}
  (a : G ⟹ G') (b : G' ⟹ G'') {c c' c'' : C}
  (HC : IsAColimit G c) (HC' : IsAColimit G' c')
  (HC'' : IsAColimit G'' c'') :
  colimit_induced (b ∙ a) HC HC''
    ≈ colimit_induced b HC' HC'' ∘ colimit_induced a HC HC'.
Proof.
  apply colimit_induced_unique.
  intro x; simpl.
  rewrite <- comp_assoc.
  rewrite (colimit_induced_commutes a HC HC' x).
  rewrite comp_assoc.
  rewrite (colimit_induced_commutes b HC' HC'' x).
  now rewrite comp_assoc.
Qed.

(** ** How (B) and (C) fit together *)

(*
   The 正向 components of a [函子_Setoid] 等价 form a

   本节：自然变换: coherence field [函子_Setoid] is naturality square disguise, [fun_equiv_to_fmap] (Theory/函子.v) is exactly square, other orientation.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition fun_equiv_transform {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') : G ⟹ G'.
Proof.
  apply (Build_Transform' (fun x => to (`1 e x))).
  intros x y f.
  symmetry.
  exact (fun_equiv_to_fmap e x y f).
Defined.

Example fun_equiv_transform_component {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (x : J) :
  transform[fun_equiv_transform e] x = to (`1 e x) := eq_refl.

(*
   Theory/等价/极限.v's [cone_transport] IS [cone_along] at those

   本节说明相关定义、性质与动机。 components, LEG BY LEG nose, so invertible case (C) cone half (B) are one construction.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example cone_along_is_cone_transport {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') (N : Cone G) (x : J) :
  cone_leg (cone_along (fun_equiv_transform e) N) x
  = cone_leg (cone_transport e N) x := eq_refl.

(*
   And the comparison induced between a 极限 and its OWN transport is

   本节说明相关定义、性质与动机。 the identity. This is what (1) adds (2): apex is pinned, so comparison has nowhere go.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma limit_induced_of_transport {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (HL : IsALimit G c) :
  limit_induced (fun_equiv_transform e) HL (isalimit_transport e HL) ≈ id.
Proof.
  apply limit_induced_unique.
  intro x.
  now rewrite id_right.
Qed.

(*
   The 余极限 reading of the same fact.  The 变换 is the

   本节说明相关定义、性质与动机。 BACKWARD family here: transporting 余极限 precomposes its injections [from], so comparison that comes out identity is one induced inverse components.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition fun_equiv_transform_inv {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') : G' ⟹ G.
Proof.
  apply (Build_Transform' (fun x => from (`1 e x))).
  intros x y f.
  exact (fun_equiv_fmap_from e x y f).
Defined.

Lemma colimit_induced_of_transport {J C : Category} {G G' : J ⟶ C}
  (e : G ≈ G') {c : C} (H : IsAColimit G c) :
  colimit_induced (fun_equiv_transform_inv e) (isacolimit_transport e H) H
    ≈ id.
Proof.
  apply colimit_induced_unique.
  intro x.
  now rewrite id_left.
Qed.

(** ** Witnesses over the walking arrow *)

(*
   本节说明相关定义、性质与动机。 Non-vacuity. The cheapest index shape non-identity arrow is.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition two_limit_leg {C : Category} (D : _2 ⟶ C) (x : _2) :
  D TwoX ~{C}~> D x :=
  match x with
  | TwoX => id
  | TwoY => fmap[D] TwoXY
  end.

Lemma two_limit_coherence {C : Category} (D : _2 ⟶ C) {x y : _2}
  (f : x ~{_2}~> y) :
  fmap[D] f ∘ two_limit_leg D x ≈ two_limit_leg D y.
Proof.
  destruct f; simpl.
  - rewrite id_right.
    exact (@fmap_id _ _ D TwoX).
  - rewrite (@fmap_id _ _ D TwoY).
    now rewrite id_left.
  - now rewrite id_right.
Qed.

Program Definition two_IsALimit {C : Category} (D : _2 ⟶ C) :
  IsALimit D (D TwoX) := {|
  limit_acone :=
    @Build_ACone _2 C (D TwoX) D (two_limit_leg D)
      (fun x y f => two_limit_coherence D f)
|}.
Next Obligation.
  unshelve refine (Build_Unique _ _ _ (cone_leg N TwoX) _ _).
  - intro x; destruct x; simpl.
    + now rewrite id_left.
    + exact (cone_leg_coherence N TwoXY).
  - intros v Hv.
    specialize (Hv TwoX); simpl in Hv.
    rewrite id_left in Hv.
    now symmetry.
Defined.

Definition two_colimit_inj {C : Category} (D : _2 ⟶ C) (x : _2) :
  D x ~{C}~> D TwoY :=
  match x with
  | TwoX => fmap[D] TwoXY
  | TwoY => id
  end.

Program Definition two_IsAColimit {C : Category} (D : _2 ⟶ C) :
  IsAColimit D (D TwoY) := {|
  limit_acone :=
    @Build_ACone (Opposite _2) (Opposite C) (D TwoY) (Opposite_Functor D)
      (two_colimit_inj D) _
|}.
Next Obligation.
  destruct f; simpl.
  - rewrite (@fmap_id _ _ D TwoX).
    now rewrite id_right.
  - rewrite id_left.
    exact (@fmap_id _ _ D TwoY).
  - now rewrite id_left.
Qed.
Next Obligation.
  unshelve refine (Build_Unique _ _ _ (cocone_inj N TwoY) _ _).
  - intro x; destruct x; simpl.
    + exact (cocone_inj_coherence N TwoXY).
    + now rewrite id_right.
  - intros v Hv.
    specialize (Hv TwoY); simpl in Hv.
    rewrite id_right in Hv.
    now symmetry.
Defined.

(** *** A non-invertible transformation with a non-invertible comparison *)

(*
   Ambient [_2] as well as index [_2].  The diagram [Id[_2]] has 余极限

   本节说明相关定义、性质与动机。 apex TwoY; constant diagram at TwoY has 余极限 apex TwoY too, so sharp witness we take LIMITS instead, whose apexes are TwoX TwoY — genuinely different 对象.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition two_const : _2 ⟶ _2 := {|
  fobj := fun _ => TwoY;
  fmap := fun _ _ _ => id
|}.

Program Definition two_shift : Id[_2] ⟹ two_const := {|
  transform := fun x => match x with
                        | TwoX => TwoXY
                        | TwoY => TwoIdY
                        end
|}.
Solve Obligations with (intros; apply Two_thin).

(*
   本节说明相关定义、性质与动机。 The two diagrams are NOT naturally isomorphic, so section (B) does not. apply this pair at all: 同构 would supply arrow TwoY ~> TwoX, [_2] has none.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma two_shift_diagrams_not_isomorphic : Id[_2] ≈ two_const → False.
Proof.
  intro e.
  exact (TwoHom_Y_X_absurd (from (`1 e TwoX))).
Qed.

(* The transformation itself is not invertible at TwoX ... *)

Lemma two_shift_not_invertible :
  @IsIsomorphism _2 TwoX TwoY (transform[two_shift] TwoX) → False.
Proof. exact TwoXY_not_iso. Qed.

(*
   ... the two diagrams take TwoX to genuinely different 对象, which

   本节说明相关定义、性质与动机。 is what makes two 极限 apexes different: [two_IsALimit] pins apex diagram [D] [D TwoX], so two 对象 actions read off below ARE two apexes.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example two_shift_fobj_at_TwoX :
  (fobj[Id[_2]] TwoX, fobj[two_const] TwoX) = (TwoX, TwoY) := eq_refl.

Lemma two_shift_apexes_distinct : TwoX = TwoY → False.
Proof. discriminate. Qed.

(* ... and the induced comparison, which exists by (C), is not an
   isomorphism.  It cannot be: it is an arrow TwoX ~> TwoY, and [_2] has
   no arrow back. *)

Definition two_shift_induced : TwoX ~{_2}~> TwoY :=
  limit_induced two_shift (two_IsALimit Id[_2]) (two_IsALimit two_const).

(*
   It COMPUTES to the 变换's component at TwoX.  This is why

   本节说明相关定义、性质与动机。 the two universal properties above are closed [Defined]: [Qed] mediator is opaque only [≈] form below survives, which over thin ambient says nothing.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example two_shift_induced_computes : two_shift_induced = TwoXY := eq_refl.

Theorem two_shift_induced_not_iso :
  @IsIsomorphism _2 TwoX TwoY two_shift_induced → False.
Proof. intros [g _ _]; exact (TwoHom_Y_X_absurd g). Qed.

(*
   本节说明相关定义、性质与动机。 The comparison does satisfy its defining triangle, so witness. exercises 普遍性质 not merely existence arrow.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma two_shift_induced_commutes (x : _2) :
  limit_leg (two_IsALimit two_const) x ∘ two_shift_induced
    ≈ transform[two_shift] x ∘ limit_leg (two_IsALimit Id[_2]) x.
Proof.
  exact (limit_induced_commutes two_shift (two_IsALimit Id[_2])
           (two_IsALimit two_const) x).
Qed.

(** *** Colimit transport, exercised: distinct diagrams, moved legs *)

(*
   本节说明相关定义、性质与动机。 WHAT THIS COSTS, MEASURED. A sharp (B) witness needs two diagrams. that are naturally isomorphic genuinely different, constant diagrams cannot be different (their arrow action is forced [id]), so diagram must act non-trivially [TwoXY].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition two_endo_map {C : Category} {X : C} (u : X ~> X)
  (x y : _2) (f : x ~{_2}~> y) : X ~{C}~> X :=
  match f with
  | TwoIdX => id
  | TwoIdY => id
  | TwoXY  => u
  end.

Program Definition two_endo {C : Category} (X : C) (u : X ~> X) :
  _2 ⟶ C := {|
  fobj := fun _ => X;
  fmap := two_endo_map u
|}.
Next Obligation. destruct x; reflexivity. Qed.
Next Obligation.
  pose proof (TwoHom_inv _ _ f) as Hf.
  pose proof (TwoHom_inv _ _ g) as Hg.
  destruct x, y, z; simpl in *; try contradiction; subst; simpl;
    first [ now rewrite id_left | now rewrite id_right ].
Qed.

Example two_endo_arrow {C : Category} (X : C) (u : X ~> X) :
  fmap[two_endo X u] TwoXY = u := eq_refl.

(* The ambient: [bool] as a discrete setoid, with negation as a
   non-identity self-isomorphism of it. *)

Definition two_bool_set : SetoidObject :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

Program Definition two_negb_map :
  two_bool_set ~{Sets}~> two_bool_set := {| morphism := negb |}.

Program Definition two_negb_iso :
  @Isomorphism Sets two_bool_set two_bool_set :=
  {| to := two_negb_map ; from := two_negb_map |}.
Next Obligation. destruct x; reflexivity. Qed.
Next Obligation. destruct x; reflexivity. Qed.

(* Two diagrams over the walking arrow, sending [TwoXY] to [id] and to
   negation respectively. *)

Definition two_id_diagram : _2 ⟶ Sets := @two_endo Sets two_bool_set id.

Definition two_negb_diagram : _2 ⟶ Sets :=
  @two_endo Sets two_bool_set two_negb_map.

(* They are naturally isomorphic — identity at TwoX, negation at TwoY,
   the square closing because negation is its own inverse ... *)

Definition two_diagrams_equiv : two_id_diagram ≈ two_negb_diagram.
Proof.
  exists (fun x => match x with
                   | TwoX => iso_id
                   | TwoY => two_negb_iso
                   end).
  intros x y f; destruct f; simpl; intro b; destruct b; reflexivity.
Defined.

(*
   本节说明相关定义、性质与动机。 ... they are genuinely different diagrams: their arrow actions at. [TwoXY] are not even [≈]-equal, which is strictly stronger than refuting Leibniz equality two 函子 records.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma two_diagrams_differ :
  fmap[two_id_diagram] TwoXY ≈ fmap[two_negb_diagram] TwoXY → False.
Proof. intro K; specialize (K true); simpl in K; discriminate. Qed.

(*
   The 余极限 of the first diagram, and the transport of it along the

   本节说明相关定义、性质与动机。 同构. THE TRANSPORT VISIBLY MOVES A LEG: injection at TwoY goes from identity negation, two are provably not [≈]-equal.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition two_id_colimit : IsAColimit two_id_diagram two_bool_set :=
  two_IsAColimit two_id_diagram.

(*
   本节说明相关定义、性质与动机。 MEASURED REJECTION: strict form next statement,. [... TwoY = two_negb_map], is rejected. The transported leg is [id ∘ two_negb_map], 复合 [Sets] rebuilds [SetoidMorphism] record rather than reducing, so [id ∘ _] residue survives.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma two_transport_inj_computes :
  colimit_inj (isacolimit_transport two_diagrams_equiv two_id_colimit)
    TwoY ≈ two_negb_map.
Proof. intro b; destruct b; reflexivity. Qed.

Example two_id_colimit_inj_Y :
  colimit_inj two_id_colimit TwoY = id := eq_refl.

Theorem two_transport_moves_inj :
  colimit_inj (isacolimit_transport two_diagrams_equiv two_id_colimit) TwoY
    ≈ colimit_inj two_id_colimit TwoY → False.
Proof. intro K; specialize (K true); simpl in K; discriminate. Qed.

(* The walking arrow's own (co)limit legs compute, at the identity
   diagram, which is what the two Examples above are read against. *)

Example two_colimit_inj_X :
  colimit_inj (two_IsAColimit Id[_2]) TwoX = TwoXY := eq_refl.

Example two_colimit_inj_Y :
  colimit_inj (two_IsAColimit Id[_2]) TwoY = TwoIdY := eq_refl.

Example two_limit_leg_Y :
  limit_leg (two_IsALimit Id[_2]) TwoY = TwoXY := eq_refl.
