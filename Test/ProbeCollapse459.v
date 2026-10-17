(*
   本文件为测试：ProbeCollapse459。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Coequalizer.Wide.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.Quotient.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Homotopy.
Require Import Category.Instance.Top.Quotient.Pairs.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live *)

(* The instrument *)
Fail Check probe459_absent_name.

(** ** Instance/Top/Quotient.v: small wide coequalizers, W-a and W-b *)

(* CONTROL: the instance at an index at or below the points, the class's
   first inhabitant, and its object read back at [eq_refl]. *)
Definition p459_hwc_small@{i o h | i <= o, o < h +} :
  HasWideCoequalizers@{i h h} Top@{h o} :=
  Top_HasWideCoequalizers_small@{i o h}.

Example p459_hwc_obj@{i o h | i <= o, o < h +}
  {I : Type@{i}} {x y : Top@{h o}} (fs : I → x ~{Top@{h o}}~> y) :
  `1 (@wide_coeq Top@{h o} Top_HasWideCoequalizers_small@{i o h} I x y fs)
    = TQuot y (WSetsCoeq@{i o} (fun i => continuous_map (fs i)))
        (wsets_coeq_proj@{i o} (fun i => continuous_map (fs i))) := eq_refl.

(* N1 *)
Fail Definition p459_hwc_at_hom@{o h | o < h +} :
  HasWideCoequalizers@{h h h} Top@{h o} :=
  Top_HasWideCoequalizers_small@{h o h}.

(* CONTROL: the relation under a closed constraint list that declares
   [i <= o]. *)
Definition p459_rel_bounded@{i o | i <= o} {I : Type@{i}}
  {A B : SetoidObject@{o o}} (fs : I → SetoidMorphism@{o o o} A B) :
  B → B → Type@{o} := wcoeq_rel@{i o} fs.

(* N2 *)
Fail Definition p459_rel_unbounded@{i o |} {I : Type@{i}}
  {A B : SetoidObject@{o o}} (fs : I → SetoidMorphism@{o o o} A B) :
  B → B → Type@{o} := wcoeq_rel@{i o} fs.

(* CONTROL: [wcoeq_rel] declared afresh under the closed binder with the
   bound, and without its glue constructor under the binder without it. *)
Inductive p459_wrel@{i o | i <= o} {I : Type@{i}} {A B : SetoidObject@{o o}}
  (fs : I → SetoidMorphism@{o o o} A B) : B → B → Type@{o} :=
  | p459_wbase : ∀ b1 b2 : B, b1 ≈ b2 → p459_wrel b1 b2
  | p459_wglue : ∀ (i j : I) (a : A), p459_wrel (fs i a) (fs j a)
  | p459_wsym : ∀ b1 b2 : B, p459_wrel b1 b2 → p459_wrel b2 b1
  | p459_wtrans : ∀ b1 b2 b3 : B,
      p459_wrel b1 b2 → p459_wrel b2 b3 → p459_wrel b1 b3.

Inductive p459_wrel_noglue@{i o |} {I : Type@{i}}
  {A B : SetoidObject@{o o}} (fs : I → SetoidMorphism@{o o o} A B) :
  B → B → Type@{o} :=
  | p459_nbase : ∀ b1 b2 : B, b1 ≈ b2 → p459_wrel_noglue b1 b2
  | p459_nsym : ∀ b1 b2 : B, p459_wrel_noglue b1 b2 → p459_wrel_noglue b2 b1
  | p459_ntrans : ∀ b1 b2 b3 : B,
      p459_wrel_noglue b1 b2 → p459_wrel_noglue b2 b3 →
      p459_wrel_noglue b1 b3.

(* N3 *)
Fail Inductive p459_wrel_unbounded@{i o |} {I : Type@{i}}
  {A B : SetoidObject@{o o}} (fs : I → SetoidMorphism@{o o o} A B) :
  B → B → Type@{o} :=
  | p459_ubase : ∀ b1 b2 : B, b1 ≈ b2 → p459_wrel_unbounded b1 b2
  | p459_uglue : ∀ (i j : I) (a : A), p459_wrel_unbounded (fs i a) (fs j a)
  | p459_usym : ∀ b1 b2 : B,
      p459_wrel_unbounded b1 b2 → p459_wrel_unbounded b2 b1
  | p459_utrans : ∀ b1 b2 b3 : B,
      p459_wrel_unbounded b1 b2 → p459_wrel_unbounded b2 b3 →
      p459_wrel_unbounded b1 b3.

(* CONTROL: the relation with its index at the points' universe. *)
Definition p459_rel_at_points@{o h | o < h +} (I : Type@{o})
  (A B : SetoidObject@{o o}) (fs : I → SetoidMorphism@{o o o} A B) :
  B → B → Type@{o} := wcoeq_rel fs.

(* N4 *)
Fail Definition p459_rel_at_hom@{o h | o < h +} (I : Type@{h})
  (A B : SetoidObject@{o o}) (fs : I → SetoidMorphism@{o o o} A B) :
  B → B → Type@{o} := wcoeq_rel fs.

(** ** Instance/Top/Quotient.v: Construction 5 and W-c *)

(* CONTROL: X/A's points are those of X, and their equality IS
   [collapse_rel], at [eq_refl]. *)
Example p459_collapse_equiv@{o} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) (x y : X) :
  @equiv _ (is_setoid (top_carrier (Top_collapse X I p))) x y
    = collapse_rel X I p x y := eq_refl.

(* CONTROL: the mediator is the competing map itself, as a setoid map and
   at every point, at [eq_refl]. *)
Example p459_desc_map_points@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j) :
  continuous_map (collapse_desc_map X I p k Hk) = collapse_med X I p k Hk
  := eq_refl.

Example p459_desc_map_at@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j)
  (x : X) :
  continuous_map (collapse_desc_map X I p k Hk) x = continuous_map k x
  := eq_refl.

(* CONTROL: Construction 5 in the elementary form at the flexible index,
   and at Mac Lane's index, the points of A. *)
Definition p459_collapse_coequalizer@{o h i | o < h, o <= i +}
  (X : TopSpace@{o}) (A : X → Type@{o}) :
  IsWideCoequalizer@{i h h} (C := Top@{h o}) (collapse_sub_family X A)
    (Top_collapse_sub X A) (collapse_sub_proj X A) :=
  collapse_coequalizer@{o h i} X A.

Definition p459_coequalizer_at_points@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o}) :
  IsWideCoequalizer@{o h h} (C := Top@{h o}) (collapse_sub_family X A)
    (Top_collapse_sub X A) (collapse_sub_proj X A) :=
  collapse_coequalizer@{o h o} X A.

(* CONTROL: the record read at the hom universe. *)
Definition p459_coequalizer_at_hom@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) :
  IsWideCoequalizer@{h h h} (C := Top@{h o}) (collapse_family X I p)
    (Top_collapse X I p) (collapse_proj X I p) :=
  collapse_family_coequalizer@{o h h} X I p.

(* N5 *)
Fail Definition p459_coequalizer_cumulative@{o h | o < h +}
  (X : TopSpace@{o}) (I : Type@{o}) (p : I → X) :
  IsWideCoequalizer@{h h h} (C := Top@{h o}) (collapse_family X I p)
    (Top_collapse X I p) (collapse_proj X I p) :=
  collapse_family_coequalizer@{o h o} X I p.

(* CONTROL: the colimit round trip fed the record at the hom universe,
   and the colimit form given a point of A. *)
Definition p459_colimit_flexible@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (i0 : I) :=
  is_wide_coequalizer_colimit (C := Top@{h o}) (collapse_family@{o h} X I p)
    i0 (collapse_family_coequalizer@{o h h} X I p).

Definition p459_collapse_colimit@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o}) (a0 : collapse_sub_points X A) :
  WideCoequalizer (AWide (C := Top@{h o}) (collapse_sub_family X A)) :=
  collapse_colimit X A a0.

(* N6 *)
Fail Definition p459_colimit_at_points@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (i0 : I) :=
  is_wide_coequalizer_colimit (C := Top@{h o}) (collapse_family@{o h} X I p)
    i0 (collapse_family_coequalizer@{o h o} X I p).

(* CONTROL: the collapse map is epic. *)
Definition p459_collapse_epic@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) : Epic (collapse_proj X I p) :=
  collapse_proj_epic X I p.

(** ** Instance/Top/Quotient.v: the comparisons and their extra universe *)

(* CONTROL: the direct collapse against the generic wide coequalizer, with
   [u] in the binder, the identity on points both ways at [eq_refl]. *)
Definition p459_iso_generic@{o h u | o < h, h < u +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) :
  Top_collapse X I p ≅[Top@{h o}] twcoeq_obj@{o o h} (collapse_family X I p) :=
  wide_coequalizer_unique _ (collapse_family_coequalizer@{o h o} X I p)
    (twcoeq_IsWideCoequalizer@{o o h} (collapse_family X I p)).

Example p459_iso_generic_to@{o h u | o < h, h < u +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (x : X) :
  continuous_map (to (collapse_iso_generic@{o h u} X I p)) x = x := eq_refl.

Example p459_iso_generic_from@{o h u | o < h, h < u +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (x : X) :
  continuous_map (from (collapse_iso_generic@{o h u} X I p)) x = x
  := eq_refl.

(* N7 *)
Fail Definition p459_iso_generic_no_u@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) :
  Top_collapse X I p ≅[Top@{h o}] twcoeq_obj@{o o h} (collapse_family X I p) :=
  wide_coequalizer_unique _ (collapse_family_coequalizer@{o h o} X I p)
    (twcoeq_IsWideCoequalizer@{o o h} (collapse_family X I p)).

(* CONTROL: X/∅ ≅ X with [u] in the binder. *)
Definition p459_empty_iso@{o h u | o < h, h < u +} (X : TopSpace@{o}) :
  Top_collapse_sub X (fun _ => False) ≅[Top@{h o}] X :=
  wide_coequalizer_unique _ (collapse_coequalizer@{o h o} X (fun _ => False))
    (wide_empty_id_IsWideCoequalizer _
       (fun a : collapse_sub_points X (fun _ => False) => projT2 a)).

(* N8 *)
Fail Definition p459_empty_iso_no_u@{o h | o < h +} (X : TopSpace@{o}) :
  Top_collapse_sub X (fun _ => False) ≅[Top@{h o}] X :=
  wide_coequalizer_unique _ (collapse_coequalizer@{o h o} X (fun _ => False))
    (wide_empty_id_IsWideCoequalizer _
       (fun a : collapse_sub_points X (fun _ => False) => projT2 a)).

(* CONTROL: X/∅ and X have the same underlying type at [eq_refl]. *)
Example p459_empty_carrier@{o} (X : TopSpace@{o}) :
  carrier (top_carrier (Top_collapse_sub X (fun _ => False)))
    = carrier (top_carrier X) := eq_refl.

(* N9 *)
Fail Example p459_empty_eq@{o} (X : TopSpace@{o}) :
  Top_collapse_sub X (fun _ => False) = X := eq_refl.

(* CONTROL: at ∅ every elementary wide coequalizer of the empty family is
   pointless; [collapse_empty_pointless] is a readback of [Empty_Top]'s
   carrier, and a proof closes for every subset of ∅
   ([p459_pointless_any]). *)
Definition p459_empty_coequalizer_pointless@{o h i | o < h, o <= i +}
  (Q : Top@{h o}) (e : Empty_Top@{o} ~{Top@{h o}}~> Q) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) Q e →
  top_carrier Q → False :=
  empty_wide_coequalizer_pointless@{o h i} Q e.

Definition p459_collapse_empty_pointless@{o} :
  top_carrier (Top_collapse_sub Empty_Top@{o} (fun _ => False)) → False :=
  collapse_empty_pointless@{o}.

Definition p459_pointless_any@{o}
  (A : carrier (top_carrier Empty_Top@{o}) → Type@{o}) :
  top_carrier (Top_collapse_sub Empty_Top@{o} A) → False :=
  fun z => match z with end.

(** ** Instance/Top/Quotient/Pairs.v: the category of pairs *)

(* CONTROL: the category and the two functors. *)
Definition p459_top_pairs@{h o | o < h +} : Category@{h h h} :=
  Top_pairs@{h o}.

Definition p459_point_pair_functor@{h o | o < h +} :
  Top_pointed@{h o} ⟶ Top_pairs@{h o} := PointPair@{h o}.

Definition p459_quotient_functor@{h o | o < h +} :
  Top_pairs@{h o} ⟶ Top_pointed@{h o} := PairQuotient@{h o}.

(* CONTROL: ⟨Y, *⟩'s subset is the Type-valued predicate y ≈ y0, at
   [eq_refl]. *)
Definition p459_point_sub@{o} (Y : PointedTop@{o}) :
  carrier (top_carrier (ptop_space Y)) → Type@{o} :=
  fun y => y ≈ ptop_pt Y.

Example p459_point_pair_sub@{h o | o < h +} (Y : PointedTop@{o}) :
  pair_sub (fobj[PointPair@{h o}] Y) = p459_point_sub Y := eq_refl.

(* N10 *)
Fail Definition p459_point_sub_prop@{o} (Y : PointedTop@{o}) :
  carrier (top_carrier (ptop_space Y)) → Prop :=
  fun y => y ≈ ptop_pt Y.

(* CONTROL: the squash eliminates into a proposition. *)
Definition p459_squash@{o} (Y : PointedTop@{o})
  (y : carrier (top_carrier (ptop_space Y)))
  (H : inhabited (y ≈ ptop_pt Y)) : inhabited (y ≈ ptop_pt Y) :=
  match H with inhabits e => inhabits e end.

(* N11 *)
Fail Definition p459_unsquash@{o} (Y : PointedTop@{o})
  (y : carrier (top_carrier (ptop_space Y)))
  (H : inhabited (y ≈ ptop_pt Y)) : y ≈ ptop_pt Y :=
  match H with inhabits e => e end.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p459_sat@{o} (X : TopSpace@{o}) (A : X → Type@{o}) (x : X) :
  Type@{o} := { a : X & (A a * (a ≈ x))%type }.

Definition p459_sat_respects@{o} (X : TopSpace@{o}) (A : X → Type@{o})
  (x y : X) (e : x ≈ y) (s : p459_sat X A x) : p459_sat X A y :=
  (projT1 s; (fst (projT2 s), transitivity (snd (projT2 s)) e)).

Definition p459_sat_rel@{o} (X : TopSpace@{o}) (A : X → Type@{o})
  (u v : option X) : Type@{o} :=
  match u, v with
  | Some x, Some y => ((x ≈ y) + (p459_sat X A x * p459_sat X A y))%type
  | Some x, None => p459_sat X A x
  | None, Some y => p459_sat X A y
  | None, None => poly_unit@{o}
  end.

Definition p459_sat_rel_Equivalence@{o} (X : TopSpace@{o})
  (A : X → Type@{o}) : Equivalence (p459_sat_rel X A) :=
  ltac:(constructor;
    [ intros [x|]; simpl; [left; reflexivity | exact ttt]
    | intros [x|] [y|] H; simpl in *; try exact H;
      destruct H as [H|[H1 H2]]; [left; now symmetry | right; exact (H2, H1)]
    | intros [x|] [y|] [z|] H1 H2; simpl in *; try exact ttt;
      [ destruct H1 as [H1|[H1 H1']], H2 as [H2|[H2 H2']];
        [ left; now transitivity y
        | right; split;
            [ exact (p459_sat_respects X A _ _ (symmetry H1) H2) | exact H2' ]
        | right; split; [ exact H1 | exact (p459_sat_respects X A _ _ H2 H1') ]
        | right; exact (H1, H2') ]
      | destruct H1 as [H1|[H1 H1']];
        [ exact (p459_sat_respects X A _ _ (symmetry H1) H2) | exact H1 ]
      | right; exact (H1, H2)
      | exact H1
      | destruct H2 as [H2|[H2 H2']];
        [ exact (p459_sat_respects X A _ _ H2 H1) | exact H2' ]
      | exact H2 ] ]).

Definition p459_unsat_rel@{o} (S : SetoidObject@{o o}) (A : S → Type@{o})
  (u v : option S) : Type@{o} :=
  match u, v with
  | Some x, Some y => ((x ≈ y) + (A x * A y))%type
  | Some x, None => A x
  | None, Some y => A y
  | None, None => poly_unit@{o}
  end.

Definition p459_bool_total : SetoidObject := {|
  carrier := bool;
  is_setoid := {| equiv := fun _ _ => poly_unit;
                  setoid_equiv := ltac:(constructor; repeat intro; exact ttt) |}
|}.

Definition p459_unsat_rel_not_transitive :
  (∀ (S : SetoidObject) (A : S → Type), Transitive (p459_unsat_rel S A)) →
  False :=
  fun H => match H p459_bool_total (fun b => b = true) (Some false)
                   (Some true) None (inl ttt) eq_refl in _ = b
                   return if b then False else True with
           | eq_refl => I
           end.

(** ** Instance/Top/Quotient/Pairs.v: the adjunction *)

(* CONTROL: the adjunction at its explicit record instance, its unit and
   counit read back at [eq_refl], and its hom-set isomorphism IS
   [pairs_quotient_iso] at [eq_refl]. *)
Definition p459_adjunction@{h o u v | o < h, h < u +} :
  @Adjunction@{h h h h h h h h u h v} Top_pointed@{h o} Top_pairs@{h o}
    PairQuotient@{h o} PointPair@{h o} :=
  pairs_quotient_adjunction@{h o u v}.

Example p459_unit_eval@{h o u v | o < h, h < u +} (X : PairTop@{o})
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map
    (pair_map (@unit _ _ _ _ pairs_quotient_adjunction@{h o u v} X)) x
    = Some x := eq_refl.

Example p459_counit_some@{h o u v | o < h, h < u +} (Y : PointedTop@{o})
  (y : carrier (top_carrier (ptop_space Y))) :
  continuous_map
    (ptop_map (@counit _ _ _ _ pairs_quotient_adjunction@{h o u v} Y))
    (Some y) = y := eq_refl.

Example p459_counit_none@{h o u v | o < h, h < u +} (Y : PointedTop@{o}) :
  continuous_map
    (ptop_map (@counit _ _ _ _ pairs_quotient_adjunction@{h o u v} Y)) None
    = ptop_pt Y := eq_refl.

Example p459_adj_is@{h o u v | o < h, h < u +} (X : PairTop@{o})
  (Y : PointedTop@{o}) :
  @adj _ _ _ _ pairs_quotient_adjunction@{h o u v} X Y
    = pairs_quotient_iso@{h o u} X Y := eq_refl.

(* N12 *)
Fail Example p459_hom_eq@{h o | o < h +} (X : PairTop@{o})
  (Y : PointedTop@{o}) :
  @hom Top_pointed@{h o} (PairQuotient@{h o} X) Y
    = @hom Top_pairs@{h o} X (PointPair@{h o} Y) := eq_refl.

(* CONTROL: the [Build_Adjunction'] term of the target at the explicit
   record instance. *)
Definition p459_adjunction_built@{h o u v | o < h, h < u +} :
  @Adjunction@{h h h h h h h h u h v} Top_pointed@{h o} Top_pairs@{h o}
    PairQuotient@{h o} PointPair@{h o} :=
  @Build_Adjunction' Top_pointed@{h o} Top_pairs@{h o} PairQuotient@{h o}
    PointPair@{h o} pairs_quotient_iso@{h o u}
    ltac:(intros X Y Z f g x; reflexivity)
    ltac:(intros X Y Z f g x; reflexivity).

(* N13 *)
Fail Definition p459_adjunction_built_notation@{h o u v | o < h, h < u +} :
  PairQuotient@{h o} ⊣ PointPair@{h o} :=
  @Build_Adjunction' Top_pointed@{h o} Top_pairs@{h o} PairQuotient@{h o}
    PointPair@{h o} pairs_quotient_iso@{h o u}
    ltac:(intros X Y Z f g x; reflexivity)
    ltac:(intros X Y Z f g x; reflexivity).

(* CONTROL: the finished adjunction read through the notation, [v] named
   in the binder. *)
Definition p459_adjunction_notation@{h o u v | o < h, h < u +} :
  PairQuotient@{h o} ⊣ PointPair@{h o} :=
  pairs_quotient_adjunction@{h o u v}.

(* N14 *)
Fail Definition p459_adjunction_notation_no_v@{h o u | o < h, h < u +} :
  PairQuotient@{h o} ⊣ PointPair@{h o} :=
  pairs_quotient_adjunction.

(** ** Instance/Top/Quotient/Pairs.v: X/A as the pushout *)

(* CONTROL: X/A is the pushout X ⊔_A ∗, its apex at [eq_refl]. *)
Definition p459_pushout@{h o | o < h +} (X : PairTop@{o}) :
  IsPushout (C := Top@{h o}) (pair_sub_incl X) (top_one (pair_sub_space X)) :=
  pquot_pushout@{h o} X.

Example p459_pushout_apex@{h o | o < h +} (X : PairTop@{o}) :
  pushout_apex (pquot_pushout@{h o} X) = pquot_space X := eq_refl.

(** ** Instance/Top/Quotient/Pairs.v: the colimit form, every A *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p459_wide_colimit@{o h | o < h +} (X : PairTop@{o}) :
  WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                     (collapse_sub_family (pair_space X) (pair_sub X))) :=
  pquot_wide_coequalizer_colimit@{o h} X.

Definition p459_wide_colimit_collapse_type@{o h | o < h +}
  (X : PairTop@{o}) :
  WideCoequalizer (AWide (C := Top@{h o})
                     (collapse_sub_family (pair_space X) (pair_sub X))) :=
  pquot_wide_coequalizer_colimit@{o h} X.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example p459_wide_colimit_apex@{o h | o < h +} (X : PairTop@{o}) :
  colimit_apex (pquot_wide_coequalizer_colimit@{o h} X) = pquot_space X
  := eq_refl.

Example p459_wide_colimit_in@{o h | o < h +} (X : PairTop@{o}) :
  colimit_inj (colimit_is_acolimit (pquot_wide_coequalizer_colimit@{o h} X))
    ParY = pquot_in X := eq_refl.

Example p459_wide_colimit_base@{o h | o < h +} (X : PairTop@{o}) :
  continuous_map
    (colimit_inj (colimit_is_acolimit (pquot_wide_coequalizer_colimit@{o h} X))
       ParX) ttt
    = ptop_pt (fobj[PairQuotient@{h o}] X) := eq_refl.

Example p459_wide_colimit_quotient@{o h | o < h +} (X : PairTop@{o}) :
  ptop_space (fobj[PairQuotient@{h o}] X)
    = colimit_apex (pquot_wide_coequalizer_colimit@{o h} X) := eq_refl.

(* CONTROL: at the empty subset the colimit is X ⊔ *; every colimit of the
   family has a point, at ⟨∅, ∅⟩ the new point [None]. *)
Definition p459_wide_colimit_empty@{o h | o < h +} (X : TopSpace@{o}) :
  colimit_apex (pquot_wide_coequalizer_colimit@{o h} (empty_pair X))
    ≅[Top@{h o}] Sum_Top X Point_Top@{o} :=
  pquot_wide_coequalizer_colimit_empty@{o h} X.

Definition p459_colimit_point@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o})
  (L : WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                          (collapse_sub_family X A))) :
  top_carrier (colimit_apex L) :=
  collapse_colimit_point@{o h} X A L.

Definition p459_colimit_pointed_at_empty@{o h | o < h +} :
  top_carrier (colimit_apex
    (pquot_wide_coequalizer_colimit@{o h} (empty_pair Empty_Top@{o}))) :=
  None.

(** ** Instance/Top/Quotient/Pairs.v: the elementary record, given a point *)

(* CONTROL: given a point of A, X/A is an elementary wide coequalizer of
   the point-inclusions, isomorphic to Construction 5's in [Top] and in
   [Top_pointed]. *)
Definition p459_pquot_coequalizer@{o h i | o < h, o <= i +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family (pair_space X) (pair_sub X))
    (pquot_space X) (pquot_in X) :=
  pquot_coequalizer@{o h i} X a0.

Definition p459_pquot_collapse_iso@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  Top_collapse_sub (pair_space X) (pair_sub X) ≅[Top@{h o}] pquot_space X :=
  wide_coequalizer_unique _
    (collapse_coequalizer@{o h o} (pair_space X) (pair_sub X))
    (pquot_coequalizer@{o h o} X a0).

Example p459_pquot_collapse_iso_to@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X))
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (to (pquot_collapse_iso@{o h u} X a0)) x = Some x
  := eq_refl.

Example p459_pquot_collapse_iso_from_none@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  continuous_map (from (pquot_collapse_iso@{o h u} X a0)) None = projT1 a0
  := eq_refl.

(* N15 *)
Fail Definition p459_pquot_collapse_iso_no_u@{o h | o < h +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  Top_collapse_sub (pair_space X) (pair_sub X) ≅[Top@{h o}] pquot_space X :=
  wide_coequalizer_unique _
    (collapse_coequalizer@{o h o} (pair_space X) (pair_sub X))
    (pquot_coequalizer@{o h o} X a0).

Definition p459_pquot_collapse_iso_pointed@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  collapse_pointed X a0 ≅[Top_pointed@{h o}] fobj[PairQuotient@{h o}] X :=
  pquot_collapse_iso_pointed@{o h u} X a0.

Example p459_collapse_pointed_pt@{o} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  ptop_pt (collapse_pointed X a0) = projT1 a0 := eq_refl.

(** ** Instance/Top/Quotient/Pairs.v: the empty subset *)

(* CONTROL: X/∅ is X₊ in [Top], [Some x] ↦ [inl x] and [None] ↦ [inr ttt]
   at [eq_refl]. *)
Definition p459_empty_sum_iso@{h o | o < h +} (X : TopSpace@{o}) :
  pquot_space (empty_pair X) ≅[Top@{h o}] Sum_Top X Point_Top@{o} :=
  pquot_empty_sum_iso@{h o} X.

Example p459_empty_sum_some@{h o | o < h +} (X : TopSpace@{o})
  (x : carrier (top_carrier X)) :
  continuous_map (to (pquot_empty_sum_iso@{h o} X)) (Some x)
    = Datatypes.inl x := eq_refl.

Example p459_empty_sum_none@{h o | o < h +} (X : TopSpace@{o}) :
  continuous_map (to (pquot_empty_sum_iso@{h o} X)) None
    = Datatypes.inr ttt := eq_refl.

(* N16 *)
Fail Example p459_empty_sum_eq@{o} (X : TopSpace@{o}) :
  pquot_space (empty_pair X) = Sum_Top X Point_Top@{o} := eq_refl.

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p459_pquot_empty_not_coequalizer@{o h i | o < h, o <= i +} :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family (pair_space (empty_pair Empty_Top@{o}))
       (pair_sub (empty_pair Empty_Top@{o})))
    (pquot_space (empty_pair Empty_Top@{o}))
    (pquot_in (empty_pair Empty_Top@{o})) → False :=
  pquot_empty_not_coequalizer@{o h i}.

Definition p459_pquot_needs_point@{o h i | o < h, o <= i +} :
  (∀ X : PairTop@{o},
     IsWideCoequalizer@{i h h} (C := Top@{h o})
       (collapse_sub_family (pair_space X) (pair_sub X))
       (pquot_space X) (pquot_in X)) → False :=
  pquot_coequalizer_needs_point@{o h i}.

Definition p459_no_pointed_coequalizer@{o h i | o < h, o <= i +}
  (Q : PointedTop@{o}) (e : Empty_Top@{o} ~{Top@{h o}}~> ptop_space Q) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) (ptop_space Q) e →
  False :=
  no_pointed_coequalizer_at_empty@{o h i} Q e.

Definition p459_no_assignment@{o h i | o < h, o <= i +}
  (L : PairTop@{o} → PointedTop@{o}) :
  (∀ X : PairTop@{o}, ∃ e : pair_space X ~{Top@{h o}}~> ptop_space (L X),
     IsWideCoequalizer@{i h h} (C := Top@{h o})
       (collapse_sub_family (pair_space X) (pair_sub X)) (ptop_space (L X)) e)
  → False :=
  no_pointed_elementary_coequalizers@{o h i} L.

Definition p459_no_functor@{o h i | o < h, o <= i +}
  (L : Top_pairs@{h o} ⟶ Top_pointed@{h o}) :
  (∀ X : PairTop@{o}, ∃ e : pair_space X ~{Top@{h o}}~> ptop_space (L X),
     IsWideCoequalizer@{i h h} (C := Top@{h o})
       (collapse_sub_family (pair_space X) (pair_sub X)) (ptop_space (L X)) e)
  → False :=
  no_pointed_elementary_coequalizers@{o h i} (fun X => fobj[L] X).

Definition p459_empty_colimit_not_elementary@{o h i | o < h, o <= i +}
  (L : WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                          (collapse_sub_family Empty_Top@{o}
                             (fun _ => False))))
  (e : Empty_Top@{o} ~{Top@{h o}}~> colimit_apex L) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) (colimit_apex L) e →
  False :=
  empty_colimit_not_elementary@{o h i} L e.

(** ** Guard: every constant of the two targets *)

(* Instance/Top/Quotient.v *)
Check Top_HasWideCoequalizers_small.
Check Top_collapse.
Check Top_collapse_equiv.
Check Top_collapse_sub.
Check Top_wide_coequalizer_obj.
Check WSetsCoeq.
Check collapse_carrier.
Check collapse_coequalizer.
Check collapse_colimit.
Check collapse_desc.
Check collapse_desc_map.
Check collapse_desc_map_points.
Check collapse_empty_iso.
Check collapse_empty_pointless.
Check collapse_family.
Check collapse_family_coequalizer.
Check collapse_family_colimit.
Check collapse_image.
Check collapse_image_respects.
Check collapse_iso_generic.
Check collapse_iso_generic_from.
Check collapse_iso_generic_to.
Check collapse_med.
Check collapse_med_proper.
Check collapse_proj.
Check collapse_proj_epic.
Check collapse_q.
Check collapse_rel.
Check collapse_rel_Equivalence.
Check collapse_setoid.
Check collapse_sub_family.
Check collapse_sub_incl.
Check collapse_sub_points.
Check collapse_sub_proj.
Check collapse_wcofork.
Check empty_wide_coequalizer_pointless.
Check twcoeq_IsWideCoequalizer.
Check twcoeq_cofork.
Check twcoeq_desc.
Check twcoeq_med.
Check twcoeq_obj.
Check twcoeq_proj.
Check wcoeq_rel.
Check wcoeq_rel_Equivalence.
Check wcoeq_rel_ind.
Check wcoeq_rel_of_cofork.
Check wcoeq_rel_rec.
Check wcoeq_rel_rect.
Check wcoeq_rel_sind.
Check wcq_base.
Check wcq_glue.
Check wcq_sym.
Check wcq_trans.
Check wsets_coeq_proj.

(* Instance/Top/Quotient/Pairs.v *)
Check Build_PairMap.
Check Build_PairTop.
Check PairMap.
Check PairMap_Setoid.
Check PairMap_equiv_Equivalence.
Check PairQuotient.
Check Pairs.PairQuotient_obligation_1.
Check Pairs.PairQuotient_obligation_2.
Check Pairs.PairQuotient_obligation_3.
Check PairTop.
Check PointPair.
Check Pairs.PointPair_obligation_1.
Check Pairs.PointPair_obligation_2.
Check Pairs.PointPair_obligation_3.
Check PointPair_sub.
Check Top_pairs.
Check Pairs.Top_pairs_obligation_1.
Check Pairs.Top_pairs_obligation_2.
Check Pairs.Top_pairs_obligation_3.
Check Pairs.Top_pairs_obligation_4.
Check collapse_colimit_point.
Check collapse_pointed.
Check empty_colimit_not_elementary.
Check empty_pair.
Check no_pointed_coequalizer_at_empty.
Check no_pointed_elementary_coequalizers.
Check pair_carries.
Check pair_compose.
Check pair_compose_respects.
Check pair_id.
Check pair_map.
Check pair_space.
Check pair_sub.
Check pair_sub_equiv_Equivalence.
Check pair_sub_incl.
Check pair_sub_incl_map.
Check pair_sub_proper.
Check pair_sub_setoid.
Check pair_sub_space.
Check pairs_quotient_adj_is.
Check pairs_quotient_adjunction.
Check pairs_quotient_counit_none.
Check pairs_quotient_counit_some.
Check pairs_quotient_iso.
Check Pairs.pairs_quotient_iso_obligation_1.
Check Pairs.pairs_quotient_iso_obligation_2.
Check Pairs.pairs_quotient_iso_obligation_3.
Check Pairs.pairs_quotient_iso_obligation_4.
Check pairs_quotient_unit_eval.
Check point_pair.
Check point_pair_map.
Check pquot_base.
Check pquot_basepoint.
Check pquot_carrier.
Check pquot_coequalizer.
Check pquot_coequalizer_needs_point.
Check pquot_collapse_iso.
Check pquot_collapse_iso_from_none.
Check pquot_collapse_iso_from_some.
Check pquot_collapse_iso_pointed.
Check pquot_collapse_iso_to.
Check pquot_empty_new_point.
Check pquot_empty_not_coequalizer.
Check pquot_empty_sum_from.
Check pquot_empty_sum_iso.
Check pquot_empty_sum_iso_none.
Check pquot_empty_sum_iso_some.
Check pquot_empty_sum_to.
Check pquot_fmap.
Check pquot_fmap_cont.
Check pquot_fmap_map.
Check pquot_from.
Check pquot_from_eval_none.
Check pquot_from_eval_some.
Check pquot_from_map.
Check pquot_in.
Check pquot_po_map.
Check pquot_po_med.
Check pquot_pointed.
Check pquot_pushout.
Check pquot_pushout_apex.
Check pquot_rel.
Check pquot_rel_Equivalence.
Check pquot_setoid.
Check pquot_some.
Check pquot_space.
Check pquot_space_carrier.
Check pquot_space_open.
Check pquot_to.
Check pquot_to_eval.
Check pquot_wide_cocone.
Check pquot_wide_coequalizer_colimit.
Check pquot_wide_coequalizer_colimit_apex.
Check pquot_wide_coequalizer_colimit_base.
Check pquot_wide_coequalizer_colimit_empty.
Check pquot_wide_coequalizer_colimit_in.
Check pquot_wide_coequalizer_colimit_quotient.
Check pquot_wide_legs.
Check pquot_wide_legs_coherence.
Check pquot_wide_ump.
