(*
   本文件为测试：ProbeComponents462。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyReals.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyRealsMult.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyAbs.
Require Import Coq.Reals.Cauchy.ConstructiveRcomplete.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Adjunction.Continuity.Equalizer.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Subcategory.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Instance.Top.Separation.
Require Category.Theory.Concrete.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.Components.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Circle.
Require Import Category.Instance.Top.Components.Paths.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Functor.Hom.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

Open Scope category_scope.

(** ** Instrument: the refutation keyword is live *)

(* The instrument *)
Fail Check p462_absent_name.

(** ** Instance/Top/Components.v, ENCODING: the Type-valued [Top] *)

(* CONTROL: a functor out of [Top@{h o}] into the [Sets] one universe up,
   and an [Adjunction] record between them. *)
Definition p462_top_to_sets_up@{h o so +} (C : Top@{h o} ⟶ Sets@{h so}) :
  True := I.

Definition p462_top_adj_up@{h o so +} (C : Top@{h o} ⟶ Sets@{h so})
  (D : Sets@{h so} ⟶ Top@{h o}) (A : C ⊣ D) : True := I.

(* N1 *)
Fail Definition p462_top_to_sets@{h o so +}
  (C : Top@{h o} ⟶ Sets@{o so}) : True := I.

(* N2 *)
Fail Definition p462_top_adj_discrete@{h o so +}
  (C : Top@{h o} ⟶ Sets@{h so}) (A : C ⊣ Top_Discrete) : True := I.

(* CONTROL: the component relation over [Top], Prop-valued, is formable
   under the closed universe list of the points' universe alone. *)
Definition p462_tconnsub@{o} (X : TopSpace@{o}) (W : X → Prop) : Prop :=
  ∀ φ : X → Prop,
    (∀ z, W z → ex (fun O : X → Type@{o} =>
        inhabited (IsOpen X O) /\ inhabited (O z) /\
        ∀ w, W w → inhabited (O w) → (φ w <-> φ z))) →
    ∀ a b, W a → W b → φ a → φ b.

Definition tcomp_rel_prop@{o} (X : TopSpace@{o}) (x y : X) : Prop :=
  ex (fun W : X → Prop => p462_tconnsub X W /\ W x /\ W y).

(* CONTROL: the Type-valued forms, one universe up. *)
Definition p462_tcomp_rel_sigma_up@{o h | o < h +} (X : TopSpace@{o})
  (x y : X) : Type@{h} :=
  { W : X → Type@{o} & (W x * W y)%type }.

Definition p462_tcomp_rel_forall_up@{o h | o < h +} (X : TopSpace@{o})
  (x y : X) : Type@{h} :=
  ∀ U : X → Type@{o}, IsOpen X U → U x → U y.

Definition p462_tconnected_up@{o h | o < h +} (X : TopSpace@{o})
  (W : X → Type@{o}) : Type@{h} :=
  ∀ (S : SetoidObject@{o o}) (g : X → S), ∀ a b, W a → W b → g a ≈ g b.

(* N3 *)
Fail Definition p462_tcomp_rel_sigma@{o} (X : TopSpace@{o}) (x y : X) :
  Type@{o} :=
  { W : X → Type@{o} & (W x * W y)%type }.

(* N4 *)
Fail Definition p462_tcomp_rel_forall@{o} (X : TopSpace@{o}) (x y : X) :
  Type@{o} :=
  ∀ U : X → Type@{o}, IsOpen X U → U x → U y.

(* N5 *)
Fail Definition p462_tconnected@{o} (X : TopSpace@{o}) (W : X → Type@{o}) :
  Type@{o} :=
  ∀ (S : SetoidObject@{o o}) (g : X → S), ∀ a b, W a → W b → g a ≈ g b.

(** ** Instance/Top/Components.v, MAC LANE'S SET: the propositional sets *)

(* N6 *)
Fail Definition p462_comp_rel_witness@{o} (X : PTop@{o}) (x y : X)
  (H : comp_rel X x y) :
  { W : X → Prop & (PConnectedSub X W * W x * W y)%type } :=
  match H with ex_intro _ W (conj HW (conj wx wy)) => existT _ W (HW, wx, wy)
  end.

(* N7 *)
Fail Definition p462_transpose_inh@{o} (X : PTop@{o})
  (S : SetoidObject@{o o}) (g : PMor@{o} X (PDiscrete S)) (x y : X)
  (HR : inhabited (pmap g x ≈ pmap g y)) : pmap g x ≈ pmap g y :=
  match HR with inhabits h => h end.

(* CONTROL: through a [PropEquiv] of the target the truncation is
   eliminated, and the transposition respects components. *)
Definition p462_transpose_pe@{o} (X : PTop@{o}) (S : SetoidObject@{o o})
  (P : PropEquiv@{o o} (is_setoid S)) (g : PMor@{o} X (PDiscrete S))
  (x y : X) (HR : inhabited (pmap g x ≈ pmap g y)) : pmap g x ≈ pmap g y :=
  @pequiv_elim_inhabited _ _ P _ _ HR.

Definition p462_comp_respect@{o} (X : PTop@{o}) (S : SetoidObject@{o o})
  (P : PropEquiv@{o o} (is_setoid S)) (g : PMor@{o} X (PDiscrete S))
  (x y : X) : comp_rel X x y → pmap g x ≈ pmap g y := comp_respect X S P g x y.

(* CONTROL: into all of [Sets], an adjunction makes [Untruncate] merely
   true, and [Untruncate] gives one. *)
Definition p462_unsquash@{o so ua ub | o < so, o < ua +}
  (C' : Lconn@{o so} ⟶ Sets@{o so})
  (A : @Adjunction@{so o o so o o o o ua o ub} Sets@{o so} Lconn@{o so}
         C' LDisc@{o so}) : inhabited Untruncate@{o} :=
  components_on_all_Sets_Untruncate C' A.

Definition p462_unsquash_principle@{o so ua ub | o < so, o < ua +}
  (C' : Lconn@{o so} ⟶ Sets@{o so})
  (A : @Adjunction@{so o o so o o o o ua o ub} Sets@{o so} Lconn@{o so}
         C' LDisc@{o so}) : inhabited (∀ Q : Type@{o}, inhabited Q → Q) :=
  components_on_all_Sets_unsquashes C' A.

Definition p462_adj_Sets@{o so | o < so +} (U : Untruncate@{o}) :
  components_functor_Sets@{o so} ⊣ LDisc@{o so} :=
  components_left_adjoint_discrete_Sets U.

(* CONTROL: [PSetsSub]'s object predicate placed at the points' universe
   is formable, with [Set < o] in its block; at the pin, at [so]. *)
Definition p462_psets_sub_at_o@{o so | o < so +} :
  Subcategory@{so o o o} Sets@{o so} :=
  @Build_Subcategory@{so o o o} Sets@{o so}
    (fun S : SetoidObject@{o o} => PropEquivObj S)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition p462_psets_sub_Set@{so | Set < so +} := PSetsSub@{Set so}.

(* N8 *)
Fail Definition p462_psets_sub_o_Set@{so | Set < so +} :=
  p462_psets_sub_at_o@{Set so}.

(** ** Adjunction/Continuity/Equalizer.v: why the proof is direct *)

Section Pair.

Context {C D : Category} (U : C ⟶ D) {x y : C} (f g : x ~> y).

(* CONTROL: the two diagrams agree on objects, at [eq_refl]. *)
Example p462_pair_obj_X :
  fobj[U ◯ APair f g] ParX = fobj[APair (fmap[U] f) (fmap[U] g)] ParX
  := eq_refl.

Example p462_pair_obj_Y :
  fobj[U ◯ APair f g] ParY = fobj[APair (fmap[U] f) (fmap[U] g)] ParY
  := eq_refl.

(* N9 *)
Fail Example p462_pair : U ◯ APair f g = APair (fmap[U] f) (fmap[U] g)
  := eq_refl.

End Pair.

(* CONTROL: right adjoints preserve equalizers, and the refutation. *)
Definition p462_rapl_equalizers@{co do h +} {C : Category@{co h h}}
  {D : Category@{do h h}} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) :
  PreservesEqualizers U := right_adjoint_PreservesEqualizers A.

(** ** Instance/Top/Components.v: the adjunction, at [eq_refl] *)

(* CONTROL: both transposes and the unit are the identity on points. *)
Example p462_to_points@{o so | o < so +} (X : Lconn@{o so})
  (S : PSets@{o so}) (h : components_functor@{o so} X ~{PSets@{o so}}~> S)
  (x : pt_carrier (`1 X)) :
  pmap (`1 (to (@adj _ _ _ _ components_left_adjoint_discrete@{o so} X S) h))
    x = `1 h x := eq_refl.

Example p462_from_points@{o so | o < so +} (X : Lconn@{o so})
  (S : PSets@{o so}) (g : X ~{Lconn@{o so}}~> PSetsDisc@{o so} S)
  (x : pt_carrier (`1 X)) :
  `1 (from (@adj _ _ _ _ components_left_adjoint_discrete@{o so} X S) g) x
    = pmap (`1 g) x := eq_refl.

Example p462_unit_points@{o so | o < so +} (X : Lconn@{o so})
  (x : pt_carrier (`1 X)) :
  pmap (`1 (@unit _ _ _ _ components_left_adjoint_discrete@{o so} X)) x = x
  := eq_refl.

Example p462_Sets_to_points@{o so | o < so +} (U : Untruncate@{o})
  (X : Lconn@{o so}) (S : Sets@{o so})
  (h : components_functor_Sets@{o so} X ~{Sets@{o so}}~> S)
  (x : pt_carrier (`1 X)) :
  pmap (`1 (to (@adj _ _ _ _
                 (components_left_adjoint_discrete_Sets@{o so} U) X S) h)) x
    = h x := eq_refl.

Example p462_Sets_from_points@{o so | o < so +} (U : Untruncate@{o})
  (X : Lconn@{o so}) (S : Sets@{o so})
  (g : X ~{Lconn@{o so}}~> LDisc@{o so} S) (x : pt_carrier (`1 X)) :
  from (@adj _ _ _ _ (components_left_adjoint_discrete_Sets@{o so} U) X S)
    g x = pmap (`1 g) x := eq_refl.

(* CONTROL: D is [PDisc] on objects and arrows, and C is [comp_rel]. *)
Example p462_LDisc_obj@{o so | o < so +} (S : Sets@{o so}) :
  `1 (fobj[LDisc@{o so}] S) = fobj[PDisc@{o so}] S := eq_refl.

Example p462_components_equiv@{o so | o < so +} (X : Lconn@{o so})
  (x y : pt_carrier (`1 X)) :
  @equiv _ (is_setoid (`1 (fobj[components_functor@{o so}] X))) x y
    = comp_rel (`1 X) x y := eq_refl.

(** ** Instance/Top/Components.v: the concrete equalizer, and the
    non-existence statements *)

(* CONTROL: the fork on the three-point space is an equalizer in [Lconn],
   and C does not preserve it. *)
Definition p462_zig_equalizer@{o so | o < so +} :
  @IsEqualizer Lconn@{o so} LZig@{o so} LTwoIndisc@{o so}
    zig_f@{o so} zig_g@{o so} LBool@{o so} zig_e@{o so} :=
  Lconn_zig_equalizer.

Definition p462_zig_not_preserved@{o so | o < so +} :
  @IsEqualizer PSets@{o so} _ _
    (fmap[components_functor@{o so}] zig_f@{o so})
    (fmap[components_functor@{o so}] zig_g@{o so})
    (components_functor@{o so} LBool@{o so})
    (fmap[components_functor@{o so}] zig_e@{o so}) → False :=
  components_zig_not_preserved.

(* CONTROL: the refutations, restated. *)
Definition p462_no_left_adjoint@{o so u u0 | o < so, o < u +}
  (L : PSets@{o so} ⟶ Lconn@{o so})
  (B : @Adjunction@{so o o so o o o o u o u0} Lconn@{o so} PSets@{o so}
         L components_functor@{o so}) : False :=
  components_no_left_adjoint L B.

Definition p462_any_left_adjoint@{o so ua ub u u0 +| o < so, o < ua,
    o < ub +}
  (C : Lconn@{o so} ⟶ PSets@{o so})
  (A : @Adjunction@{so o o so o o o o ua o u} PSets@{o so} Lconn@{o so}
         C PSetsDisc@{o so})
  (L : PSets@{o so} ⟶ Lconn@{o so})
  (B : @Adjunction@{so o o so o o o o ub o u0} Lconn@{o so} PSets@{o so}
         L C) : False :=
  discrete_left_adjoint_no_left_adjoint C A L B.

Definition p462_no_left_on_PTop@{o so u u0 | o < so, o < u +}
  (C' : PTopCat@{o so} ⟶ PSets@{o so})
  (A : @Adjunction@{so o o so o o o o u o u0} PSets@{o so} PTopCat@{o so}
         C' PSetsDiscTop@{o so}) : False :=
  discrete_no_left_adjoint_on_PTop C' A.

Definition p462_PDisc_no_left@{o so u u0 | o < so, o < u +}
  (C' : PTopCat@{o so} ⟶ Sets@{o so})
  (A : @Adjunction@{so o o so o o o o u o u0} Sets@{o so} PTopCat@{o so}
         C' PDisc@{o so}) : False :=
  PDisc_no_left_adjoint C' A.

(* CONTROL: the points may be in [Set]: the ten theorems at [o := Set]. *)
Definition p462_adj_at_Set@{so | Set < so +} :=
  components_left_adjoint_discrete@{Set so}.

Definition p462_adj_Sets_at_Set@{so | Set < so +} :=
  components_left_adjoint_discrete_Sets@{Set so}.

Definition p462_no_left_at_Set@{so u u0 | Set < so, Set < u +} :=
  components_no_left_adjoint@{Set so u u0}.

Definition p462_any_left_at_Set@{so ua ub u u0 | Set < so, Set < ua,
    Set < ub +} :=
  discrete_left_adjoint_no_left_adjoint@{Set so ua ub u u0}.

Definition p462_unsquash_principle_at_Set@{so u u0 | Set < so,
    Set < u +} :=
  components_on_all_Sets_unsquashes@{Set so u u0}.

Definition p462_unsquash_at_Set@{so u u0 | Set < so, Set < u +} :=
  components_on_all_Sets_Untruncate@{Set so u u0}.

Definition p462_ptop_at_Set@{so u u0 | Set < so, Set < u +} :=
  discrete_no_left_adjoint_on_PTop@{Set so u u0}.

Definition p462_pdisc_at_Set@{so u u0 | Set < so, Set < u +} :=
  PDisc_no_left_adjoint@{Set so u u0}.

Definition p462_zig_at_Set@{so | Set < so +} :=
  components_zig_not_preserved@{Set so}.

Definition p462_swap_at_Set@{so | Set < so +} :=
  components_swap_not_preserved@{Set so}.

(** ** Instance/Top/Components/Paths.v: π₀ = colim ∘ P *)

(* CONTROL: the arrow part of π₀ IS the colimit functor's, and on
   representatives it is postcomposition. *)
Example p462_pi0_fmap@{o so p f | o < so, p <= o, o < f +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) :
  fmap[PPi0@{o so p f}] h
    = Colim_map PathColim@{o so p} (PPathPair_map@{o so p} h) := eq_refl.

Example p462_pi0_fmap_point@{o so p f | o < so, p <= o, o < f +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) (x : PMor@{o} PPoint@{o} X) :
  fmap[PPi0@{o so p f}] h (existT _ ParY x) = existT _ ParY (pcompose h x)
  := eq_refl.

(* CONTROL: the identity law, up to [≈], and the underlying functions,
   at [eq_refl]. *)
Definition p462_pi0_id@{o so p f | o < so, p <= o, o < f +} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) :
  fmap[PPi0@{o so p f}] (pid X) (existT _ ParY x) ≈ existT _ ParY x :=
  @fmap_id _ _ PPi0@{o so p f} X (existT _ ParY x).

Example p462_id_fun@{o} (X : PTop@{o}) (x : PMor@{o} PPoint@{o} X) :
  (fun u => pmap (pcompose (pid X) x) u) = (fun u => pmap x u) := eq_refl.

(* N10 *)
Example p462_pi0_id_point@{o so p f | o < so, p <= o, o < f +}
  (X : PTop@{o}) (x : PMor@{o} PPoint@{o} X) :
  fmap[PPi0@{o so p f}] (pid X) (existT _ ParY x) = existT _ ParY x
  := eq_refl.

(* N11 *)
Example p462_id_setoid_map@{o} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) : pmap (pcompose (pid X) x) = pmap x
  := eq_refl.

(* CONTROL: the endpoint pair as a diagram in [PTopCat^op], and the
   Yoneda embedding of [PTopCat]. *)
Definition p462_iota@{o so +| o < so +} : Parallel ⟶ PTopCat@{o so}^op :=
  @APair (PTopCat@{o so}^op) PInterval@{o} PPoint@{o}
    ival_end0@{o} ival_end1@{o}.

Definition p462_yoneda@{o so +| o < so +} := Curried_CoHom PTopCat@{o so}.

(* N12 *)
Fail Definition p462_P_derived@{o so +| o < so +} :=
  Induced p462_iota ◯ Curried_CoHom PTopCat@{o so}.

(* CONTROL: the interval is connected in Instance/Top/Components.v's
   two-point form; π₀ of the interval and of [PBool]. *)
Definition p462_interval_connected@{o} : PConnectedBool PInterval@{o} :=
  interval_PConnectedBool.

Definition p462_pi0_interval@{o so p f | o < so, p <= o, o < f +} :
  fobj[PPi0@{o so p f}] PInterval@{o} ≅[Sets@{o so}] unit_setoid_object@{o o}
  := PPi0_PInterval_iso.

Definition p462_pi0_bool@{o so p f | o < so, p <= o, o < f +} :
  fobj[PPi0@{o so p f}] PBool@{o} ≅[Sets@{o so}] bool_setoid_object@{o o}
  := PPi0_PBool_iso.

(** ** Closure: a readback, not a refutation *)

Print Assumptions right_adjoint_PreservesEqualizers.
Print Assumptions components_functor.
Print Assumptions components_left_adjoint_discrete.
Print Assumptions components_no_left_adjoint.
Print Assumptions components_left_adjoint_discrete_Sets.
Print Assumptions PPi0.

(** ** Guard: the constants of the three targets *)

(* Adjunction/Continuity/Equalizer.v: 2 names. *)
Check Category.Adjunction.Continuity.Equalizer.not_PreservesEqualizers_no_left_adjoint.
Check Category.Adjunction.Continuity.Equalizer.right_adjoint_PreservesEqualizers.

(* Instance/Top/Components.v: 125 names and the constructors of [zig_pt].
   CORRECTION (#1349): 121 names now; the squash setoid's four follow the
   group, by their new names. *)
Check Category.Instance.Top.Components.adj_from_points.
Check Category.Instance.Top.Components.adj_Sets_from_points.
Check Category.Instance.Top.Components.adj_Sets_to_points.
Check Category.Instance.Top.Components.adj_to_points.
Check Category.Instance.Top.Components.comp_adj_iso.
Check Category.Instance.Top.Components.comp_adj_iso_obligation_1.
Check Category.Instance.Top.Components.comp_adj_iso_obligation_2.
Check Category.Instance.Top.Components.comp_adj_iso_obligation_3.
Check Category.Instance.Top.Components.comp_adj_iso_obligation_4.
Check Category.Instance.Top.Components.comp_adj_iso_U.
Check Category.Instance.Top.Components.comp_adj_iso_U_obligation_1.
Check Category.Instance.Top.Components.comp_adj_iso_U_obligation_2.
Check Category.Instance.Top.Components.comp_adj_iso_U_obligation_3.
Check Category.Instance.Top.Components.comp_adj_iso_U_obligation_4.
Check Category.Instance.Top.Components.comp_cont.
Check Category.Instance.Top.Components.comp_PropEquiv.
Check Category.Instance.Top.Components.comp_rel.
Check Category.Instance.Top.Components.comp_rel_map.
Check Category.Instance.Top.Components.comp_rel_of_equiv.
Check Category.Instance.Top.Components.comp_rel_sym.
Check Category.Instance.Top.Components.comp_rel_trans.
Check Category.Instance.Top.Components.comp_respect.
Check Category.Instance.Top.Components.comp_respect_U.
Check Category.Instance.Top.Components.comp_setoid_map.
Check Category.Instance.Top.Components.components_equiv.
Check Category.Instance.Top.Components.components_fmap.
Check Category.Instance.Top.Components.components_functor.
Check Category.Instance.Top.Components.components_functor_Sets.
Check Category.Instance.Top.Components.components_left_adjoint_discrete.
Check Category.Instance.Top.Components.components_left_adjoint_discrete_Sets.
Check Category.Instance.Top.Components.components_no_left_adjoint.
Check Category.Instance.Top.Components.components_obj.
Check Category.Instance.Top.Components.components_on_all_Sets_unsquashes.
Check Category.Instance.Top.Components.components_on_all_Sets_Untruncate.
Check Category.Instance.Top.Components.components_swap_not_preserved.
Check Category.Instance.Top.Components.components_unit_points.
Check Category.Instance.Top.Components.components_zig_not_preserved.
Check Category.Instance.Top.Components.CompSet.
Check Category.Instance.Top.Components.CompSetoid.
Check Category.Instance.Top.Components.CompTop.
Check Category.Instance.Top.Components.CompTop_obligation_1.
Check Category.Instance.Top.Components.CompTop_obligation_2.
Check Category.Instance.Top.Components.CompTop_obligation_3.
Check Category.Instance.Top.Components.connected_bool_constant.
Check Category.Instance.Top.Components.connected_no_separation.
Check Category.Instance.Top.Components.discrete_left_adjoint_no_left_adjoint.
Check Category.Instance.Top.Components.discrete_left_adjoint_not_preserved.
Check Category.Instance.Top.Components.discrete_no_left_adjoint_on_PTop.
Check Category.Instance.Top.Components.empty_set_map.
Check Category.Instance.Top.Components.image_connected.
Check Category.Instance.Top.Components.LBool.
Check Category.Instance.Top.Components.Lconn.
Check Category.Instance.Top.Components.Lconn_Sub.
Check Category.Instance.Top.Components.Lconn_swap_equalizer.
Check Category.Instance.Top.Components.Lconn_zig_equalizer.
Check Category.Instance.Top.Components.LDisc.
Check Category.Instance.Top.Components.LDisc_obligation_1.
Check Category.Instance.Top.Components.LDisc_obligation_2.
Check Category.Instance.Top.Components.LDisc_obligation_3.
Check Category.Instance.Top.Components.LDisc_PDisc_fmap.
Check Category.Instance.Top.Components.LDisc_PDisc_obj.
Check Category.Instance.Top.Components.LEmpty.
Check Category.Instance.Top.Components.locconst_restrict.
Check Category.Instance.Top.Components.LocConstOn.
Check Category.Instance.Top.Components.LTwoIndisc.
Check Category.Instance.Top.Components.LZig.
Check Category.Instance.Top.Components.negb_no_fixpoint.
Check Category.Instance.Top.Components.pbool_two_components.
Check Category.Instance.Top.Components.PConnected.
Check Category.Instance.Top.Components.PConnected_Bool.
Check Category.Instance.Top.Components.PConnected_Sep.
Check Category.Instance.Top.Components.PConnectedBool.
Check Category.Instance.Top.Components.PConnectedSep.
Check Category.Instance.Top.Components.PConnectedSub.
Check Category.Instance.Top.Components.pconv_not_locconn.
Check Category.Instance.Top.Components.pdisc_locconn.
Check Category.Instance.Top.Components.PDisc_no_left_adjoint.
Check Category.Instance.Top.Components.PLocConn.
Check Category.Instance.Top.Components.point_connected.
Check Category.Instance.Top.Components.PSets.
Check Category.Instance.Top.Components.PSetsDisc.
Check Category.Instance.Top.Components.PSetsDisc_obj.
Check Category.Instance.Top.Components.PSetsDiscTop.
Check Category.Instance.Top.Components.PSetsOne.
Check Category.Instance.Top.Components.PSetsSub.
Check Category.Instance.Top.Components.PTop_zig_equalizer.
Check Category.Instance.Top.Components.PTwoIndisc_connected.
Check Category.Instance.Top.Components.PTwoIndisc_PLocConn.
Check Category.Instance.Top.Components.PZig.
Check Category.Instance.Top.Components.PZig_connected.
Check Category.Instance.Top.Components.PZig_one_component.
Check Category.Instance.Top.Components.PZig_PLocConn.
Check Category.Instance.Top.Components.squash_id.
Check Category.Instance.Top.Components.squash_id_cont.
Check Category.Instance.Top.Components.swap_e.
Check Category.Instance.Top.Components.swap_L.
Check Category.Instance.Top.Components.swap_map.
Check Category.Instance.Top.Components.swap_set.
Check Category.Instance.Top.Components.union_connected.
Check Category.Instance.Top.Components.unsquash_choice.
Check Category.Instance.Top.Components.unsquash_Untruncate.
Check Category.Instance.Top.Components.Untruncate_unsquash.
Check Category.Instance.Top.Components.zig_a.
Check Category.Instance.Top.Components.zig_b.
Check Category.Instance.Top.Components.zig_c.
Check Category.Instance.Top.Components.zig_e.
Check Category.Instance.Top.Components.zig_e_fun.
Check Category.Instance.Top.Components.zig_e_map.
Check Category.Instance.Top.Components.zig_e_set.
Check Category.Instance.Top.Components.zig_f.
Check Category.Instance.Top.Components.zig_f_map.
Check Category.Instance.Top.Components.zig_f_set.
Check Category.Instance.Top.Components.zig_g.
Check Category.Instance.Top.Components.zig_g_fun.
Check Category.Instance.Top.Components.zig_g_map.
Check Category.Instance.Top.Components.zig_g_set.
Check Category.Instance.Top.Components.zig_lift_fun.
Check Category.Instance.Top.Components.zig_open.
Check Category.Instance.Top.Components.zig_pt.
Check Category.Instance.Top.Components.zig_pt_ind.
Check Category.Instance.Top.Components.zig_pt_rec.
Check Category.Instance.Top.Components.zig_pt_rect.
Check Category.Instance.Top.Components.zig_pt_sind.
Check Category.Instance.Top.Components.zig_setoid.

(* Instance/Sets/Propositional/Full.v: the squash setoid's 4 names, moved
   there from Instance/Top/Components.v by #1349. *)
Check Category.Instance.Sets.Propositional.Full.squash_rel.
Check Category.Instance.Sets.Propositional.Full.squash_sym.
Check Category.Instance.Sets.Propositional.Full.squash_trans.
Check Category.Instance.Sets.Propositional.Full.SquashSetoid.

(* Instance/Top/Components/Paths.v: 126 names. *)
Check Category.Instance.Top.Components.Paths.ibis_clamp.
Check Category.Instance.Top.Components.Paths.ibis_clamp_hi.
Check Category.Instance.Top.Components.Paths.ibis_clamp_id.
Check Category.Instance.Top.Components.Paths.ibis_clamp_ival.
Check Category.Instance.Top.Components.Paths.ibis_clamp_lo.
Check Category.Instance.Top.Components.Paths.ibis_contra.
Check Category.Instance.Top.Components.Paths.ibis_cv_ge.
Check Category.Instance.Top.Components.Paths.ibis_cv_le.
Check Category.Instance.Top.Components.Paths.ibis_inv.
Check Category.Instance.Top.Components.Paths.ibis_left_close.
Check Category.Instance.Top.Components.Paths.ibis_lim.
Check Category.Instance.Top.Components.Paths.ibis_lim_cv.
Check Category.Instance.Top.Components.Paths.ibis_lim_ival.
Check Category.Instance.Top.Components.Paths.ibis_lim_pt.
Check Category.Instance.Top.Components.Paths.ibis_nest.
Check Category.Instance.Top.Components.Paths.ibis_pt.
Check Category.Instance.Top.Components.Paths.ibis_q_pos_inv.
Check Category.Instance.Top.Components.Paths.ibis_right_in.
Check Category.Instance.Top.Components.Paths.ibis_seq.
Check Category.Instance.Top.Components.Paths.ibis_seq_cauchy.
Check Category.Instance.Top.Components.Paths.ibis_seq_in.
Check Category.Instance.Top.Components.Paths.ibis_stage.
Check Category.Instance.Top.Components.Paths.ibis_step.
Check Category.Instance.Top.Components.Paths.ibis_val.
Check Category.Instance.Top.Components.Paths.ibis_val_proper.
Check Category.Instance.Top.Components.Paths.ibis_width.
Check Category.Instance.Top.Components.Paths.ibis_width_bound.
Check Category.Instance.Top.Components.Paths.ibis_width_mono.
Check Category.Instance.Top.Components.Paths.ibis_width_pos.
Check Category.Instance.Top.Components.Paths.ibis_width_small.
Check Category.Instance.Top.Components.Paths.interval_bool_constant.
Check Category.Instance.Top.Components.Paths.interval_bool_endpoints.
Check Category.Instance.Top.Components.Paths.interval_PConnectedBool.
Check Category.Instance.Top.Components.Paths.ival_abs_le.
Check Category.Instance.Top.Components.Paths.ival_end0.
Check Category.Instance.Top.Components.Paths.ival_end1.
Check Category.Instance.Top.Components.Paths.ival_incl.
Check Category.Instance.Top.Components.Paths.ival_incl_obligation_1.
Check Category.Instance.Top.Components.Paths.ival_mult_pred.
Check Category.Instance.Top.Components.Paths.ival_one.
Check Category.Instance.Top.Components.Paths.ival_pred.
Check Category.Instance.Top.Components.Paths.ival_pred_0.
Check Category.Instance.Top.Components.Paths.ival_pred_1.
Check Category.Instance.Top.Components.Paths.ival_scale_map.
Check Category.Instance.Top.Components.Paths.ival_scale_map_obligation_1.
Check Category.Instance.Top.Components.Paths.ival_segment.
Check Category.Instance.Top.Components.Paths.ival_segment_0.
Check Category.Instance.Top.Components.Paths.ival_segment_1.
Check Category.Instance.Top.Components.Paths.ival_segment_map.
Check Category.Instance.Top.Components.Paths.ival_zero.
Check Category.Instance.Top.Components.Paths.IvalSetoid.
Check Category.Instance.Top.Components.Paths.IvalSetoid_obligation_1.
Check Category.Instance.Top.Components.Paths.line_scale.
Check Category.Instance.Top.Components.Paths.line_scale_obligation_1.
Check Category.Instance.Top.Components.Paths.ParSets.
Check Category.Instance.Top.Components.Paths.path_at.
Check Category.Instance.Top.Components.Paths.path_at_obligation_1.
Check Category.Instance.Top.Components.Paths.PathColim.
Check Category.Instance.Top.Components.Paths.pbool_at_point.
Check Category.Instance.Top.Components.Paths.pbool_at_point_obligation_1.
Check Category.Instance.Top.Components.Paths.pbool_at_zero.
Check Category.Instance.Top.Components.Paths.pbool_at_zero_obligation_1.
Check Category.Instance.Top.Components.Paths.PHomSetoid.
Check Category.Instance.Top.Components.Paths.pi0_bool_cocone.
Check Category.Instance.Top.Components.Paths.Pi0_PBool_two.
Check Category.Instance.Top.Components.Paths.PInterval.
Check Category.Instance.Top.Components.Paths.pinterval_point_rel.
Check Category.Instance.Top.Components.Paths.pinterval_rel.
Check Category.Instance.Top.Components.Paths.pline_scale.
Check Category.Instance.Top.Components.Paths.pline_scale_cont.
Check Category.Instance.Top.Components.Paths.PPathPair.
Check Category.Instance.Top.Components.Paths.PPathPair_ev0.
Check Category.Instance.Top.Components.Paths.PPathPair_ev1.
Check Category.Instance.Top.Components.Paths.PPathPair_fmap_paths.
Check Category.Instance.Top.Components.Paths.PPathPair_map.
Check Category.Instance.Top.Components.Paths.PPathPair_map_obligation_1.
Check Category.Instance.Top.Components.Paths.PPathPair_map_obligation_2.
Check Category.Instance.Top.Components.Paths.PPathPair_obj.
Check Category.Instance.Top.Components.Paths.PPathPair_obligation_1.
Check Category.Instance.Top.Components.Paths.PPathPair_obligation_2.
Check Category.Instance.Top.Components.Paths.PPathPair_obligation_3.
Check Category.Instance.Top.Components.Paths.PPathPair_paths.
Check Category.Instance.Top.Components.Paths.PPathPair_points.
Check Category.Instance.Top.Components.Paths.PPi0.
Check Category.Instance.Top.Components.Paths.PPi0_carrier.
Check Category.Instance.Top.Components.Paths.PPi0_coeq_iso.
Check Category.Instance.Top.Components.Paths.PPi0_coeq_iso_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_coeq_iso_obligation_2.
Check Category.Instance.Top.Components.Paths.PPi0_equiv.
Check Category.Instance.Top.Components.Paths.PPi0_fmap.
Check Category.Instance.Top.Components.Paths.PPi0_fmap_path.
Check Category.Instance.Top.Components.Paths.PPi0_fmap_point.
Check Category.Instance.Top.Components.Paths.PPi0_fobj.
Check Category.Instance.Top.Components.Paths.ppi0_from_coeq.
Check Category.Instance.Top.Components.Paths.ppi0_from_coeq_obligation_1.
Check Category.Instance.Top.Components.Paths.ppi0_from_coeq_point.
Check Category.Instance.Top.Components.Paths.ppi0_from_points.
Check Category.Instance.Top.Components.Paths.ppi0_from_points_at.
Check Category.Instance.Top.Components.Paths.ppi0_from_points_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_inj_point.
Check Category.Instance.Top.Components.Paths.PPi0_PBool_iso.
Check Category.Instance.Top.Components.Paths.PPi0_PBool_iso_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_PBool_iso_obligation_2.
Check Category.Instance.Top.Components.Paths.PPi0_PBool_iso_obligation_3.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso_obligation_2.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso_obligation_3.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso_obligation_4.
Check Category.Instance.Top.Components.Paths.PPi0_points_iso.
Check Category.Instance.Top.Components.Paths.PPi0_points_iso_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_points_iso_obligation_2.
Check Category.Instance.Top.Components.Paths.ppi0_to_coeq.
Check Category.Instance.Top.Components.Paths.ppi0_to_coeq_path.
Check Category.Instance.Top.Components.Paths.ppi0_to_coeq_point.
Check Category.Instance.Top.Components.Paths.ppi0_to_points.
Check Category.Instance.Top.Components.Paths.ppi0_to_points_fun.
Check Category.Instance.Top.Components.Paths.ppi0_to_points_obligation_1.
Check Category.Instance.Top.Components.Paths.ppi0_to_points_point.
Check Category.Instance.Top.Components.Paths.ppi0_to_points_respects.
Check Category.Instance.Top.Components.Paths.ppoint_at.
Check Category.Instance.Top.Components.Paths.ppostcomp.
Check Category.Instance.Top.Components.Paths.ppostcomp_obligation_1.
Check Category.Instance.Top.Components.Paths.pprecomp.
Check Category.Instance.Top.Components.Paths.pprecomp_obligation_1.
Check Category.Instance.Top.Components.Paths.rball_scale.

(*
   本节说明 ProbeComponents462 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Category.Instance.Sets.Propositional.Full.

Example p462_c469_propsets_sub@{o so | o < so +} :
  PropSets_sub@{o so} = PSetsSub@{o so} := eq_refl.

Example p462_c469_propsets@{o so | o < so +} :
  PropSets@{o so} = PSets@{o so} := eq_refl.
