Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
   本文件给出自由构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(*
   nLab:      https://ncatlab.org/nlab/show/free+module
   nLab:      https://ncatlab.org/nlab/show/free+object
   nLab:      https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Free_module
   Wikipedia: https://en.wikipedia.org/wiki/Basis_(linear_algebra)
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   Book: Mac Lane, ibid., §IV.1, printed p. 79 (the same content in
   Book: Riehl, Category Theory in Context, §4.0, printed p. 131 (k[S],

   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Formal linear combinations and the module quotient *)

Section FreeModule.

Context (R : RingObject).
Context (X : SetoidObject).

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive FVTerm : Type :=
  | fv_gen  : carrier X → FVTerm
  | fv_zero : FVTerm
  | fv_plus : FVTerm → FVTerm → FVTerm
  | fv_neg  : FVTerm → FVTerm
  | fv_smul : carrier (rig_setoid (ring_rig R)) → FVTerm → FVTerm.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive fv_eq : FVTerm → FVTerm → Prop :=
  | fe_gen {x y : carrier X} : x ≈ y → fv_eq (fv_gen x) (fv_gen y)
  | fe_plus {s s' t t'} :
      fv_eq s s' → fv_eq t t' → fv_eq (fv_plus s t) (fv_plus s' t')
  | fe_neg {s s'} : fv_eq s s' → fv_eq (fv_neg s) (fv_neg s')
  | fe_smul {r r' : carrier (rig_setoid (ring_rig R))} {s s'} :
      r ≈ r' → fv_eq s s' → fv_eq (fv_smul r s) (fv_smul r' s')

  (* abelian group *)
  | fe_assoc (s t u : FVTerm) :
      fv_eq (fv_plus (fv_plus s t) u) (fv_plus s (fv_plus t u))
  | fe_comm (s t : FVTerm) : fv_eq (fv_plus s t) (fv_plus t s)
  | fe_zero_l (s : FVTerm) : fv_eq (fv_plus fv_zero s) s
  | fe_neg_l (s : FVTerm) : fv_eq (fv_plus (fv_neg s) s) fv_zero

  (* module *)
  | fe_smul_distr_l (r : carrier (rig_setoid (ring_rig R))) (s t : FVTerm) :
      fv_eq (fv_smul r (fv_plus s t))
            (fv_plus (fv_smul r s) (fv_smul r t))
  | fe_smul_distr_r (r r' : carrier (rig_setoid (ring_rig R))) (s : FVTerm) :
      fv_eq (fv_smul (rig_add (ring_rig R) r r') s)
            (fv_plus (fv_smul r s) (fv_smul r' s))
  | fe_smul_assoc (r r' : carrier (rig_setoid (ring_rig R))) (s : FVTerm) :
      fv_eq (fv_smul (rig_mul (ring_rig R) r r') s)
            (fv_smul r (fv_smul r' s))
  | fe_smul_one (s : FVTerm) :
      fv_eq (fv_smul (rig_one (ring_rig R)) s) s

  | fe_sym {s t} : fv_eq s t → fv_eq t s
  | fe_trans {s t u} : fv_eq s t → fv_eq t u → fv_eq s u.

Lemma fv_refl (s : FVTerm) : fv_eq s s.
Proof.
  induction s.
  - exact (fe_gen (reflexivity _)).
  - exact (fe_trans (fe_sym (fe_zero_l fv_zero)) (fe_zero_l fv_zero)).
  - exact (fe_plus IHs1 IHs2).
  - exact (fe_neg IHs).
  - exact (fe_smul (reflexivity _) IHs).
Qed.

Lemma fv_eq_Equivalence : Equivalence fv_eq.
Proof.
  constructor.
  - exact fv_refl.
  - exact (fun s t => fe_sym).
  - exact (fun s t u => fe_trans).
Qed.

Definition fv_Setoid : Setoid FVTerm := {|
  equiv        := fv_eq;
  setoid_equiv := fv_eq_Equivalence
|}.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FreeModObject : RModObject R := {|
  rm_ab := {|
    ab_cmon := {|
      cmon_setoid := {| carrier := FVTerm; is_setoid := fv_Setoid |};
      cmon_zero := fv_zero;
      cmon_plus := fv_plus;
      cmon_plus_respects := fun _ _ Hs _ _ Ht => fe_plus Hs Ht;
      cmon_plus_assoc := fe_assoc;
      cmon_plus_comm := fe_comm;
      cmon_plus_zero_l := fe_zero_l;
      (* [fv_eq] IS a [Prop] relation, so it is its own [Prop] mirror. *)
      cmon_prop := @PropEquiv_of_relation _ fv_Setoid fv_eq
                     (fun _ _ h => h) (fun _ _ h => h)
    |};
    ab_neg := fv_neg;
    ab_neg_respects := fun _ _ Hs => fe_neg Hs;
    ab_neg_left := fe_neg_l
  |};
  rm_smul := fv_smul;
  rm_smul_respects := fun _ _ Hr _ _ Hs => fe_smul Hr Hs;
  rm_smul_distr_l := fe_smul_distr_l;
  rm_smul_distr_r := fe_smul_distr_r;
  rm_smul_assoc := fe_smul_assoc;
  rm_smul_one := fe_smul_one
|}.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fv_insert : X ~{Sets}~> RMod_Forget R FreeModObject.
Proof.
  unshelve refine {| morphism := fv_gen |}.
  intros x y H; exact (fe_gen H).
Defined.

(** ** The linear extension of a function on generators *)

Section Extension.

Context (W : RModObject R).
Context (h : X ~{Sets}~> RMod_Forget R W).

(* Fold a formal expression through the target module's operations.  It
   computes on constructors, which is what makes all three homomorphism
   obligations below hold by [reflexivity]. *)
Fixpoint fv_eval (t : FVTerm) : carrier (cmon_setoid W) :=
  match t with
  | fv_gen x    => h x
  | fv_zero     => cmon_zero W
  | fv_plus s t => cmon_plus W (fv_eval s) (fv_eval t)
  | fv_neg s    => ab_neg W (fv_eval s)
  | fv_smul r s => rm_smul W r (fv_eval s)
  end.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fv_eval_respects (s t : FVTerm) : fv_eq s t → fv_eval s ≈ fv_eval t.
Proof.
  intro He.
  (*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  apply pequiv_to.
  induction He as
    [ x y Hxy
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | r r' s s' Hr _ IHs
    | s t u | s t | s | s
    | r s t | r r' s | r r' s | s
    | s t _ IHst
    | s t u _ IHst _ IHtu ]; simpl.
  - apply pequiv_from; exact (proper_morphism h _ _ Hxy).
  - apply pequiv_from.
    exact (cmon_plus_respects W _ _ (pequiv_to _ _ IHs)
                                _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from.
    exact (ab_neg_respects W _ _ (pequiv_to _ _ IHs)).
  - apply pequiv_from.
    exact (rm_smul_respects W _ _ Hr _ _ (pequiv_to _ _ IHs)).
  - apply pequiv_from; exact (cmon_plus_assoc W _ _ _).
  - apply pequiv_from; exact (cmon_plus_comm W _ _).
  - apply pequiv_from; exact (cmon_plus_zero_l W _).
  - apply pequiv_from; exact (ab_neg_left W _).
  - apply pequiv_from; exact (rm_smul_distr_l W _ _ _).
  - apply pequiv_from; exact (rm_smul_distr_r W _ _ _).
  - apply pequiv_from; exact (rm_smul_assoc W _ _ _).
  - apply pequiv_from; exact (rm_smul_one W _).
  - exact (symmetry IHst).
  - exact (transitivity IHst IHtu).
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition fv_extend : FreeModObject ~{RMod R}~> W := {|
  rm_hom := {| cmon_map := {| morphism := fv_eval |} |}
|}.
Next Obligation.
  first [ (intros s t He; exact (fv_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fv_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fv_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fv_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.

(* It agrees with [h] on the basis — definitionally, not up to [≈]. *)
Example free_module_extend_generators (x : carrier X) :
  cmon_map (rm_hom fv_extend) (fv_gen x) = h x := eq_refl.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_module_extend_zero :
  cmon_map (rm_hom fv_extend) fv_zero = cmon_zero W := eq_refl.

Example free_module_extend_plus (s t : FVTerm) :
  cmon_map (rm_hom fv_extend) (fv_plus s t)
    = cmon_plus W (cmon_map (rm_hom fv_extend) s)
                  (cmon_map (rm_hom fv_extend) t) := eq_refl.

Example free_module_extend_smul
  (r : carrier (rig_setoid (ring_rig R))) (s : FVTerm) :
  cmon_map (rm_hom fv_extend) (fv_smul r s)
    = rm_smul W r (cmon_map (rm_hom fv_extend) s) := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fv_extend_unique (g : FreeModObject ~{RMod R}~> W)
  (Hg : ∀ x : carrier X, cmon_map (rm_hom g) (fv_gen x) ≈ h x) (t : FVTerm) :
  cmon_map (rm_hom g) t ≈ fv_eval t.
Proof.
  induction t as [ x | | t1 IHt1 t2 IHt2 | t IHt | r t IHt ]; simpl.
  - exact (Hg x).
  - exact (cmon_map_zero (rm_hom g)).
  - refine (transitivity (cmon_map_plus (rm_hom g) t1 t2) _).
    exact (cmon_plus_respects W _ _ IHt1 _ _ IHt2).
  - refine (transitivity (rmod_map_neg g t) _).
    exact (ab_neg_respects W _ _ IHt).
  - refine (transitivity (rm_map_smul g r t) _).
    exact (rm_smul_respects W _ _ (reflexivity r) _ _ IHt).
Qed.

End Extension.

Arguments fv_eval {W} h t.
Arguments fv_extend {W} h.

(** ** The universal property, in the shape [universal_arrow_from_UMP]
       consumes *)
Theorem free_module_universal :
  ∀ (W : RModObject R) (h : X ~{Sets}~> RMod_Forget R W),
    ∃! g : FreeModObject ~{RMod R}~> W,
      h ≈ fmap[RMod_Forget R] g ∘ fv_insert.
Proof.
  intros W h.
  unshelve eexists.
  - exact (fv_extend h).
  - intro x; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry; apply (fv_extend_unique W h g).
    intro x; symmetry; exact (Hg x).
Qed.

End FreeModule.

Arguments FVTerm {R X}.
Arguments fv_gen {R X} x.
Arguments fv_zero {R X}.
Arguments fv_plus {R X} s t.
Arguments fv_neg {R X} s.
Arguments fv_smul {R X} r s.
Arguments fv_eq {R X} s t.
Arguments fv_refl {R X} s.
Arguments fe_gen {R X x y} _.
Arguments fe_plus {R X s s' t t'} _ _.
Arguments fe_neg {R X s s'} _.
Arguments fe_smul {R X r r' s s'} _ _.
Arguments fe_assoc {R X} s t u.
Arguments fe_comm {R X} s t.
Arguments fe_zero_l {R X} s.
Arguments fe_neg_l {R X} s.
Arguments fe_smul_distr_l {R X} r s t.
Arguments fe_smul_distr_r {R X} r r' s.
Arguments fe_smul_assoc {R X} r r' s.
Arguments fe_smul_one {R X} s.
Arguments fe_sym {R X s t} _.
Arguments fe_trans {R X s t u} _ _.
Arguments FreeModObject {R} X.
Arguments fv_insert {R} X.
Arguments fv_eval {R X W} h t.
Arguments fv_extend {R X W} h.
Arguments fv_eval_respects {R X} W h s t _.
Arguments fv_extend_unique {R X} W h g _ t.
Arguments free_module_universal {R} X W h.

(** ** The universal arrow, the free functor and the adjunction *)

Section FreeModuleAdjunction.

Context (R : RingObject).

(* The free module packaged as a universal arrow.  By
   Theory/Universal/Arrow.v this IS an initial object of the comma
   category [=(X) ↓ RMod_Forget R]. *)
Definition free_module_universal_arrow (X : Sets)
  : UniversalArrow X (RMod_Forget R) :=
  universal_arrow_from_UMP X (RMod_Forget R) (FreeModObject X) (fv_insert X)
    (free_module_universal X).

(* The same content in the direct encoding, where the universal object is
   named rather than projected out of a comma category. *)
Program Definition free_module_AUniversalArrow (X : Sets)
  : AUniversalArrow X (RMod_Forget R) (FreeModObject X) := {|
  universal_arrow := fv_insert X
|}.
Next Obligation.
  intros X W h.
  unshelve eexists.
  - exact (fv_extend h).
  - intro x; simpl; reflexivity.
  - intros g Hg t; simpl.
    (* [AUniversalArrow]'s uniqueness field is oriented the other way
       round from the comma-packaged one, hence the [symmetry]. *)
    symmetry; apply (fv_extend_unique W h g).
    intro x; exact (Hg x).
Qed.

(* The functor and the adjunction come out of the generic machinery with
   no further proof — the route Instance/Grp/Free.v,
   Instance/Coq/Monoid/Free.v and Construction/Free/Quiver.v all take. *)
Definition FreeMod : Sets ⟶ RMod R :=
  LeftAdjointFunctorFromUniversalArrows (RMod_Forget R)
    free_module_universal_arrow.

Definition free_module_adjunction : FreeMod ⊣ RMod_Forget R :=
  AdjunctionFromUniversalArrows (RMod_Forget R) free_module_universal_arrow.

(** The free functor's object part is the formal-sum module,
    definitionally. *)
Example FreeMod_obj (X : Sets) : FreeMod X = FreeModObject X := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_module_arrow_is_insert (X : Sets) :
  @arrow _ _ X (RMod_Forget R) (free_module_universal_arrow X) = fv_insert X
  := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_module_unit (X : Sets)
  : X ~{Sets}~> RMod_Forget R (FreeMod X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_module_adjunction X.

Example free_module_unit_is_insert (X : Sets) (x : carrier X) :
  free_module_unit X x = fv_insert X x := eq_refl.

Example free_module_unit_is_generator (X : Sets) (x : carrier X) :
  free_module_unit X x = @fv_gen R X x := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_module_counit (W : RMod R)
  : FreeMod (RMod_Forget R W) ~{RMod R}~> W :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_module_adjunction W.

Lemma free_module_counit_generator (W : RMod R)
  (m : carrier (RMod_Forget R W)) :
  cmon_map (rm_hom (free_module_counit W)) (fv_gen m) ≈ m.
Proof.
  exact (@to_adj_counit _ _ _ _ free_module_adjunction W m).
Qed.

Theorem free_module_counit_evaluates (W : RMod R)
  (t : @FVTerm R (RMod_Forget R W)) :
  cmon_map (rm_hom (free_module_counit W)) t
    ≈ fv_eval (@id Sets (RMod_Forget R W)) t.
Proof.
  apply (fv_extend_unique W (@id Sets (RMod_Forget R W))
           (free_module_counit W)).
  intro m; exact (free_module_counit_generator W m).
Qed.

(** ** The free functor relabels basis vectors

    Riehl's "functoriality on maps of generating sets".
    [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
    factorization, not by a formula, so what the functor does to a
    generator has to be proved. *)
Lemma free_module_fmap_generators {X Y : Sets} (u : X ~{Sets}~> Y)
  (x : carrier X) :
  cmon_map (rm_hom (fmap[FreeMod] u)) (fv_gen x) ≈ fv_gen (u x).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_module_universal_arrow X)
              (@arrow _ _ Y (RMod_Forget R)
                 (free_module_universal_arrow Y) ∘ u)) x).
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition fv_transpose {X : Sets} {W : RMod R}
  (g : FreeMod X ~{RMod R}~> W) : X ~{Sets}~> RMod_Forget R W :=
  fmap[RMod_Forget R] g ∘ fv_insert X.

Example free_module_transpose_is_adj {X : Sets} {W : RMod R}
  (g : FreeMod X ~{RMod R}~> W) :
  to (@adj _ _ _ _ free_module_adjunction X W) g = fv_transpose g := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma fv_transpose_extend {X : Sets} {W : RMod R}
  (h : X ~{Sets}~> RMod_Forget R W) : fv_transpose (fv_extend h) ≈ h.
Proof. intro x; simpl; reflexivity. Qed.

Lemma fv_extend_transpose {X : Sets} {W : RMod R}
  (g : FreeMod X ~{RMod R}~> W) : fv_extend (fv_transpose g) ≈ g.
Proof.
  intro t; simpl.
  symmetry; apply (fv_extend_unique W (fv_transpose g) g).
  intro x; simpl; reflexivity.
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_module_naturality_in_set {X Y : Sets} {W : RMod R}
  (g : FreeMod Y ~{RMod R}~> W) (u : X ~{Sets}~> Y) :
  fv_transpose (g ∘ fmap[FreeMod] u) ≈ fv_transpose g ∘ u.
Proof.
  intro x; simpl.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (free_module_fmap_generators u x)).
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_module_naturality_in_module {X : Sets} {W W' : RMod R}
  (k : W ~{RMod R}~> W') (g : FreeMod X ~{RMod R}~> W) :
  fv_transpose (k ∘ g) ≈ fmap[RMod_Forget R] k ∘ fv_transpose g.
Proof. intro x; simpl; reflexivity. Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_module_naturality_in_set_is_to_adj_nat_l
  {X Y : Sets} {W : RMod R} (g : FreeMod Y ~{RMod R}~> W)
  (u : X ~{Sets}~> Y) :
  (to (@adj _ _ _ _ free_module_adjunction X W) (g ∘ fmap[FreeMod] u)
     ≈ to (@adj _ _ _ _ free_module_adjunction Y W) g ∘ u)
  = (fv_transpose (g ∘ fmap[FreeMod] u) ≈ fv_transpose g ∘ u) := eq_refl.

Example free_module_naturality_in_module_is_to_adj_nat_r
  {X : Sets} {W W' : RMod R} (k : W ~{RMod R}~> W')
  (g : FreeMod X ~{RMod R}~> W) :
  (to (@adj _ _ _ _ free_module_adjunction X W') (k ∘ g)
     ≈ fmap[RMod_Forget R] k ∘ to (@adj _ _ _ _ free_module_adjunction X W) g)
  = (fv_transpose (k ∘ g) ≈ fmap[RMod_Forget R] k ∘ fv_transpose g) := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary free_module_triangle_left (X : Sets) :
  free_module_counit (FreeMod X) ∘ fmap[FreeMod] (free_module_unit X)
    ≈ @id (RMod R) (FreeMod X).
Proof. exact (@counit_fmap_unit _ _ _ _ free_module_adjunction X). Qed.

Corollary free_module_triangle_right (W : RMod R) :
  fmap[RMod_Forget R] (free_module_counit W)
    ∘ free_module_unit (RMod_Forget R W)
    ≈ @id Sets (RMod_Forget R W).
Proof. exact (@fmap_counit_unit _ _ _ _ free_module_adjunction W). Qed.

End FreeModuleAdjunction.

Arguments free_module_universal_arrow {R} X.
Arguments fv_transpose {R X W} g.
Arguments free_module_fmap_generators {R X Y} u x.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The fold respects pointwise-`≈` maps on generators: a citation of
   [fv_extend_unique]. *)
Lemma fv_eval_pointwise@{a c p so +} (R : RingObject@{a c p})
      {X : Sets@{c so}} {W : RMod R}
      (h h' : X ~{Sets@{c so}}~> RMod_Forget R W) (H : h ≈ h')
      (t : @FVTerm R X) :
  fv_eval h t ≈ fv_eval h' t.
Proof. exact (fv_extend_unique W h' (fv_extend h) (fun x => H x) t). Qed.

(* The natural bijection RMod(F X, W) ≅ Sets(X, U W): forward the
   restriction to the basis, backward the linear extension. *)
Definition free_module_hom_iso@{a c p so +} (R : RingObject@{a c p})
  (X : Sets@{c so}) (W : RMod R) :
  @Isomorphism Sets@{c so}
    {| carrier := @hom (RMod R) (FreeMod R X) W
     ; is_setoid := @homset (RMod R) (FreeMod R X) W |}
    {| carrier := @hom Sets@{c so} X (RMod_Forget R W)
     ; is_setoid := @homset Sets@{c so} X (RMod_Forget R W) |}.
Proof.
  unshelve refine
    (@Build_Isomorphism Sets
       {| carrier := @hom (RMod R) (FreeMod R X) W
        ; is_setoid := @homset (RMod R) (FreeMod R X) W |}
       {| carrier := @hom Sets X (RMod_Forget R W)
        ; is_setoid := @homset Sets X (RMod_Forget R W) |}
       (@Build_SetoidMorphism
          (@hom (RMod R) (FreeMod R X) W) (@homset (RMod R) (FreeMod R X) W)
          (@hom Sets X (RMod_Forget R W)) (@homset Sets X (RMod_Forget R W))
          (fun g => fv_transpose g) _)
       (@Build_SetoidMorphism
          (@hom Sets X (RMod_Forget R W)) (@homset Sets X (RMod_Forget R W))
          (@hom (RMod R) (FreeMod R X) W) (@homset (RMod R) (FreeMod R X) W)
          (fun h => fv_extend h) _) _ _).
  - intros g g' H x. exact (H (fv_gen x)).
  - intros h h' H t. exact (fv_eval_pointwise R h h' H t).
  - intros h x. reflexivity.
  - intros g t. exact (fv_extend_transpose R g t).
Defined.

(* The adjunction's last level, which no constraint mentions when it is
   left free, is pinned to the one of [Sets], as Instance/Smgrp.v and
   Instance/Mon/Free.v pin theirs. *)
Definition free_module_adjunction_hom@{a c p so +} (R : RingObject@{a c p}) :
  @Adjunction@{_ c c so c c c c so c so} (RMod R) Sets@{c so}
    (FreeMod R) (RMod_Forget R).
Proof.
  unshelve refine
    (@Build_Adjunction' (RMod R) Sets (FreeMod R) (RMod_Forget R)
       (free_module_hom_iso R) _ _).
  - intros X Y W g u. exact (free_module_naturality_in_set R g u).
  - intros X W W' k g. exact (free_module_naturality_in_module R k g).
Defined.

(* Its counit is the fold of the identity, by conversion. *)
Example free_module_hom_counit@{a c p so +} (R : RingObject@{a c p})
  (W : RMod R) (t : @FVTerm R (RMod_Forget R W)) :
  cmon_map (rm_hom (@counit _ _ _ _ (free_module_adjunction_hom R) W)) t
    = fv_eval (@id Sets@{c so} (RMod_Forget R W)) t := eq_refl.

(* Its unit and its forward transpose ARE those of
   [free_module_adjunction].  The cast pins the free level of that
   adjunction too, as the hom-set form's own is pinned above. *)
Example free_module_hom_unit@{a c p so +} (R : RingObject@{a c p})
  (X : Sets@{c so}) :
  @Category.Theory.Adjunction.unit _ _ _ _ (free_module_adjunction_hom R) X
    = @Category.Theory.Adjunction.unit _ _ _ _
        (free_module_adjunction R
           : @Adjunction@{_ c c so c c c c so c so} _ _ _ _) X
  := eq_refl.

Example free_module_hom_to@{a c p so +} (R : RingObject@{a c p})
  (X : Sets@{c so}) (W : RMod R) (g : FreeMod R X ~{RMod R}~> W) :
  to (@adj _ _ _ _ (free_module_adjunction_hom R) X W) g
    = to (@adj _ _ _ _ (free_module_adjunction R
                          : @Adjunction@{_ c c so c c c c so c so} _ _ _ _)
            X W) g := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section NormalForm.

Context (R : RingObject).
Context (X : SetoidObject).

Definition fv_pair : Type :=
  (carrier (rig_setoid (ring_rig R)) * carrier X)%type.

Fixpoint fv_lc (l : list fv_pair) : @FVTerm R X :=
  match l with
  | nil       => fv_zero
  | cons p l' => fv_plus (fv_smul (fst p) (fv_gen (snd p))) (fv_lc l')
  end.

Fixpoint fv_app (l l' : list fv_pair) : list fv_pair :=
  match l with
  | nil       => l'
  | cons p l0 => cons p (fv_app l0 l')
  end.

Fixpoint fv_negate (l : list fv_pair) : list fv_pair :=
  match l with
  | nil       => nil
  | cons p l0 => cons (ring_neg R (fst p), snd p) (fv_negate l0)
  end.

Fixpoint fv_scale (r : carrier (rig_setoid (ring_rig R)))
         (l : list fv_pair) : list fv_pair :=
  match l with
  | nil       => nil
  | cons p l0 => cons (rig_mul (ring_rig R) r (fst p), snd p) (fv_scale r l0)
  end.

Lemma fv_lc_app (l l' : list fv_pair) :
  fv_eq (fv_lc (fv_app l l')) (fv_plus (fv_lc l) (fv_lc l')).
Proof.
  induction l as [|p l IHl]; simpl.
  - exact (fe_sym (fe_zero_l _)).
  - exact (fe_trans (fe_plus (fv_refl _) IHl) (fe_sym (fe_assoc _ _ _))).
Qed.

(* Negating a combination negates each coefficient. *)
Lemma fv_lc_negate (l : list fv_pair) :
  fv_eq (fv_lc (fv_negate l)) (fv_neg (fv_lc l)).
Proof.
  induction l as [|p l IHl]; simpl.
  - exact (fe_sym (ab_neg_zero (FreeModObject X))).
  - refine (fe_trans (fe_plus (rm_smul_neg_l (FreeModObject X) _ _) IHl) _).
    exact (fe_sym (ab_neg_plus (FreeModObject X) _ _)).
Qed.

(* Scaling a combination scales each coefficient. *)
Lemma fv_lc_scale (r : carrier (rig_setoid (ring_rig R))) (l : list fv_pair) :
  fv_eq (fv_lc (fv_scale r l)) (fv_smul r (fv_lc l)).
Proof.
  induction l as [|p l IHl]; simpl.
  - exact (fe_sym (rm_smul_zero_r (FreeModObject X) r)).
  - exact (fe_trans (fe_plus (fe_smul_assoc _ _ _) IHl)
             (fe_sym (fe_smul_distr_l _ _ _))).
Qed.

Theorem fv_normal_form (t : @FVTerm R X) :
  ∃ l : list fv_pair, fv_eq t (fv_lc l).
Proof.
  induction t as [ x | | t1 IHt1 t2 IHt2 | t IHt | r t IHt ].
  - exists (cons (rig_one (ring_rig R), x) nil); simpl.
    refine (fe_trans (fe_sym (fe_zero_l _)) _).
    refine (fe_trans (fe_comm _ _) _).
    exact (fe_plus (fe_sym (fe_smul_one _)) (fv_refl _)).
  - exists nil; exact (fv_refl _).
  - destruct IHt1 as [l1 H1], IHt2 as [l2 H2].
    exists (fv_app l1 l2).
    exact (fe_trans (fe_plus H1 H2) (fe_sym (fv_lc_app l1 l2))).
  - destruct IHt as [l Hl].
    exists (fv_negate l).
    exact (fe_trans (fe_neg Hl) (fe_sym (fv_lc_negate l))).
  - destruct IHt as [l Hl].
    exists (fv_scale r l).
    exact (fe_trans (fe_smul (reflexivity r) Hl) (fe_sym (fv_lc_scale r l))).
Qed.

End NormalForm.

Arguments fv_lc {R X} l.
Arguments fv_normal_form {R X} t.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section NonDegeneracy.

Context (R : RingObject).
Context (X : SetoidObject).

(** *** Distinct scalars give distinct multiples of a basis vector

    This needs NO hypothesis on X and none on R beyond what
    [RingObject] already carries.  Map every generator to 1 in R viewed
    as a module over itself (Instance/Mod.v's [Ring_RMod]); then r·e_x
    evaluates to r·1 ≈ r. *)

Definition fv_probe_one : X ~{Sets}~> RMod_Forget R (Ring_RMod R).
Proof.
  unshelve refine {| morphism := fun _ => rig_one (ring_rig R) |}.
  intros a b _; exact (reflexivity (rig_one (ring_rig R))).
Defined.

Theorem free_module_scalars_faithful
  (r s : carrier (rig_setoid (ring_rig R))) (x : carrier X) :
  fv_eq (@fv_smul R X r (fv_gen x)) (fv_smul s (fv_gen x)) → r ≈ s.
Proof.
  intro He.
  pose proof (fv_eval_respects (Ring_RMod R) fv_probe_one _ _ He) as Hv.
  simpl in Hv.
  rewrite (rig_mul_one_r (ring_rig R) r) in Hv.
  rewrite (rig_mul_one_r (ring_rig R) s) in Hv.
  exact Hv.
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Context (Xdec : ∀ x y : carrier X, (x ≈ y) + ((x ≈ y) → False)).
Context (Rnz : rig_one (ring_rig R) ≈ rig_zero (ring_rig R) → False).

(* The characteristic function of the generator [x], with values in R
   viewed as a module over itself. *)
Definition fv_probe_at (x : carrier X)
  : X ~{Sets}~> RMod_Forget R (Ring_RMod R).
Proof using R X Xdec.
  unshelve refine {|
    morphism := fun z => match Xdec x z with
                         | inl _ => rig_one (ring_rig R)
                         | inr _ => rig_zero (ring_rig R)
                         end
  |}.
  intros z z' Hz; simpl.
  destruct (Xdec x z) as [Hxz|Hxz], (Xdec x z') as [Hxz'|Hxz'].
  - reflexivity.
  - destruct (Hxz' (transitivity Hxz Hz)).
  - destruct (Hxz (transitivity Hxz' (symmetry Hz))).
  - reflexivity.
Defined.

Theorem free_module_basis_injective (x y : carrier X) :
  fv_eq (@fv_gen R X x) (fv_gen y) → x ≈ y.
Proof using R X Xdec Rnz.
  intro He.
  destruct (Xdec x y) as [Hxy|Hxy]; [ exact Hxy | ].
  destruct Rnz.
  pose proof (fv_eval_respects (Ring_RMod R) (fv_probe_at x) _ _ He) as Hv.
  simpl in Hv.
  destruct (Xdec x x) as [_|Hxx]; [ | destruct (Hxx (reflexivity x)) ].
  destruct (Xdec x y) as [Hc|_]; [ destruct (Hxy Hc) | ].
  exact Hv.
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_module_two_independent (x y : carrier X)
  (Hxy : (x ≈ y) → False) (r s : carrier (rig_setoid (ring_rig R))) :
  fv_eq (fv_plus (@fv_smul R X r (fv_gen x)) (fv_smul s (fv_gen y))) fv_zero →
  (r ≈ rig_zero (ring_rig R)) * (s ≈ rig_zero (ring_rig R)).
(* [Rnz] is deliberately absent: this separation does not need it, and
   naming the section variables keeps that visible in the signature. *)
Proof using R X Xdec.
  intro He.
  split.
  - pose proof (fv_eval_respects (Ring_RMod R) (fv_probe_at x) _ _ He) as Hv.
    simpl in Hv.
    destruct (Xdec x x) as [_|Hxx]; [ | destruct (Hxx (reflexivity x)) ].
    destruct (Xdec x y) as [Hc|_]; [ destruct (Hxy Hc) | ].
    (* r·1 + s·0 ≈ 0 *)
    rewrite (rig_mul_one_r (ring_rig R) r) in Hv.
    rewrite (rig_mul_zero_r (ring_rig R) s) in Hv.
    rewrite (rig_add_zero_r (ring_rig R) r) in Hv.
    exact Hv.
  - pose proof (fv_eval_respects (Ring_RMod R) (fv_probe_at y) _ _ He) as Hv.
    simpl in Hv.
    destruct (Xdec y x) as [Hc|_];
      [ destruct (Hxy (symmetry Hc)) | ].
    destruct (Xdec y y) as [_|Hyy]; [ | destruct (Hyy (reflexivity y)) ].
    (* r·0 + s·1 ≈ 0 *)
    rewrite (rig_mul_zero_r (ring_rig R) r) in Hv.
    rewrite (rig_mul_one_r (ring_rig R) s) in Hv.
    rewrite (rig_add_zero_l (ring_rig R) s) in Hv.
    exact Hv.
Qed.

End NonDegeneracy.

Arguments fv_probe_one {R} X.
Arguments free_module_scalars_faithful {R X} r s x _.
Arguments free_module_basis_injective {R X} Xdec Rnz x y _.
Arguments free_module_two_independent {R X} Xdec x y Hxy r s _.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition TwoGens : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := eq; setoid_equiv := eq_equivalence |}
|}.

Definition two_gens_dec :
  ∀ x y : carrier TwoGens, (x ≈ y) + ((x ≈ y) → False).
Proof.
  intros x y; simpl.
  destruct x, y.
  - exact (inl eq_refl).
  - right; intro H; discriminate.
  - right; intro H; discriminate.
  - exact (inl eq_refl).
Defined.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma two_gens_distinct : @equiv _ (is_setoid TwoGens) true false → False.
Proof. intro H; discriminate H. Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Notation zgen  := (@fv_gen Int_Ring TwoGens).
Local Notation zsmul := (@fv_smul Int_Ring TwoGens).
Local Notation zplus := (@fv_plus Int_Ring TwoGens).

(* Two integers, read off the two generators. *)
Definition int_probe : TwoGens ~{Sets}~> RMod_Forget Int_Ring Int_RMod.
Proof.
  unshelve refine {| morphism := fun b : carrier TwoGens => if b then 3%Z else 5%Z |}.
  (*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  all: intros x y H; simpl in H; subst y; reflexivity.
Defined.

(* The linear extension computes: 2·e_true + e_false ↦ 2·3 + 5 = 11. *)
Example int_free_extend_computes :
  fv_eval int_probe
    (zplus (zsmul 2%Z (zgen true)) (zgen false)) = 11%Z := eq_refl.

Example int_free_extend_generator_true :
  fv_eval int_probe (zgen true) = 3%Z := eq_refl.

(* ℤ is not the zero ring, so the basis insertion is injective on this
   generating setoid. *)
Lemma int_one_neq_zero :
  rig_one (ring_rig Int_Ring) ≈ rig_zero (ring_rig Int_Ring) → False.
Proof. intro H; compute in H; discriminate H. Qed.

Theorem int_free_basis_distinct :
  fv_eq (zgen true) (zgen false) → False.
Proof.
  intro He.
  pose proof (free_module_basis_injective two_gens_dec int_one_neq_zero
                true false He) as Hb.
  compute in Hb; discriminate Hb.
Qed.

(* The basis is linearly independent over ℤ too.  This one spends the
   decider but NOT [int_one_neq_zero] — the ℚ reading of the same
   theorem is [free_vect_basis_independent]. *)
Theorem int_free_two_independent
  (r s : carrier (rig_setoid (ring_rig Int_Ring))) :
  fv_eq (zplus (zsmul r (zgen true)) (zsmul s (zgen false)))
        (@fv_zero Int_Ring TwoGens) →
  ((@equiv _ (rig_setoid (ring_rig Int_Ring)) r (rig_zero (ring_rig Int_Ring))) *
   (@equiv _ (rig_setoid (ring_rig Int_Ring)) s (rig_zero (ring_rig Int_Ring))))%type.
Proof.
  exact (@free_module_two_independent Int_Ring TwoGens two_gens_dec
           true false two_gens_distinct r s).
Qed.

(* ...and the scalars embed, with no decidability spent. *)
Theorem int_free_scalars_distinct :
  fv_eq (zsmul 2%Z (zgen true)) (zsmul 3%Z (zgen true)) → False.
Proof.
  intro He.
  pose proof (@free_module_scalars_faithful Int_Ring TwoGens 2%Z 3%Z true He)
    as Hz.
  compute in Hz; discriminate Hz.
Qed.
