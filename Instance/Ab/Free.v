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
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/free+abelian+group
 nLab:      https://ncatlab.org/nlab/show/free+object
 nLab:      https://ncatlab.org/nlab/show/universal+morphism
 Wikipedia: https://en.wikipedia.org/wiki/Free_abelian_group
 Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
 Book: Mac Lane, ibid., §IV.1, printed p. 79 (a free construction

   本文件给出自由构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

Section FreeAbelian.

Context (X : SetoidObject).

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive FATerm : Type :=
  | fa_gen  : carrier X → FATerm
  | fa_zero : FATerm
  | fa_plus : FATerm → FATerm → FATerm
  | fa_neg  : FATerm → FATerm.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive fa_eq : FATerm → FATerm → Prop :=
  | fae_gen {x y : carrier X} : x ≈ y → fa_eq (fa_gen x) (fa_gen y)
  | fae_plus {s s' t t'} :
      fa_eq s s' → fa_eq t t' → fa_eq (fa_plus s t) (fa_plus s' t')
  | fae_neg {s s'} : fa_eq s s' → fa_eq (fa_neg s) (fa_neg s')

  (* abelian group *)
  | fae_assoc (s t u : FATerm) :
      fa_eq (fa_plus (fa_plus s t) u) (fa_plus s (fa_plus t u))
  | fae_comm (s t : FATerm) : fa_eq (fa_plus s t) (fa_plus t s)
  | fae_zero_l (s : FATerm) : fa_eq (fa_plus fa_zero s) s
  | fae_neg_l (s : FATerm) : fa_eq (fa_plus (fa_neg s) s) fa_zero

  | fae_sym {s t} : fa_eq s t → fa_eq t s
  | fae_trans {s t u} : fa_eq s t → fa_eq t u → fa_eq s u.

Lemma fa_refl (s : FATerm) : fa_eq s s.
Proof.
  induction s.
  - exact (fae_gen (reflexivity _)).
  - exact (fae_trans (fae_sym (fae_zero_l fa_zero)) (fae_zero_l fa_zero)).
  - exact (fae_plus IHs1 IHs2).
  - exact (fae_neg IHs).
Qed.

Lemma fa_eq_Equivalence : Equivalence fa_eq.
Proof.
  constructor.
  - exact fa_refl.
  - exact (fun s t => fae_sym).
  - exact (fun s t u => fae_trans).
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fa_Setoid : Setoid FATerm := {|
  equiv        := fa_eq;
  setoid_equiv := fa_eq_Equivalence
|}.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FreeAbObject : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := FATerm; is_setoid := fa_Setoid |};
    cmon_zero := fa_zero;
    cmon_plus := fa_plus;
    cmon_plus_respects := fun _ _ Hs _ _ Ht => fae_plus Hs Ht;
    cmon_plus_assoc := fae_assoc;
    cmon_plus_comm := fae_comm;
    cmon_plus_zero_l := fae_zero_l;
    cmon_prop := @PropEquiv_of_relation _ fa_Setoid fa_eq
                   (fun _ _ h => h) (fun _ _ h => h)
  |};
  ab_neg := fa_neg;
  ab_neg_respects := fun _ _ Hs => fae_neg Hs;
  ab_neg_left := fae_neg_l
|}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_ab_carrier_is_FATerm :
  carrier (Ab_Forget FreeAbObject) = FATerm := eq_refl.

Example free_ab_equiv_is_fa_eq (s t : FATerm) :
  (@equiv _ (is_setoid (Ab_Forget FreeAbObject)) s t) = fa_eq s t
  := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition free_ab_insert : X ~{Sets}~> Ab_Forget FreeAbObject.
Proof.
  unshelve refine {| morphism := fa_gen |}.
  intros x y H; exact (fae_gen H).
Defined.

(* The 嵌入 IS generator former nose. （已译） *)
Example free_ab_insert_is_gen (x : carrier X) :
  free_ab_insert x = fa_gen x := eq_refl.

(* 相关说明。 （已译） *)

Section Extension.

Context (A : AbObject).
Context (h : X ~{Sets}~> Ab_Forget A).

(* Fold a formal expression through the target group's operations.  It
   computes on constructors, which is what makes both homomorphism
   obligations below hold by [reflexivity]. *)
Fixpoint fa_eval (t : FATerm) : carrier (cmon_setoid A) :=
  match t with
  | fa_gen x    => h x
  | fa_zero     => cmon_zero A
  | fa_plus s t => cmon_plus A (fa_eval s) (fa_eval t)
  | fa_neg s    => ab_neg A (fa_eval s)
  end.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fa_eval_respects (s t : FATerm) : fa_eq s t → fa_eval s ≈ fa_eval t.
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
    | s t u | s t | s | s
    | s t _ IHst
    | s t u _ IHst _ IHtu ]; simpl.
  - apply pequiv_from; exact (proper_morphism h _ _ Hxy).
  - apply pequiv_from.
    exact (cmon_plus_respects A _ _ (pequiv_to _ _ IHs)
                                _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from.
    exact (ab_neg_respects A _ _ (pequiv_to _ _ IHs)).
  - apply pequiv_from; exact (cmon_plus_assoc A _ _ _).
  - apply pequiv_from; exact (cmon_plus_comm A _ _).
  - apply pequiv_from; exact (cmon_plus_zero_l A _).
  - apply pequiv_from; exact (ab_neg_left A _).
  - exact (symmetry IHst).
  - exact (transitivity IHst IHtu).
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition free_ab_extend : FreeAbObject ~{Ab}~> A := {|
  cmon_map := {| morphism := fa_eval |}
|}.
Next Obligation.
  first [ (intros s t He; exact (fa_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fa_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fa_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.

(* 相关说明。 （已译） *)
Example free_ab_extend_generators (x : carrier X) :
  cmon_map free_ab_extend (fa_gen x) = h x := eq_refl.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_ab_extend_zero :
  cmon_map free_ab_extend fa_zero = cmon_zero A := eq_refl.

Example free_ab_extend_plus (s t : FATerm) :
  cmon_map free_ab_extend (fa_plus s t)
    = cmon_plus A (cmon_map free_ab_extend s)
                  (cmon_map free_ab_extend t) := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_ab_extend_neg (s : FATerm) :
  cmon_map free_ab_extend (fa_neg s)
    = ab_neg A (cmon_map free_ab_extend s) := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma free_ab_extend_unique (g : FreeAbObject ~{Ab}~> A)
  (Hg : ∀ x : carrier X, cmon_map g (fa_gen x) ≈ h x) (t : FATerm) :
  cmon_map g t ≈ fa_eval t.
Proof.
  induction t as [ x | | t1 IHt1 t2 IHt2 | t IHt ]; simpl.
  - exact (Hg x).
  - exact (cmon_map_zero g).
  - refine (transitivity (cmon_map_plus g t1 t2) _).
    exact (cmon_plus_respects A _ _ IHt1 _ _ IHt2).
  - refine (transitivity (ab_map_neg g t) _).
    exact (ab_neg_respects A _ _ IHt).
Qed.

End Extension.

Arguments fa_eval {A} h t.
Arguments free_ab_extend {A} h.

(* * ** The 普遍性质, shape [universal_arrow_from_UMP]
 所消耗 （已译） *)
Theorem free_ab_universal :
  ∀ (A : AbObject) (h : X ~{Sets}~> Ab_Forget A),
    ∃! g : FreeAbObject ~{Ab}~> A,
      h ≈ fmap[Ab_Forget] g ∘ free_ab_insert.
Proof.
  intros A h.
  unshelve eexists.
  - exact (free_ab_extend h).
  - intro x; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry; apply (free_ab_extend_unique A h g).
    intro x; symmetry; exact (Hg x).
Qed.

End FreeAbelian.

Arguments fa_gen {X} x.
Arguments fa_zero {X}.
Arguments fa_plus {X} s t.
Arguments fa_neg {X} s.
Arguments fa_eq {X} s t.
Arguments fa_refl {X} s.
Arguments fae_gen {X x y} _.
Arguments fae_plus {X s s' t t'} _ _.
Arguments fae_neg {X s s'} _.
Arguments fae_assoc {X} s t u.
Arguments fae_comm {X} s t.
Arguments fae_zero_l {X} s.
Arguments fae_neg_l {X} s.
Arguments fae_sym {X s t} _.
Arguments fae_trans {X s t u} _ _.
Arguments fa_eval {X A} h t.
Arguments free_ab_extend {X A} h.
Arguments fa_eval_respects {X} A h s t _.
Arguments free_ab_extend_unique {X} A h g _ t.

(* * ** The 泛箭头, free 函子 伴随 （已译） *)

(* The free abelian group packaged 泛箭头. By
 Theory/Universal/Arrow.v IS 始对象 comma
 范畴 [=(X) ↓ Ab_Forget]. （已译） *)
Definition free_ab_universal_arrow (X : Sets)
  : UniversalArrow X Ab_Forget :=
  universal_arrow_from_UMP X Ab_Forget (FreeAbObject X) (free_ab_insert X)
    (free_ab_universal X).

(* The same content direct encoding, where universal 对象 is
 named rather than projected out comma 范畴. （已译） *)
Program Definition free_ab_AUniversalArrow (X : Sets)
  : AUniversalArrow X Ab_Forget (FreeAbObject X) := {|
  universal_arrow := free_ab_insert X
|}.
Next Obligation.
  intros X A h.
  unshelve eexists.
  - exact (free_ab_extend h).
  - intro x; simpl; reflexivity.
  - intros g Hg t; simpl.
    (* 相关说明。 （已译） *)
    symmetry; apply (free_ab_extend_unique A h g).
    intro x; exact (Hg x).
Qed.

(*
   本节说明伴随、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FreeAb : Sets ⟶ Ab :=
  LeftAdjointFunctorFromUniversalArrows Ab_Forget free_ab_universal_arrow.

Definition free_ab_adjunction : FreeAb ⊣ Ab_Forget :=
  AdjunctionFromUniversalArrows Ab_Forget free_ab_universal_arrow.

(** The free 函子's 对象 part formal-sum group,
 definitionally. （已译） *)
Example FreeAb_obj (X : Sets) : FreeAb X = FreeAbObject X := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_ab_arrow_is_insert (X : Sets) :
  @arrow _ _ X Ab_Forget (free_ab_universal_arrow X) = free_ab_insert X
  := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_ab_unit (X : Sets)
  : X ~{Sets}~> Ab_Forget (FreeAb X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_ab_adjunction X.

Example free_ab_unit_is_insert (X : Sets) (x : carrier X) :
  free_ab_unit X x = free_ab_insert X x := eq_refl.

Example free_ab_unit_is_generator (X : Sets) (x : carrier X) :
  free_ab_unit X x = @fa_gen X x := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_ab_counit (A : Ab)
  : FreeAb (Ab_Forget A) ~{Ab}~> A :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_ab_adjunction A.

Lemma free_ab_counit_generator (A : Ab) (a : carrier (Ab_Forget A)) :
  cmon_map (free_ab_counit A) (fa_gen a) ≈ a.
Proof.
  exact (@to_adj_counit _ _ _ _ free_ab_adjunction A a).
Qed.

Theorem free_ab_counit_evaluates (A : Ab) (t : FATerm (Ab_Forget A)) :
  cmon_map (free_ab_counit A) t ≈ fa_eval (@id Sets (Ab_Forget A)) t.
Proof.
  apply (free_ab_extend_unique A (@id Sets (Ab_Forget A))
           (free_ab_counit A)).
  intro a; exact (free_ab_counit_generator A a).
Qed.

(* * ** The free 函子 relabels generators

 [LeftAdjointFunctorFromUniversalArrows] defines [fmap] universal
 factorization, not formula, so what 函子 does a
 generator has proved; it [≈] not [eq_refl]. （已译） *)
Lemma free_ab_fmap_generators {X Y : Sets} (u : X ~{Sets}~> Y)
  (x : carrier X) :
  cmon_map (fmap[FreeAb] u) (fa_gen x) ≈ fa_gen (u x).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_ab_universal_arrow X)
              (@arrow _ _ Y Ab_Forget (free_ab_universal_arrow Y) ∘ u)) x).
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition fa_transpose {X : Sets} {A : Ab}
  (g : FreeAb X ~{Ab}~> A) : X ~{Sets}~> Ab_Forget A :=
  fmap[Ab_Forget] g ∘ free_ab_insert X.

Example free_ab_transpose_is_adj {X : Sets} {A : Ab}
  (g : FreeAb X ~{Ab}~> A) :
  to (@adj _ _ _ _ free_ab_adjunction X A) g = fa_transpose g := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma fa_transpose_extend {X : Sets} {A : Ab}
  (h : X ~{Sets}~> Ab_Forget A) : fa_transpose (free_ab_extend h) ≈ h.
Proof. intro x; simpl; reflexivity. Qed.

Lemma fa_extend_transpose {X : Sets} {A : Ab}
  (g : FreeAb X ~{Ab}~> A) : free_ab_extend (fa_transpose g) ≈ g.
Proof.
  intro t; simpl.
  symmetry; apply (free_ab_extend_unique A (fa_transpose g) g).
  intro x; simpl; reflexivity.
Qed.

(* 相关说明。 （已译） *)
Theorem free_ab_naturality_in_set {X Y : Sets} {A : Ab}
  (g : FreeAb Y ~{Ab}~> A) (u : X ~{Sets}~> Y) :
  fa_transpose (g ∘ fmap[FreeAb] u) ≈ fa_transpose g ∘ u.
Proof.
  intro x; simpl.
  exact (proper_morphism (cmon_map g) _ _ (free_ab_fmap_generators u x)).
Qed.

(* * *** Naturality target group

 Both sides same 复合 underlying functions, so 这是
 [reflexivity] pointwise. （已译） *)
Theorem free_ab_naturality_in_group {X : Sets} {A A' : Ab}
  (k : A ~{Ab}~> A') (g : FreeAb X ~{Ab}~> A) :
  fa_transpose (k ∘ g) ≈ fmap[Ab_Forget] k ∘ fa_transpose g.
Proof. intro x; simpl; reflexivity. Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_ab_naturality_in_set_is_to_adj_nat_l
  {X Y : Sets} {A : Ab} (g : FreeAb Y ~{Ab}~> A) (u : X ~{Sets}~> Y) :
  (to (@adj _ _ _ _ free_ab_adjunction X A) (g ∘ fmap[FreeAb] u)
     ≈ to (@adj _ _ _ _ free_ab_adjunction Y A) g ∘ u)
  = (fa_transpose (g ∘ fmap[FreeAb] u) ≈ fa_transpose g ∘ u) := eq_refl.

Example free_ab_naturality_in_group_is_to_adj_nat_r
  {X : Sets} {A A' : Ab} (k : A ~{Ab}~> A') (g : FreeAb X ~{Ab}~> A) :
  (to (@adj _ _ _ _ free_ab_adjunction X A') (k ∘ g)
     ≈ fmap[Ab_Forget] k ∘ to (@adj _ _ _ _ free_ab_adjunction X A) g)
  = (fa_transpose (k ∘ g) ≈ fmap[Ab_Forget] k ∘ fa_transpose g) := eq_refl.

(** ** The triangle identities *)

Corollary free_ab_triangle_left (X : Sets) :
  free_ab_counit (FreeAb X) ∘ fmap[FreeAb] (free_ab_unit X)
    ≈ @id Ab (FreeAb X).
Proof. exact (@counit_fmap_unit _ _ _ _ free_ab_adjunction X). Qed.

Corollary free_ab_triangle_right (A : Ab) :
  fmap[Ab_Forget] (free_ab_counit A) ∘ free_ab_unit (Ab_Forget A)
    ≈ @id Sets (Ab_Forget A).
Proof. exact (@fmap_counit_unit _ _ _ _ free_ab_adjunction A). Qed.

Arguments fa_transpose {X A} g.
Arguments free_ab_fmap_generators {X Y} u x.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The fold respects pointwise-`≈` maps on generators: a citation of
   [free_ab_extend_unique]. *)
Lemma fa_eval_pointwise@{c so +} {X : Sets@{c so}} {A : Ab}
      (h h' : X ~{Sets@{c so}}~> Ab_Forget A) (H : h ≈ h') (t : FATerm X) :
  fa_eval h t ≈ fa_eval h' t.
Proof.
  exact (free_ab_extend_unique A h' (free_ab_extend h) (fun x => H x) t).
Qed.

(* 相关说明。 （已译） *)
Definition free_ab_hom_iso@{c so +} (X : Sets@{c so}) (A : Ab) :
  @Isomorphism Sets@{c so}
    {| carrier := @hom Ab (FreeAb X) A ; is_setoid := @homset Ab (FreeAb X) A |}
    {| carrier := @hom Sets@{c so} X (Ab_Forget A)
     ; is_setoid := @homset Sets@{c so} X (Ab_Forget A) |}.
Proof.
  unshelve refine
    (@Build_Isomorphism Sets
       {| carrier := @hom Ab (FreeAb X) A
        ; is_setoid := @homset Ab (FreeAb X) A |}
       {| carrier := @hom Sets X (Ab_Forget A)
        ; is_setoid := @homset Sets X (Ab_Forget A) |}
       (@Build_SetoidMorphism
          (@hom Ab (FreeAb X) A) (@homset Ab (FreeAb X) A)
          (@hom Sets X (Ab_Forget A)) (@homset Sets X (Ab_Forget A))
          (fun g => fa_transpose g) _)
       (@Build_SetoidMorphism
          (@hom Sets X (Ab_Forget A)) (@homset Sets X (Ab_Forget A))
          (@hom Ab (FreeAb X) A) (@homset Ab (FreeAb X) A)
          (fun h => free_ab_extend h) _) _ _).
  - intros g g' H x. exact (H (fa_gen x)).
  - intros h h' H t. exact (fa_eval_pointwise h h' H t).
  - intros h x. reflexivity.
  - intros g t. exact (fa_extend_transpose g t).
Defined.

(* The 伴随's last level, no constraint mentions it is
 left free, pinned one [Sets], Instance/Mod/Free.v pins
 own hom-set form. （已译） *)
Definition free_ab_adjunction_hom@{c so +} :
  @Adjunction@{_ c c so c c c c so c so} Ab Sets@{c so} FreeAb Ab_Forget.
Proof.
  unshelve refine
    (@Build_Adjunction' Ab Sets FreeAb Ab_Forget free_ab_hom_iso _ _).
  - intros X Y A g u. exact (free_ab_naturality_in_set g u).
  - intros X A A' k g. exact (free_ab_naturality_in_group k g).
Defined.

(* Its counit fold 恒等, conversion. （已译） *)
Example free_ab_hom_counit@{c so +} (A : Ab) (t : FATerm (Ab_Forget A)) :
  cmon_map (@counit _ _ _ _ free_ab_adjunction_hom A) t
    = fa_eval (@id Sets@{c so} (Ab_Forget A)) t := eq_refl.

(* Its unit forward transpose ARE those [free_ab_adjunction].
 The cast pins free level 伴随 too, hom-set
 form's own pinned above. （已译） *)
Example free_ab_hom_unit@{c so +} (X : Sets@{c so}) :
  @Category.Theory.Adjunction.unit _ _ _ _ free_ab_adjunction_hom X
    = @Category.Theory.Adjunction.unit _ _ _ _
        (free_ab_adjunction : @Adjunction@{_ c c so c c c c so c so} _ _ _ _)
        X
  := eq_refl.

Example free_ab_hom_to@{c so +} (X : Sets@{c so}) (A : Ab)
  (g : FreeAb X ~{Ab}~> A) :
  to (@adj _ _ _ _ free_ab_adjunction_hom X A) g
    = to (@adj _ _ _ _ (free_ab_adjunction
                          : @Adjunction@{_ c c so c c c c so c so} _ _ _ _)
            X A) g := eq_refl.


(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section NonDegeneracy.

Context (X : SetoidObject).
Context (A : AbObject).
Context (a : carrier (cmon_setoid A)).
Context (Ha : a ≈ cmon_zero A → False).

(* * *** Two separations need no decider at all

 The 常值 map at [a] 态射 [Sets] no 假设 on
 X whatever, it already refutes two cheapest collapses. （已译） *)

Definition fa_probe_const : X ~{Sets}~> Ab_Forget A.
Proof using X A a.
  unshelve refine {| morphism := fun _ => a |}.
  intros z z' _; reflexivity.
Defined.

(** A generator is not zero. *)
Theorem free_ab_gen_not_zero (x : carrier X) :
  fa_eq (@fa_gen X x) fa_zero → False.
Proof using X A a Ha.
  intro He.
  exact (Ha (fa_eval_respects A fa_probe_const _ _ He)).
Qed.

(*
   本节说明幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_ab_gen_not_idempotent (x : carrier X) :
  fa_eq (fa_plus (@fa_gen X x) (fa_gen x)) (fa_gen x) → False.
Proof using X A a Ha.
  intro He.
  pose proof (fa_eval_respects A fa_probe_const _ _ He) as Hv; simpl in Hv.
  apply Ha.
  apply (ab_cancel_l A a).
  transitivity a; [ exact Hv | ].
  symmetry; apply cmon_plus_zero_r.
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Context (Xdec : ∀ x y : carrier X, (x ≈ y) + ((x ≈ y) → False)).

(* 相关说明。 （已译） *)
Definition fa_probe_at (x : carrier X) : X ~{Sets}~> Ab_Forget A.
Proof using X A a Xdec.
  unshelve refine {|
    morphism := fun z => match Xdec x z with
                         | inl _ => a
                         | inr _ => cmon_zero A
                         end
  |}.
  intros z z' Hz; simpl.
  destruct (Xdec x z) as [Hxz|Hxz], (Xdec x z') as [Hxz'|Hxz'].
  - reflexivity.
  - destruct (Hxz' (transitivity Hxz Hz)).
  - destruct (Hxz (transitivity Hxz' (symmetry Hz))).
  - reflexivity.
Defined.

(** Distinct generators give distinct elements. *)
Theorem free_ab_gen_injective (x y : carrier X) :
  fa_eq (@fa_gen X x) (fa_gen y) → x ≈ y.
Proof using X A a Ha Xdec.
  intro He.
  destruct (Xdec x y) as [Hxy|Hxy]; [ exact Hxy | ].
  destruct Ha.
  pose proof (fa_eval_respects A (fa_probe_at x) _ _ He) as Hv.
  simpl in Hv.
  destruct (Xdec x x) as [_|Hxx]; [ | destruct (Hxx (reflexivity x)) ].
  destruct (Xdec x y) as [Hc|_]; [ destruct (Hxy Hc) | ].
  exact Hv.
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_ab_sum_not_summand (x y : carrier X)
  (Hxy : (x ≈ y) → False) :
  fa_eq (fa_plus (@fa_gen X x) (fa_gen y)) (fa_gen x) → False.
Proof using X A a Ha Xdec.
  intro He.
  pose proof (fa_eval_respects A (fa_probe_at y) _ _ He) as Hv.
  simpl in Hv.
  destruct (Xdec y x) as [Hc|_]; [ destruct (Hxy (symmetry Hc)) | ].
  destruct (Xdec y y) as [_|Hyy]; [ | destruct (Hyy (reflexivity y)) ].
  apply Ha.
  rewrite <- Hv.
  symmetry; apply cmon_plus_zero_l.
Qed.

End NonDegeneracy.

Arguments fa_probe_const {X} A a.
Arguments fa_probe_at {X} A a Xdec x.
Arguments free_ab_gen_not_zero {X} A a Ha x _.
Arguments free_ab_gen_not_idempotent {X} A a Ha x _.
Arguments free_ab_gen_injective {X} A a Ha Xdec x y _.
Arguments free_ab_sum_not_summand {X} A a Ha Xdec x y Hxy _.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ab_int : AbObject := ring_ab Int_Ring.

Lemma ab_int_one_not_zero : (1%Z : carrier (cmon_setoid ab_int))
  ≈ cmon_zero ab_int → False.
Proof. intro H; compute in H; discriminate H. Qed.

Definition AbTwoGens : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := eq; setoid_equiv := eq_equivalence |}
|}.

Definition ab_two_gens_dec :
  ∀ x y : carrier AbTwoGens, (x ≈ y) + ((x ≈ y) → False).
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
Local Notation zgen  := (@fa_gen AbTwoGens).
Local Notation zplus := (@fa_plus AbTwoGens).
Local Notation zneg  := (@fa_neg AbTwoGens).

(* Two integers, read off the two generators. *)
Definition ab_int_probe : AbTwoGens ~{Sets}~> Ab_Forget ab_int.
Proof.
  unshelve refine {|
    morphism := fun b : carrier AbTwoGens => if b then 3%Z else 5%Z
  |}.
  (*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  all: intros x y H; simpl in H; subst y; reflexivity.
Defined.

(* The additive extension computes: e_true + e_true + (−e_false)
   ↦ 3 + 3 − 5 = 1. *)
Example int_free_ab_extend_computes :
  fa_eval ab_int_probe
    (zplus (zplus (zgen true) (zgen true)) (zneg (zgen false)))
    = 1%Z := eq_refl.

Example int_free_ab_extend_generator_true :
  fa_eval ab_int_probe (zgen true) = 3%Z := eq_refl.

Example int_free_ab_extend_zero :
  fa_eval ab_int_probe (@fa_zero AbTwoGens) = 0%Z := eq_refl.

(** 本节：The four separations, instantiated at ℤ element 1 at the
 decidable two-element setoid. （已译） *)

Theorem int_free_ab_gen_not_zero :
  fa_eq (zgen true) (@fa_zero AbTwoGens) → False.
Proof.
  exact (@free_ab_gen_not_zero AbTwoGens ab_int 1%Z
           ab_int_one_not_zero true).
Qed.

Theorem int_free_ab_gen_not_idempotent :
  fa_eq (zplus (zgen true) (zgen true)) (zgen true) → False.
Proof.
  exact (@free_ab_gen_not_idempotent AbTwoGens ab_int 1%Z
           ab_int_one_not_zero true).
Qed.

Theorem int_free_ab_gens_distinct : fa_eq (zgen true) (zgen false) → False.
Proof.
  intro He.
  pose proof (@free_ab_gen_injective AbTwoGens ab_int 1%Z
                ab_int_one_not_zero ab_two_gens_dec true false He) as Hb.
  compute in Hb; discriminate Hb.
Qed.

Theorem int_free_ab_sum_not_summand :
  fa_eq (zplus (zgen true) (zgen false)) (zgen true) → False.
Proof.
  refine (@free_ab_sum_not_summand AbTwoGens ab_int 1%Z
            ab_int_one_not_zero ab_two_gens_dec true false _).
  intro H; discriminate H.
Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example counit_does_not_compute (A : Ab) (b : carrier (Ab_Forget A)) :
  cmon_map (free_ab_counit A) (fa_gen b) = b := eq_refl.

Example ab_control_unit_computes (X : Sets) (x : carrier X) :
  free_ab_unit X x = @fa_gen X x := eq_refl.

(*
   本节说明函子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example fmap_generator_does_not_compute
  (X Y : Sets) (u : X ~{Sets}~> Y) (x : carrier X) :
  cmon_map (fmap[FreeAb] u) (fa_gen x) = fa_gen (u x) := eq_refl.

Example control_fobj_computes (X : Sets) : FreeAb X = FreeAbObject X
  := eq_refl.

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example free_on_carrier_is_not_the_group :
  FreeAbObject (Ab_Forget ab_int) = ab_int := eq_refl.

Example control_generators_typecheck :
  carrier (Ab_Forget (FreeAbObject AbTwoGens))
  := (zgen true : FATerm AbTwoGens).

(* 相关说明。 （已译） *)
Fail Example instrument_check : (0%Z = 1%Z) := eq_refl.
