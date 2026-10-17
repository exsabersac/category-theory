Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Adjunction.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.Coalgebra.
Require Import Category.Comonad.Duality.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Thin.Monad.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Order.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monad.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/comonad
 Book: Riehl, "Category Theory in Context", 2nd ed., SS 5.1,
 Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出单子相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition InteriorOperator@{u} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) : Type@{u} :=
  ClosureOperator@{u} (flip_PreOrder P).

(* 相关说明。 （已译） *)
Definition flip_mono@{u v} {A : Type@{u}} {B : Type@{v}} {R : relation A}
  {S : relation B} (f : @MonotoneFun@{u v} A R B S) :
  @MonotoneFun@{u v} A (Basics.flip R) B (Basics.flip S) :=
  {| mono_map := f; mono_pres := fun x y h => mono_pres f y x h |}.

Definition unflip_mono@{u v} {A : Type@{u}} {B : Type@{v}} {R : relation A}
  {S : relation B}
  (f : @MonotoneFun@{u v} A (Basics.flip R) B (Basics.flip S)) :
  @MonotoneFun@{u v} A R B S :=
  {| mono_map := f; mono_pres := fun x y h => mono_pres f y x h |}.

Example flip_unflip_mono@{u v} {A : Type@{u}} {B : Type@{v}}
  {R : relation A} {S : relation B}
  (f : @MonotoneFun@{u v} A (Basics.flip R) B (Basics.flip S)) :
  flip_mono (unflip_mono f) = f := eq_refl.

Example unflip_flip_mono@{u v} {A : Type@{u}} {B : Type@{v}}
  {R : relation A} {S : relation B} (f : @MonotoneFun@{u v} A R B S) :
  unflip_mono (flip_mono f) = f := eq_refl.

(* 相关说明。 （已译） *)
Definition int_defl@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (j : InteriorOperator@{u} P) (x : A) : R (cl_fun j x) x :=
  cl_ext j x.

Definition int_comult@{u} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) (x : A) :
  R (cl_fun j x) (cl_fun j (cl_fun j x)) :=
  cl_mult j x.

Definition int_mono@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (j : InteriorOperator@{u} P) (x y : A) (h : R x y) :
  R (cl_fun j x) (cl_fun j y) :=
  mono_pres (cl_fun j) y x h.

(* Riehl's "K p = K² p", up ≅ over preorder: 同构
 [cl_idem] reversed order, read backwards. （已译） *)
Definition int_idem@{u h} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (j : InteriorOperator@{u} P) (x : A) :
  cl_fun j (cl_fun j x) ≅[Proset@{u h} P] cl_fun j x :=
  @Build_Isomorphism (Proset@{u h} P) _ _
    (from (cl_idem@{u h} j x)) (to (cl_idem@{u h} j x)) I I.

Example int_idem_to@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) (x : A) :
  to (int_idem@{u h} j x) = int_defl j (cl_fun j x) := eq_refl.

(* Under antisymmetry, Riehl's equation itself. *)
Lemma int_idem_eq@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R) (j : InteriorOperator@{u} P)
  (x : A) : cl_fun j (cl_fun j x) = cl_fun j x.
Proof. exact (AS _ _ (int_defl j (cl_fun j x)) (int_comult j x)). Qed.

(** ** The correspondence *)

Definition interior_functor@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) :
  Proset@{u h} P ⟶ Proset@{u h} P :=
  Functor_of_monotone P P (unflip_mono (cl_fun j)).

(* Interior → 余单子: at (Proset P)^op counit comultiplication
 families ARE two fields, conversion; every law [I]. （已译） *)
Definition interior_comonad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) :
  @Comonad (Proset@{u h} P) (interior_functor j) :=
  @Build_Monad ((Proset@{u h} P)^op) ((interior_functor j)^op)
    (fun x => cl_ext j x) (fun x => cl_mult j x)
    (fun _ _ _ => I) (fun _ => I) (fun _ => I) (fun _ => I)
    (fun _ _ _ => I).

(* The same data as Structure/Thin/Monad.v's [thin_comonad]. *)
Example interior_comonad_extract@{u h t} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) (x : A) :
  @extract _ _ (interior_comonad@{u h} j) x
    = @extract _ _ (@thin_comonad@{t u h} (Proset@{u h} P) (fun _ _ _ _ => I)
                      (interior_functor@{u h} j) (cl_ext j) (cl_mult j)) x
  := eq_refl.

Example interior_comonad_duplicate@{u h t} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (j : InteriorOperator@{u} P) (x : A) :
  @duplicate _ _ (interior_comonad@{u h} j) x
    = @duplicate _ _ (@thin_comonad@{t u h} (Proset@{u h} P) (fun _ _ _ _ => I)
                        (interior_functor@{u h} j) (cl_ext j) (cl_mult j)) x
  := eq_refl.

(* 相关说明。 （已译） *)
Definition interior_of_comonad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} : InteriorOperator@{u} P :=
  {| cl_fun  := flip_mono (monotone_of_Functor P P W)
   ; cl_ext  := fun x => @extract _ W H x
   ; cl_mult := fun x => @duplicate _ W H x |}.

Definition comonad_interior_iff@{u h +} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) :
  { W : Proset@{u h} P ⟶ Proset@{u h} P & @Comonad (Proset@{u h} P) W }
    ↔ InteriorOperator@{u} P :=
  (fun p => match p with existT _ W H => interior_of_comonad W (H := H) end,
   fun j => existT (fun W : Proset@{u h} P ⟶ Proset@{u h} P =>
                      @Comonad (Proset@{u h} P) W)
              (interior_functor j) (interior_comonad j)).

(* interior → 余单子 → interior 恒等 WHOLE record. （已译） *)
Example interior_round_trip@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) :
  interior_of_comonad@{u h} (interior_functor@{u h} j)
    (H := interior_comonad j) = j := eq_refl.

(* comonad → interior → comonad: ≈ of functors, identity components. *)
Definition comonad_round_trip@{u h m n | h < n, u <= m, h <= m +}
  {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :
  interior_functor (interior_of_comonad W (H := H)) ≈ W :=
  Functor_of_monotone_of_Functor P P W.

Example comonad_round_trip_fobj@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  fobj[interior_functor (interior_of_comonad W (H := H))] x = fobj[W] x
  := eq_refl.

Example comonad_round_trip_fmap@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x y : A) (f : R x y) :
  fmap[interior_functor (interior_of_comonad W (H := H))] f = fmap[W] f
  := eq_refl.

(* ...and 余单子 it rebuilds has W's counit comultiplication. （已译） *)
Example comonad_round_trip_extract@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @extract _ _ (interior_comonad (interior_of_comonad W (H := H))) x
    = @extract _ W H x := eq_refl.

Example comonad_round_trip_duplicate@{u h} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @duplicate _ _ (interior_comonad (interior_of_comonad W (H := H))) x
    = @duplicate _ W H x := eq_refl.

(* * ** Riehl's route: 余单子 P 单子 reversed order （已译） *)

Definition flip_functor@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P) :
  Proset@{u h} (flip_PreOrder P) ⟶ Proset@{u h} (flip_PreOrder P) :=
  Functor_of_monotone (flip_PreOrder P) (flip_PreOrder P)
    (flip_mono (monotone_of_Functor P P W)).

(* The 单子 reversed order Instance/Proset/Monad.v's
 [closure_monad] at interior operator: unit extract its
 multiplication duplicate. （已译） *)
Definition comonad_flip_monad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :
  @Monad (Proset@{u h} (flip_PreOrder P)) (flip_functor W) :=
  closure_monad@{u h} (interior_of_comonad W (H := H)).

Example comonad_flip_ret@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @ret _ _ (comonad_flip_monad W (H := H)) x = @extract _ W H x
  := eq_refl.

Example comonad_flip_join@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @join _ _ (comonad_flip_monad W (H := H)) x = @duplicate _ W H x
  := eq_refl.

(* 相关说明。 （已译） *)
Example comonad_flip_monad_is_thin@{u h t} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :
  comonad_flip_monad W (H := H)
    = @thin_monad@{t u h} (Proset@{u h} (flip_PreOrder P))
        (fun _ _ _ _ => I) (flip_functor W)
        (fun x => @extract _ W H x) (fun x => @duplicate _ W H x)
  := eq_refl.

(* The interior operator W IS closure operator 单子. （已译） *)
Example interior_is_flip_closure@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :
  interior_of_comonad W (H := H)
    = closure_of_monad (flip_functor W) (MM := comonad_flip_monad W)
  := eq_refl.

(* The same functor as W^op read through Order.v's [Proset_op_iso]. *)
Example flip_functor_is_op_fobj@{u h n | h < n +} {A : Type@{u}}
  {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P) (x : A) :
  fobj[flip_functor W] x
    = fobj[Proset_op_to P ◯ W^op ◯ Proset_op_from P] x := eq_refl.

Example flip_functor_is_op_fmap@{u h n | h < n +} {A : Type@{u}}
  {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P) (x y : A)
  (f : Basics.flip R x y) :
  fmap[flip_functor W] f
    = fmap[Proset_op_to P ◯ W^op ◯ Proset_op_from P] f := eq_refl.

Lemma flip_functor_is_op@{u h m n | h < n, u <= m, h <= m +}
  {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P) :
  flip_functor W ≈ Proset_op_to P ◯ W^op ◯ Proset_op_from P.
Proof. exists (fun x => iso_id). intros; exact I. Qed.

(* 相关说明。 （已译） *)

(* A coalgebra W algebra reversed-order 单子: two
 records carry same structure map, every law [I]. （已译） *)
Definition wcoalgebra_iff_flip_talgebra@{u h} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @WCoalgebra (Proset@{u h} P) W H x
    ↔ @TAlgebra (Proset@{u h} (flip_PreOrder P)) (flip_functor W)
        (comonad_flip_monad W (H := H)) x :=
  (fun c => @Build_TAlgebra (Proset@{u h} (flip_PreOrder P))
              (flip_functor W) (comonad_flip_monad W (H := H)) x
              (@w_coalg _ W H x c) I I,
   fun a => @Build_WCoalgebra (Proset@{u h} P) W H x
              (@t_alg _ _ (comonad_flip_monad W (H := H)) x a) I I).

(* 相关说明。 （已译） *)
Definition wcoalgebra_iff_open@{u h p} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  iffT@{h p} (@WCoalgebra (Proset@{u h} P) W H x) (R x (W x)) :=
  let (to_flip, of_flip) := wcoalgebra_iff_flip_talgebra@{u h} W (H := H) x in
  let (to_closed, of_closed) :=
    talgebra_iff_closed@{u h p} (flip_functor W)
      (MM := comonad_flip_monad W (H := H)) x in
  (fun c => to_closed (to_flip c), fun h => of_flip (of_closed h)).

Example wcoalgebra_round@{u h p} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) (h : R x (W x)) :
  match wcoalgebra_iff_open@{u h p} W (H := H) x with
  | (to_open, of_open) => to_open (of_open h)
  end = h := eq_refl.

(* The second route: Structure/Thin/Monad.v's [thin_wcoalgebra_iff],
 单子 statement at (Proset P)^op. [Qed]: transparent,
 it carries sort level [Thin] body only. （已译） *)
Lemma wcoalgebra_iff_open_via_thin@{u h +} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @WCoalgebra (Proset@{u h} P) W H x ↔ R x (W x).
Proof. exact (@thin_wcoalgebra_iff (Proset@{u h} P) (fun _ _ _ _ => I) W H x).
Qed.

(* "x ≤ Kx ≤ x": open means Kx ≅ x. *)
Definition open_iff_fixed@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  R x (W x) ↔ (W x ≅[Proset@{u h} P] x) :=
  (fun h => @Build_Isomorphism (Proset@{u h} P) _ _
              (@extract _ W H x) h I I,
   fun i => from i).

(* Under antisymmetry a coalgebra is a fixed point: the dual of
   Instance/Proset/Monad.v's [closed_eq]. *)
Lemma open_eq@{u h} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R)
  (W : Proset@{u h} P ⟶ Proset@{u h} P) {H : @Comonad (Proset@{u h} P) W}
  (x : A) : @WCoalgebra (Proset@{u h} P) W H x → W x = x.
Proof. intro c. exact (AS _ _ (@extract _ W H x) (@w_coalg _ W H x c)). Qed.

(* FixedPoints.v's W-local 对象 (extract invertible) open
 ones. （已译） *)
Definition wlocal_iff_open@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  sobj (Proset@{u h} P) (WLocal_Subcategory H) x ↔ R x (W x) :=
  (fun Hi => @two_sided_inverse _ _ _ _ Hi,
   fun h => @Build_IsIsomorphism ((Proset@{u h} P)^op) x (W x)
              (@extract _ W H x) h I I).

(* 相关说明。 （已译） *)
Definition proset_open_coreflective@{u h t s f | h < s, u <= t, h <= t +}
  {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :=
  @thin_coreflective@{t u h s f} (Proset@{u h} P) (fun _ _ _ _ => I) W H.

(* * ** Seven Sketches SS 1.4.4: both composites ONE 伴随 （已译） *)

Definition adj_closure@{a b h s w | h < s +} {A : Type@{a}} {B : Type@{b}}
  {RA : relation A} {RB : relation B} {PA : PreOrder RA}
  {PB : PreOrder RB} {F : Proset@{a h} PA ⟶ Proset@{b h} PB}
  {U : Proset@{b h} PB ⟶ Proset@{a h} PA}
  (Adj : @Adjunction@{b h h a h h h h s h w} _ _ F U) :
  ClosureOperator@{a} PA :=
  closure_of_monad (U ◯ F) (MM := Adjunction_Monad@{b h a h s w} Adj).

(* [Adjunction_Comonad]'s level u4 (sixth in its binder) occurs in
   neither its type nor its constraints; it is pinned to h. *)
Definition adj_interior@{a b h s w | h < s +} {A : Type@{a}} {B : Type@{b}}
  {RA : relation A} {RB : relation B} {PA : PreOrder RA}
  {PB : PreOrder RB} {F : Proset@{a h} PA ⟶ Proset@{b h} PB}
  {U : Proset@{b h} PB ⟶ Proset@{a h} PA}
  (Adj : @Adjunction@{b h h a h h h h s h w} _ _ F U) :
  InteriorOperator@{b} PB :=
  interior_of_comonad (F ◯ U)
    (H := Adjunction_Comonad@{b h a h s h w} Adj).

Example adj_closure_fun@{a b h s w | h < s +} {A : Type@{a}}
  {B : Type@{b}} {RA : relation A} {RB : relation B} {PA : PreOrder RA}
  {PB : PreOrder RB} {F : Proset@{a h} PA ⟶ Proset@{b h} PB}
  {U : Proset@{b h} PB ⟶ Proset@{a h} PA}
  (Adj : @Adjunction@{b h h a h h h h s h w} _ _ F U) (x : A) :
  cl_fun (adj_closure Adj) x = U (F x) := eq_refl.

Example adj_interior_fun@{a b h s w | h < s +} {A : Type@{a}}
  {B : Type@{b}} {RA : relation A} {RB : relation B} {PA : PreOrder RA}
  {PB : PreOrder RB} {F : Proset@{a h} PA ⟶ Proset@{b h} PB}
  {U : Proset@{b h} PB ⟶ Proset@{a h} PA}
  (Adj : @Adjunction@{b h h a h h h h s h w} _ _ F U) (y : B) :
  cl_fun (adj_interior Adj) y = F (U y) := eq_refl.

(* At Galois.v's truncated shift (n - k ⊣ m + k) on (ℕ, ≤). *)
Example shift_closure_fun@{n h s w | h < s +} (k m : nat) :
  cl_fun (adj_closure@{n n h s w} (nat_shift_adjunction@{n n s w h} k)) m
    = ((m - k) + k)%nat := eq_refl.

Example shift_interior_fun@{n h s w | h < s +} (k m : nat) :
  cl_fun (adj_interior@{n n h s w} (nat_shift_adjunction@{n n s w h} k)) m
    = ((m + k) - k)%nat := eq_refl.

(* The closure is Instance/Proset/Monad.v's [max_closure k]... *)
Lemma shift_closure_is_max@{n h s w | h < s +} (k m : nat) :
  cl_fun (adj_closure@{n n h s w} (nat_shift_adjunction@{n n s w h} k)) m
    = cl_fun (max_closure@{n} k) m.
Proof. simpl. lia. Qed.

(* ...and interior 恒等: degenerate witness. （已译） *)
Lemma shift_interior_is_id@{n h s w | h < s +} (k m : nat) :
  cl_fun (adj_interior@{n n h s w} (nat_shift_adjunction@{n n s w h} k)) m
    = m.
Proof. simpl. lia. Qed.

(* 相关说明。 （已译） *)

Definition min_mono@{u} (k : nat) :
  @MonotoneFun@{u u} nat (Basics.flip Nat.le) nat (Basics.flip Nat.le) :=
  {| mono_map := fun n => Nat.min n k
   ; mono_pres := fun x y (H : (y <= x)%nat) =>
       Nat.min_le_compat_r y x k H |}.

Lemma min_comult@{} (k n : nat) :
  (Nat.min n k <= Nat.min (Nat.min n k) k)%nat.
Proof. lia. Qed.

Definition min_interior@{u} (k : nat) :
  InteriorOperator@{u} Nat.le_preorder :=
  {| cl_fun  := min_mono k
   ; cl_ext  := fun n => Nat.le_min_l n k
   ; cl_mult := fun n => min_comult k n |}.

(* 相关说明。 （已译） *)
Lemma min_open_iff@{u h +} (k n : nat) :
  @WCoalgebra (Proset@{u h} Nat.le_preorder)
    (interior_functor@{u h} (min_interior@{u} k))
    (interior_comonad@{u h} (min_interior@{u} k)) n ↔ (n <= k)%nat.
Proof.
  destruct (wcoalgebra_iff_open (interior_functor (min_interior k))
              (H := interior_comonad (min_interior k)) n)
    as [to_open of_open].
  split.
  - intro c. pose proof (to_open c) as H. simpl in H. lia.
  - intro H. apply of_open. simpl. lia.
Qed.

Lemma min_three_not_open@{u h} :
  @WCoalgebra (Proset@{u h} Nat.le_preorder)
    (interior_functor@{u h} (min_interior@{u} 2%nat))
    (interior_comonad@{u h} (min_interior@{u} 2%nat)) 3%nat → False.
Proof.
  intro c. destruct (min_open_iff 2%nat 3%nat) as [to_le _].
  pose proof (to_le c). lia.
Qed.
