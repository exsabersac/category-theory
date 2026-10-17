Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Comma.
Require Import Category.Construction.FAlg.
Require Import Category.Construction.Funny.Comparison.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Coq.Lists.
Require Import List.

Generalizable All Variables.

(* * * The free 幺半群 type, 普遍性质 （已译） *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Free_monoid

   本文件给出自由构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:      https://ncatlab.org/nlab/show/free+monoid
   nLab:      https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Free_monoid
   Wikipedia: https://en.wikipedia.org/wiki/Kleene_star

   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Notation MonCoq := (@Mon Coq Coq_Monoidal).
#[local] Notation UMon := (@Mon_Forget Coq Coq_Monoidal).

#[local] Obligation Tactic := idtac.

(*
   本节说明幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Elements.

Context (L : MonCoq).

Definition mmul (a b : `1 L) : `1 L := mu[`2 L] (a, b).
Definition mone : `1 L := eta[`2 L] tt.

Lemma mmul_assoc (a b c : `1 L) : mmul (mmul a b) c = mmul a (mmul b c).
Proof. exact (@mu_assoc Coq Coq_Monoidal _ (`2 L) ((a, b), c)). Qed.

Lemma mone_left (a : `1 L) : mmul mone a = a.
Proof. exact (@mu_unit_left Coq Coq_Monoidal _ (`2 L) (tt, a)). Qed.

Lemma mone_right (a : `1 L) : mmul a mone = a.
Proof. exact (@mu_unit_right Coq Coq_Monoidal _ (`2 L) (a, tt)). Qed.

End Elements.

Arguments mmul {L} a b.
Arguments mone {L}.

(* 相关说明。 （已译） *)
Lemma hom_mmul {L N : MonCoq} (g : L ~{MonCoq}~> N) (a b : `1 L) :
  `1 g (mmul a b) = mmul (`1 g a) (`1 g b).
Proof. exact (@hom_mu Coq Coq_Monoidal _ _ _ _ _ (`2 g) (a, b)). Qed.

Lemma hom_mone {L N : MonCoq} (g : L ~{MonCoq}~> N) :
  `1 g (@mone L) = @mone N.
Proof. exact (@hom_eta Coq Coq_Monoidal _ _ _ _ _ (`2 g) tt). Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition FreeMonoidStructure (X : Type) :
  @Monoid Coq Coq_Monoidal (list X) := {|
  mu  := fun p => (fst p ++ snd p)%list;
  eta := fun _ => @nil X
|}.
Next Obligation.
  intros X p; destruct p as [[a b] c]; simpl.
  symmetry; apply app_assoc.
Qed.
Next Obligation.
  intros X p; destruct p as [u a]; destruct u; reflexivity.
Qed.
Next Obligation.
  intros X p; destruct p as [a u]; simpl.
  apply app_nil_r.
Qed.

(* The free monoid on [X] as an object of [Mon Coq]. *)
Definition FreeMon (X : Coq) : MonCoq := (list X; FreeMonoidStructure X).

(* 相关说明。 （已译） *)
Example free_mmul_is_app (X : Coq) (u v : list X) :
  mmul (L:=FreeMon X) u v = (u ++ v)%list := eq_refl.

Example free_mone_is_nil (X : Coq) : @mone (FreeMon X) = @nil X := eq_refl.

(* * ** The 嵌入 generators

 Awodey's [i : A → A*], sending letter one-letter word. （已译） *)

Definition insert (X : Coq) : X ~{Coq}~> UMon (FreeMon X) :=
  fun a => (a :: nil)%list.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint free_ext {X : Coq} {L : MonCoq} (h : X → `1 L) (l : list X)
  : `1 L :=
  match l with
  | nil       => @mone L
  | cons a l' => mmul (h a) (free_ext h l')
  end.

(* 相关说明。 （已译） *)
Lemma free_ext_app {X : Coq} {L : MonCoq} (h : X → `1 L) (u v : list X) :
  free_ext h (u ++ v)%list = mmul (free_ext h u) (free_ext h v).
Proof.
  induction u as [|a u IH]; simpl.
  - symmetry; apply mone_left.
  - rewrite IH; symmetry; apply mmul_assoc.
Qed.

(* 相关说明。 （已译） *)
Lemma free_ext_generators {X : Coq} {L : MonCoq} (h : X → `1 L) (a : X) :
  free_ext h (insert X a) = h a.
Proof. simpl; apply mone_right. Qed.

(* Hence it is a monoid homomorphism out of the free monoid. *)
Program Definition free_ext_MonoidHom {X : Coq} {L : MonCoq} (h : X → `1 L) :
  @MonoidHom Coq Coq_Monoidal (list X) (`1 L)
             (FreeMonoidStructure X) (`2 L) (free_ext h) := {|
  hom_mu  := _;
  hom_eta := _
|}.
Next Obligation.
  intros X L h p; destruct p as [u v]; simpl.
  apply free_ext_app.
Qed.
Next Obligation. intros X L h u; destruct u; reflexivity. Qed.

Definition free_hom {X : Coq} {L : MonCoq} (h : X → `1 L)
  : FreeMon X ~{MonCoq}~> L :=
  (free_ext h; free_ext_MonoidHom h).

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma free_ext_unique {X : Coq} {L : MonCoq} (h : X → `1 L)
      (g : FreeMon X ~{MonCoq}~> L)
      (Hg : forall a : X, `1 g (insert X a) = h a) (l : list X) :
  `1 g l = free_ext h l.
Proof.
  induction l as [|a l IH]; simpl.
  - exact (hom_mone g).
  - rewrite <- IH, <- (Hg a).
    exact (hom_mmul g (a :: nil)%list l).
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem free_monoid_universal (X : Coq) :
  forall (L : MonCoq) (h : X ~{Coq}~> UMon L),
    ∃! g : FreeMon X ~{MonCoq}~> L, h ≈ fmap[UMon] g ∘ insert X.
Proof.
  intros L h.
  unshelve eexists.
  - exact (free_hom h).
  - intro a; simpl.
    symmetry; apply free_ext_generators.
  - intros g Hg a; simpl.
    symmetry; apply free_ext_unique.
    intro b; symmetry; exact (Hg b).
Qed.

(* The free 幺半群 packaged 泛箭头 [X] [Mon_Forget].
 By [Theory/Universal/Arrow.v] IS 始对象 comma
 范畴 [=(X) ↓ Mon_Forget]. （已译） *)
Definition free_monoid_universal_arrow (X : Coq) : UniversalArrow X UMon :=
  universal_arrow_from_UMP X UMon (FreeMon X) (insert X)
                           (free_monoid_universal X).

(* The same content direct encoding, where universal 对象 is
 named rather than projected. （已译） *)
Program Definition free_monoid_AUniversalArrow (X : Coq)
  : AUniversalArrow X UMon (FreeMon X) := {|
  universal_arrow := insert X
|}.
Next Obligation.
  intros X L h.
  unshelve eexists.
  - exact (free_hom h).
  - intro a; simpl; apply free_ext_generators.
  - intros g Hg a; simpl.
    symmetry; apply free_ext_unique.
    intro b; exact (Hg b).
Qed.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FreeMonoid : Coq ⟶ MonCoq :=
  LeftAdjointFunctorFromUniversalArrows UMon free_monoid_universal_arrow.

Definition free_monoid_adjunction : FreeMonoid ⊣ UMon :=
  AdjunctionFromUniversalArrows UMon free_monoid_universal_arrow.

(* The free 函子's 对象 part word 幺半群, definitionally. （已译） *)
Example FreeMonoid_obj (X : Coq) : FreeMonoid X = FreeMon X := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_arrow_is_insert (X : Coq) :
  @arrow _ _ X UMon (free_monoid_universal_arrow X) = insert X := eq_refl.

(* Hence so unit 伴随: transpose 恒等 is
 [fmap[U] id ∘ arrow], [fmap[U] id] 恒等 function. （已译） *)
Example free_monoid_unit_is_insert (X : Coq) (a : X) :
  @Category.Theory.Adjunction.unit _ _ _ _ free_monoid_adjunction X a
    = insert X a := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma free_fmap_generators {X Y : Coq} (f : X ~{Coq}~> Y) (a : X) :
  `1 (fmap[FreeMonoid] f) (insert X a) = insert Y (f a).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_monoid_universal_arrow X)
              (@arrow _ _ Y UMon (free_monoid_universal_arrow Y) ∘ f)) a).
Qed.

(* The fold [a ↦ [f a]] 进入 free 幺半群 Y [map f]. （已译） *)
Lemma free_ext_insert {X Y : Coq} (f : X ~{Coq}~> Y) (l : list X) :
  free_ext (L:=FreeMon Y) (fun a => insert Y (f a)) l = map f l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|now rewrite IH].
Qed.

Theorem free_fmap_is_map {X Y : Coq} (f : X ~{Coq}~> Y) (l : list X) :
  `1 (fmap[FreeMonoid] f) l = map f l.
Proof.
  etransitivity.
  - apply (free_ext_unique (L:=FreeMon Y) (fun a => insert Y (f a))
             (fmap[FreeMonoid] f) (free_fmap_generators f) l).
  - apply free_ext_insert.
Qed.

(*
   本节说明自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition insert_Transform : Id[Coq] ⟹ UMon ◯ FreeMonoid := {|
  transform := insert
|}.
Next Obligation. intros X Y f a; apply free_fmap_generators. Qed.
Next Obligation. intros X Y f a; symmetry; apply free_fmap_generators. Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example insert_Transform_is_adjunction_unit (X : Coq) (a : X) :
  transform[insert_Transform] X a
    = transform[@unit _ _ _ _
                  (@Adjunction_to_Transform _ _ _ _ free_monoid_adjunction)] X a
  := eq_refl.

(*
   本节说明伴随、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary free_monoid_transposition {X : Coq} {L : MonCoq}
      (g : FreeMonoid X ~{MonCoq}~> L) :
  to (@adj _ _ _ _ free_monoid_adjunction X L) g
    ≈ fmap[UMon] g ∘ insert X.
Proof. exact (@to_adj_unit _ _ _ _ free_monoid_adjunction X L g). Qed.

Corollary free_monoid_transposition_at {X : Coq} {L : MonCoq}
      (g : FreeMonoid X ~{MonCoq}~> L) (a : X) :
  to (@adj _ _ _ _ free_monoid_adjunction X L) g a = `1 g (insert X a).
Proof. exact (free_monoid_transposition g a). Qed.

(* 相关说明。 （已译） *)
Corollary free_monoid_transposition_inv {X : Coq} {L : MonCoq}
      (h : X ~{Coq}~> UMon L) (l : list X) :
  `1 (from (@adj _ _ _ _ free_monoid_adjunction X L) h) l = free_ext h l.
Proof.
  apply free_ext_unique.
  intro a.
  etransitivity.
  - symmetry.
    exact (@free_monoid_transposition_at X L
             (from (@adj _ _ _ _ free_monoid_adjunction X L) h) a).
  - exact (@from_adj_comp_law _ _ _ _ free_monoid_adjunction X L h a).
Qed.

(*
   本节说明伴随、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AdjunctionCounit.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(* 相关说明。 （已译） *)
Program Definition adjunction_counit_underlying_retraction (x : C) :
  Retraction (fmap[U] (@Category.Theory.Adjunction.counit _ _ _ _ A x)) := {|
  retract := @Category.Theory.Adjunction.unit _ _ _ _ A (U x)
|}.
Next Obligation.
  intro x.
  exact (@Category.Theory.Adjunction.fmap_counit_unit _ _ _ _ A x).
Qed.

(* (b) A faithful 右伴随 makes counit epic: transport the
 cancellation through U, where split (a) does work. （已译） *)
Program Definition adjunction_counit_epic (FU : Faithful U) (x : C) :
  Epic (@Category.Theory.Adjunction.counit _ _ _ _ A x) := {| epic := _ |}.
Next Obligation.
  intros FU x z g1 g2 Heq.
  apply (fmap_inj (F:=U)).
  rewrite <- (id_right (fmap[U] g1)), <- (id_right (fmap[U] g2)).
  rewrite <- (@Category.Theory.Adjunction.fmap_counit_unit _ _ _ _ A x).
  rewrite !comp_assoc, <- !fmap_comp.
  now rewrite Heq.
Qed.

End AdjunctionCounit.

(* The free-monoid instances. *)
Definition free_monoid_counit_underlying_retraction (L : MonCoq) :
  Retraction (fmap[UMon]
                (@Category.Theory.Adjunction.counit _ _ _ _
                   free_monoid_adjunction L)) :=
  adjunction_counit_underlying_retraction free_monoid_adjunction L.

Definition free_monoid_counit_epic (L : MonCoq) :
  Epic (@Category.Theory.Adjunction.counit _ _ _ _ free_monoid_adjunction L) :=
  adjunction_counit_epic free_monoid_adjunction
    (@Mon_Forget_Faithful Coq Coq_Monoidal) L.

(* 相关说明。 （已译） *)
Corollary free_monoid_counit_surjective (L : MonCoq) (m : `1 L) :
  `1 (@Category.Theory.Adjunction.counit _ _ _ _ free_monoid_adjunction L)
     (insert (UMon L) m) = m.
Proof. exact (@Category.Theory.Adjunction.fmap_counit_unit _ _ _ _ free_monoid_adjunction L m). Qed.

(* And counit evaluation word L: fold 恒等
 map underlying type. （已译） *)
Theorem free_monoid_counit_is_free_ext (L : MonCoq) (w : list (`1 L)) :
  `1 (@Category.Theory.Adjunction.counit _ _ _ _ free_monoid_adjunction L) w
    = free_ext (fun m : `1 L => m) w.
Proof.
  apply free_ext_unique.
  exact (free_monoid_counit_surjective L).
Qed.

(*
   本节说明幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_monoid_unique {X : Coq} {M N : MonCoq}
      (UM : AUniversalArrow X UMon M) (UN : AUniversalArrow X UMon N) :
  Unique (fun i : M ≅ N =>
            fmap[UMon] (to i) ∘ @universal_arrow _ _ X UMon M UM
              ≈ @universal_arrow _ _ X UMon N UN) :=
  auniversal_arrow_unique UM UN.

(* At word 幺半群: any 幺半群 free-幺半群 UMP X uniquely
 isomorphic [FreeMon X] over 嵌入 generators. （已译） *)
Definition free_monoid_unique_iso {X : Coq} {N : MonCoq}
      (UN : AUniversalArrow X UMon N) :
  Unique (fun i : FreeMon X ≅ N =>
            fmap[UMon] (to i) ∘ insert X
              ≈ @universal_arrow _ _ X UMon N UN) :=
  auniversal_arrow_unique (free_monoid_AUniversalArrow X) UN.

(*
   本节说明幺半群、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition AMon (X : Coq) : Category := (=(X) ↓ UMon).

Definition AMon_ob {X : Coq} (L : MonCoq) (h : X ~{Coq}~> UMon L) : AMon X :=
  ((ttt, L); h).

Program Definition AMon_hom {X : Coq} {L N : MonCoq}
        {h : X ~{Coq}~> UMon L} {k : X ~{Coq}~> UMon N}
        (g : L ~{MonCoq}~> N) (Hg : k ≈ fmap[UMon] g ∘ h) :
  AMon_ob L h ~{AMon X}~> AMon_ob N k := ((id, g); _).
Next Obligation.
  intros X L N h k g Hg.
  simpl.
  rewrite ?fmap_id, ?id_right.
  assumption.
Qed.

(* Forward: the free monoid is an initial object of A-Mon. *)
Definition free_monoid_initial (X : Coq) : @Initial (AMon X) :=
  @arrow_initial _ _ X UMon (free_monoid_universal_arrow X).

Example free_monoid_initial_obj (X : Coq) :
  @initial_obj (AMon X) (free_monoid_initial X) = AMon_ob (FreeMon X) (insert X)
  := eq_refl.

(* Backward: an initial object of A-Mon is a universal arrow, hence a free
   monoid on X together with its insertion of generators. *)
Definition AMon_initial_universal_arrow (X : Coq) (I : @Initial (AMon X))
  : UniversalArrow X UMon := {| arrow_initial := I |}.

Example AMon_initial_round (X : Coq) :
  @arrow_initial _ _ X UMon
    (AMon_initial_universal_arrow X (free_monoid_initial X))
  = free_monoid_initial X := eq_refl.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example ListMon_hom_is_free_carrier :
  (ttt ~{ListMon}~> ttt) = UMon (FreeMon bool) := eq_refl.

Example ListMon_id_is_free_unit :
  @id ListMon ttt = @mone (FreeMon bool) := eq_refl.

Example ListMon_compose_is_free_mul (u v : list bool) :
  @compose ListMon ttt ttt ttt u v = mmul (L:=FreeMon bool) v u := eq_refl.

(* Two letters, and words in them. *)
Definition wa : list bool := (true :: nil)%list.
Definition wb : list bool := (false :: nil)%list.

Example wa_is_generator : wa = insert bool true := eq_refl.
Example wb_is_generator : wb = insert bool false := eq_refl.

Example word_ab :
  mmul (L:=FreeMon bool) wa wb = (true :: false :: nil)%list := eq_refl.
Example word_ba :
  mmul (L:=FreeMon bool) wb wa = (false :: true :: nil)%list := eq_refl.
Example word_noncommutative :
  mmul (L:=FreeMon bool) wa wb <> mmul (L:=FreeMon bool) wb wa.
Proof. discriminate. Qed.
Example word_assoc :
  mmul (L:=FreeMon bool) (mmul (L:=FreeMon bool) wa wb) wa
    = mmul (L:=FreeMon bool) wa (mmul (L:=FreeMon bool) wb wa) := eq_refl.
Example word_unit_left :
  mmul (L:=FreeMon bool) (@mone (FreeMon bool)) wa = wa := eq_refl.
Example word_unit_right :
  mmul (L:=FreeMon bool) wa (@mone (FreeMon bool)) = wa := eq_refl.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition XorMonoidStructure : @Monoid Coq Coq_Monoidal bool := {|
  mu  := fun p => xorb (fst p) (snd p);
  eta := fun _ => false
|}.
Next Obligation.
  intros p; destruct p as [[a b] c]; simpl.
  apply Bool.xorb_assoc_reverse.
Qed.
Next Obligation. intros p; destruct p as [u a]; destruct u; reflexivity. Qed.
Next Obligation.
  intros p; destruct p as [a u]; simpl; apply Bool.xorb_false_r.
Qed.

Definition XorMon : MonCoq := (bool; XorMonoidStructure).

(* The extension 恒等 map letters counts parity word,
 computes. （已译） *)
Example fold_into_xor_1 :
  free_ext (L:=XorMon) (fun b : bool => b) (true :: false :: true :: nil)%list
    = false := eq_refl.

Example fold_into_xor_2 :
  `1 (free_hom (L:=XorMon) (fun b : bool => b))
     (mmul (L:=FreeMon bool) wa wb) = true := eq_refl.

(* And it really 幺半群 homomorphism out word 幺半群, computed on
 concatenation. （已译） *)
Example fold_into_xor_hom :
  `1 (free_hom (L:=XorMon) (fun b : bool => b))
     (mmul (L:=FreeMon bool) (mmul (L:=FreeMon bool) wa wa) wb)
    = mmul (L:=XorMon)
        (`1 (free_hom (L:=XorMon) (fun b : bool => b))
            (mmul (L:=FreeMon bool) wa wa))
        (`1 (free_hom (L:=XorMon) (fun b : bool => b)) wb) := eq_refl.

(*
   本节说明幺半群、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition monoid_ListF_alg {X : Coq} {L : MonCoq} (h : X → `1 L)
  : ListF X (`1 L) ~{Coq}~> `1 L :=
  fun o => match o with
           | None          => @mone L
           | Some (a, m)   => mmul (h a) m
           end.

Definition monoid_FAlg {X : Coq} {L : MonCoq} (h : X → `1 L) : FAlg (ListF X) :=
  existT (FAlgebra (ListF X)) (`1 L) (monoid_ListF_alg h).

Theorem free_ext_is_fold {X : Coq} {L : MonCoq} (h : X → `1 L) (l : list X) :
  free_ext h l = fold (monoid_ListF_alg h) l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|now rewrite IH].
Qed.

(* The unique [ListF X]-algebra map out [(list X, alg X)] 进入 induced
 algebra free-幺半群 extension. （已译） *)
Theorem free_ext_is_initial_algebra_map {X : Coq} {L : MonCoq}
        (h : X → `1 L) (l : list X) :
  falg_hom[@zero (FAlg (ListF X)) (list_initial X) (monoid_FAlg h)] l
    = free_ext h l.
Proof. symmetry; apply free_ext_is_fold. Qed.

(* 相关说明。 （已译） *)
Corollary free_ext_is_the_unique_algebra_map {X : Coq} {L : MonCoq}
        (h : X → `1 L) (g : list X → `1 L)
        (Hg : forall o, g (alg X o) = monoid_ListF_alg h (fmap[ListF X] g o))
        (l : list X) : g l = free_ext h l.
Proof.
  rewrite (hom_is_fold (monoid_ListF_alg h) g Hg l).
  symmetry; apply free_ext_is_fold.
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

