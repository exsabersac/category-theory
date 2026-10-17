Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Square.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Map.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Adjunction.
Require Import Category.Theory.Bicategory.Mates.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Instance.Cat.Bicategory.Square.
Require Import Category.Instance.Cat.Bicategory.Adjunction.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeSquare398。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ---------------------------------------------------------------------- *)
(* INSTRUMENT.  A passing [Fail] prints nothing under this repo's coqc, so *)
(* 相关说明。 （已译） *)
(* ---------------------------------------------------------------------- *)

Fail Check p398_no_such_constant_anywhere.

(* ---------------------------------------------------------------------- *)
(* GUARD BLOCK. Every 常值 any negative below names, target and （已译） *)
(* donor alike, is named here OUTSIDE every [Fail], so that renaming any   *)
(* one of them breaks this file at a [Check] line rather than turning a    *)
(* negative vacuously green.                                              *)
(* ---------------------------------------------------------------------- *)

Check @Category.
Check @Functor.
Check @Transform.
Check @Adjunction.
Check @Compose.
Check @Id.
Check @Isomorphism.
Check @Sets.
Check @SetoidObject.
Check @carrier.
Check @id.
Check @fobj.
Check @fmap.
Check @transform.
Check @Category.Theory.Adjunction.unit.
Check @eq.

Check @AdjointSquare.
Check @AdjointSquareUnit.
Check @AdjointSquareCounit.
Check @AdjointSquareT.
Check @SqSigma.
Check @SqTau.
Check @SigmaNat.
Check @TauNat.
Check @sq_mate.
Check @sq_mate_inv.
Check @SqMate.
Check @SqMateInv.
Check @sq_dom.
Check @sq_cod.
Check @square_bijection.
Check @palm_to.
Check @palm_via_mate.
Check @palm_two_factor.
Check @AB.
Check @SqBA.
Check @SqBA'.

Check @conj_dom.
Check @conj_cod.
Check @conjugate_bijection.
Check @conj_mate.
Check @conj_mate_inv.
Check @Conjugate.
Check @MapAdjHom.
Check @fun_comp_assoc.
Check @mate.
Check @mate_inv.

Check @palm_to_via_mate.
Check @palm_two_factor_agrees.
Check @AB_unit_upto.
Check @AB_to_strict.
Check @sq_mate_is_mate.
Check @sq_mate_inv_is_mate_inv.
Check @sq_mate_inv_mate.
Check @sq_mate_mate_inv.
Check @square_is_map_adj_hom.
Check @square_is_conjugate.
Check @sq_mate_is_conj_mate.
Check @sq_mate_inv_is_conj_mate_inv.
Check @fun_comp_assoc_component.
Check @fun_comp_assoc_is_id.
Check @bracket_fobj_left.
Check @bracket_fmap_left.
Check @adjoint_square_T_is_bare.
Check @adjoint_square_iff_mate.
Check @sq_mate_is_post_of_pre.
Check @sq_dom_setoid.
Check @sq_cod_setoid.
Check @adjoint_square_iff_Cat_mate.

(* ====================================================================== *)
(* (1) N1-N6, N11-N13, N20, N21 over the four-category context.           *)
(* ====================================================================== *)

Section P398Main.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

(* 相关说明。 （已译） *)

Example ctrl_n1 (al : F' ◯ L ◯ U ⟹ K) :
  @palm_via_mate C D F U A C' D' F' U' A' K L al
    ≈ @palm_to C D F U A C' D' F' U' A' K L al
  := @palm_to_via_mate C D F U A C' D' F' U' A' K L al.

Fail Example n1 (al : F' ◯ L ◯ U ⟹ K) (x : D) :
  @eq (fobj[L] x ~{D'}~> fobj[U'] (fobj[K] (fobj[F] x)))
      (@palm_via_mate C D F U A C' D' F' U' A' K L al x)
      (@palm_to C D F U A C' D' F' U' A' K L al x) := eq_refl.

(* -- N2.  CONTROL: the two-factor route agrees componentwise up to [≈]. -- *)

Example ctrl_n2 (al : F' ◯ L ◯ U ⟹ K) (x : D) :
  @palm_to C D F U A C' D' F' U' A' K L al x
    ≈ @palm_two_factor C D F U A C' D' F' U' A' K L al x
  := @palm_two_factor_agrees C D F U A C' D' F' U' A' K L al x.

Fail Example n2 (al : F' ◯ L ◯ U ⟹ K) (x : D) :
  @eq (fobj[L] x ~{D'}~> fobj[U'] (fobj[K] (fobj[F] x)))
      (@palm_to C D F U A C' D' F' U' A' K L al x)
      (@palm_two_factor C D F U A C' D' F' U' A' K L al x) := eq_refl.

(* -- N4/N5/N6. CONTROL: two bracketings agree 对象 -- （已译） *)
(* 相关说明。 （已译） *)

Example ctrl_n456a (a : C) :
  @eq (obj[C']) (fobj[F' ◯ L ◯ U] a) (fobj[F' ◯ (L ◯ U)] a)
  := @bracket_fobj_left C D U C' D' F' L a.

Example ctrl_n456b (a b : C) (f : a ~> b) :
  fmap[F' ◯ L ◯ U] f = fmap[F' ◯ (L ◯ U)] f
  := @bracket_fmap_left C D U C' D' F' L a b f.

Fail Example n4 :
  @eq Type (@Transform C C' (F' ◯ L ◯ U) K)
           (@Transform C C' (F' ◯ (L ◯ U)) K) := eq_refl.

Fail Example n5 :
  @eq Type (@Transform D D' L (U' ◯ K ◯ F))
           (@Transform D D' L (U' ◯ (K ◯ F))) := eq_refl.

Fail Example n6 :
  @eq (C ⟶ C') (F' ◯ L ◯ U) (F' ◯ (L ◯ U)) := eq_refl.

(* 相关说明。 （已译） *)
(* -- it is [≈ id] but not [= id].                                      -- *)

Example ctrl_n11a (x : D) :
  transform[@fun_comp_assoc D C C' D' U' K F] x
    = fmap[U'] (@id C' (fobj[K] (fobj[F] x)))
  := @fun_comp_assoc_component C D F C' D' U' K x.

Example ctrl_n11b (x : D) :
  transform[@fun_comp_assoc D C C' D' U' K F] x
    ≈ @id D' (fobj[U'] (fobj[K] (fobj[F] x)))
  := @fun_comp_assoc_is_id C D F C' D' U' K x.

Fail Example n11 (x : D) :
  @eq (fobj[U'] (fobj[K] (fobj[F] x)) ~{D'}~> fobj[U'] (fobj[K] (fobj[F] x)))
      (transform[@fun_comp_assoc D C C' D' U' K F] x)
      (@id D' (fobj[U'] (fobj[K] (fobj[F] x)))) := eq_refl.

(* -- N12.  CONTROL: the Cat bridge holds at [≈].                       -- *)

Example ctrl_n12 (sg : F' ◯ L ⟹ K ◯ F) :
  @SqMate C D F U A C' D' F' U' A' K L sg
    ≈ mate (@SqBA C D F U A) (@SqBA' C' D' F' U' A') sg
  := @sq_mate_is_mate C D F U A C' D' F' U' A' K L sg.

Fail Example n12 (sg : F' ◯ L ⟹ K ◯ F) (a : C) :
  @eq (fobj[L] (fobj[U] a) ~{D'}~> fobj[U'] (fobj[K] a))
      (@SqMate C D F U A C' D' F' U' A' K L sg a)
      (mate (@SqBA C D F U A) (@SqBA' C' D' F' U' A') sg a) := eq_refl.

(* -- N20 (round trip).  CONTROL: the round trip holds at [≈] under     -- *)
(* -- [SigmaNat]; the strict form is refuted at an arbitrary family.    -- *)

Example ctrl_n20 (sigma : SqSigma K L) (Hs : SigmaNat K L sigma) (x : D) :
  @sq_mate_inv C D F U A C' D' F' U' A' K L
    (@sq_mate C D F U A C' D' F' U' A' K L sigma) x ≈ sigma x
  := @sq_mate_inv_mate C D F U A C' D' F' U' A' K L sigma Hs x.

Fail Example n20 (sigma : SqSigma K L) (x : D) :
  @eq (fobj[F'] (fobj[L] x) ~{C'}~> fobj[K] (fobj[F] x))
      (@sq_mate_inv C D F U A C' D' F' U' A' K L
         (@sq_mate C D F U A C' D' F' U' A' K L sigma) x)
      (sigma x) := eq_refl.

(* 相关说明。 （已译） *)
(* -- statement is [MapAdjHom] on the nose.                             -- *)

Example ctrl_n13
  (al : ∀ x : D, fobj[K] (fobj[F] x) ≅ fobj[F'] (fobj[L] x))
  (be : ∀ a : C, fobj[L] (fobj[U] a) ≅ fobj[U'] (fobj[K] a)) :
  @AdjointSquare C D F U A C' D' F' U' A' K L
      (fun x => from (al x)) (fun a => to (be a))
    = @MapAdjHom C D F U A C' D' F' U' A' K L al be
  := @square_is_map_adj_hom C D F U A C' D' F' U' A' K L al be.

Context (sigma : SqSigma K L) (tau : SqTau K L).

Fail Check (@MapAdjHom C D F U A C' D' F' U' A' K L
              (fun x => sigma x) (fun a => tau a)).

(* -- N21 (TYPING).  CONTROL: [SqMate] accepts a sigma-shaped Transform. -- *)

Example ctrl_n21 (sg : F' ◯ L ⟹ K ◯ F) : L ◯ U ⟹ U' ◯ K
  := @SqMate C D F U A C' D' F' U' A' K L sg.

Fail Check (fun ta : L ◯ U ⟹ U' ◯ K =>
              @SqMate C D F U A C' D' F' U' A' K L ta).

End P398Main.

(* ====================================================================== *)
(* 相关说明。 （已译） *)
(*     identity-bounding-functor development Adjunction/Conjugate.v.      *)
(* ====================================================================== *)

Section P398Id.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {F2 : D ⟶ C} {U2 : C ⟶ D} (A2 : F2 ⊣ U2).

(* 相关说明。 （已译） *)
(* 相关说明。 （已译） *)
(* 相关说明。 （已译） *)

Example ctrl_id_a (s : F2 ⟹ F) (t : U ⟹ U2) :
  @AdjointSquare C D F U A C D F2 U2 A2 Id[C] Id[D]
      (transform[s]) (transform[t])
    = @Conjugate C D F U F2 U2 A A2 s t
  := @square_is_conjugate C D F U F2 U2 A A2 s t.

Example ctrl_id_b (s : F2 ⟹ F) (a : C) :
  @sq_mate C D F U A C D F2 U2 A2 Id[C] Id[D] (transform[s]) a
    = @conj_mate C D F U F2 U2 A A2 s a
  := @sq_mate_is_conj_mate C D F U F2 U2 A A2 s a.

Example ctrl_id_c (t : U ⟹ U2) (x : D) :
  @sq_mate_inv C D F U A C D F2 U2 A2 Id[C] Id[D] (transform[t]) x
    = @conj_mate_inv C D F U F2 U2 A A2 t x
  := @sq_mate_inv_is_conj_mate_inv C D F U F2 U2 A A2 t x.

Example ctrl_id_d :
  @eq Type (carrier (@conj_dom C D F F2)) (@Transform D C F2 F) := eq_refl.

Example ctrl_id_e :
  @eq Type (carrier (@sq_dom C D F C D F2 Id[C] Id[D]))
           (@Transform D C (F2 ◯ Id[D]) (Id[C] ◯ F)) := eq_refl.

Fail Example n7 :
  @eq Type (@Transform D C (F2 ◯ Id[D]) (Id[C] ◯ F))
           (@Transform D C F2 F) := eq_refl.

Fail Example n8 : @eq (D ⟶ C) (F2 ◯ Id[D]) F2 := eq_refl.

Fail Example n9 :
  @eq SetoidObject (@sq_dom C D F C D F2 Id[C] Id[D]) (@conj_dom C D F F2)
  := eq_refl.

Fail Example n10 :
  @eq (@Isomorphism Sets (@sq_dom C D F C D F2 Id[C] Id[D])
                         (@sq_cod C D U C D U2 Id[C] Id[D]))
      (@square_bijection C D F U A C D F2 U2 A2 Id[C] Id[D])
      (@conjugate_bijection C D F U F2 U2 A A2) := eq_refl.

End P398Id.

(* ====================================================================== *)
(* (3) N3: the composite adjunction's unit.                               *)
(* ====================================================================== *)

Section P398Vert.

Context {D C E : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {G : C ⟶ E} {V : E ⟶ C} (B : G ⊣ V).

(* CONTROL: 复合's TRANSPOSE definitional, unit （已译） *)
(* 相关说明。 （已译） *)

Example ctrl_n3a (x : D) (e : E) (k : fobj[G] (fobj[F] x) ~{E}~> e) :
  to (@adj E D (G ◯ F) (U ◯ V) (@AB D C E F U A G V B) x e) k
    = to (@adj C D F U A x (fobj[V] e))
        (to (@adj E C G V B (fobj[F] x) e) k)
  := @AB_to_strict D C E F U A G V B x e k.

Example ctrl_n3b (x : D) :
  @Category.Theory.Adjunction.unit E D (G ◯ F) (U ◯ V)
      (@AB D C E F U A G V B) x
    ≈ fmap[U] (@Category.Theory.Adjunction.unit E C G V B (fobj[F] x))
        ∘ @Category.Theory.Adjunction.unit C D F U A x
  := @AB_unit_upto D C E F U A G V B x.

Fail Example n3 (x : D) :
  @eq (x ~{D}~> fobj[U ◯ V] (fobj[G ◯ F] x))
      (@Category.Theory.Adjunction.unit E D (G ◯ F) (U ◯ V)
         (@AB D C E F U A G V B) x)
      (fmap[U] (@Category.Theory.Adjunction.unit E C G V B (fobj[F] x))
         ∘ @Category.Theory.Adjunction.unit C D F U A x) := eq_refl.

End P398Vert.

(* ====================================================================== *)
(* (4) N14 (FORMABILITY): [Adjunction] hom = 证明 donor. （已译） *)
(* ====================================================================== *)

Section P398UnivAdj.

Universes co ch cp.
Constraint ch < cp.

Context (Cu Du : Category@{co ch cp}).

(* CONTROLS, all accepted at these very levels. *)

Check (Cu ⟶ Du).
Check (Du ⟶ Cu).
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => @id Cu x).
Check (fun Fq Gq : Cu ⟶ Du => Fq ⟹ Gq).

Check (fun Fq : Du ⟶ Cu => Fq ⟹ Fq).
Check (fun Uq : Cu ⟶ Du => Uq ⟹ Uq).

Fail Check (fun (Fq : Du ⟶ Cu) (Uq : Cu ⟶ Du) => Fq ⊣ Uq).

(* -- N24 (FORMABILITY).  [Compose] is a SECOND donor of hom = proof,  -- *)
(* -- independent [Adjunction] refused here no 伴随 -- （已译） *)
(* -- anywhere in the command: Adjunction/Square.v's header attributes -- *)
(* 相关说明。 （已译） *)
(* -- five controls it lists and is not discriminating.                -- *)

Fail Check (fun (Fq : Du ⟶ Cu) (Uq : Cu ⟶ Du) => Uq ◯ Fq).

End P398UnivAdj.

(* ====================================================================== *)
(* (5) N15 (FORMABILITY): functors in BOTH directions identify the two    *)
(*     hom levels, before any adjunction is formed.                       *)
(* ====================================================================== *)

Section P398UnivFun.

Universes ao ah bo bh.
Constraint ah < bh.

Context (Aq : Category@{ao ah ah}).
Context (Bq : Category@{bo bh bh}).

Check (Aq ⟶ Bq).
Check (fun x y : Aq => x ~{Aq}~> y).
Check (fun x y : Bq => x ~{Bq}~> y).

Fail Check (Bq ⟶ Aq).

End P398UnivFun.

(* ====================================================================== *)
(* 相关说明。 （已译） *)
(*     EXTRA collapse that every Transform-typed constant of              *)
(*     Adjunction/Square.v carries.  The whole bare-family engine is      *)
(*     formable at levels declared strictly apart; the four composites    *)
(* 相关说明。 （已译） *)
(* ====================================================================== *)

Section P398UnivComp.

Universes co cho c2o ch2.
Constraint cho < ch2.

Context (Cu Du : Category@{co cho cho}).
Context (C2u D2u : Category@{c2o ch2 ch2}).
Context (Fu : Du ⟶ Cu) (Uu : Cu ⟶ Du) (Au : Fu ⊣ Uu).
Context (F2u : D2u ⟶ C2u) (U2u : C2u ⟶ D2u) (A2u : F2u ⊣ U2u).
Context (Ku : Cu ⟶ C2u) (Lu : Du ⟶ D2u).
Context (sg : SqSigma Ku Lu) (ta : SqTau Ku Lu).

(* 相关说明。 （已译） *)
(* 相关说明。 （已译） *)
(* 相关说明。 （已译） *)

Check (∀ x : Du, fobj[F2u] (fobj[Lu] x) ~{C2u}~> fobj[Ku] (fobj[Fu] x)).
Check (∀ a : Cu, fobj[Lu] (fobj[Uu] a) ~{D2u}~> fobj[U2u] (fobj[Ku] a)).
Check (@SqSigma Cu Du Fu C2u D2u F2u Ku Lu).
Check (@SqTau Cu Du Uu C2u D2u U2u Ku Lu).
Check (@AdjointSquare Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu sg ta).
Check (@AdjointSquareUnit Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu sg ta).
Check (@AdjointSquareCounit Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu sg ta).
Check (@sq_mate Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu sg).
Check (@sq_mate_inv Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu ta).
Check (@adjoint_square_iff_mate Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu sg ta).

Fail Check (F2u ◯ Lu).
Fail Check (Ku ◯ Fu).
Fail Check (Lu ◯ Uu).
Fail Check (U2u ◯ Ku).
Fail Check (@AdjointSquareT Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu).
Fail Check (@square_bijection Cu Du Fu Uu Au C2u D2u F2u U2u A2u Ku Lu).

End P398UnivComp.
