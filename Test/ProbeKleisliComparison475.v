(*
   本文件为测试：ProbeKleisliComparison475。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Theory.Skeleton.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.StrictCat.
Require Import Category.Adjunction.Map.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Adjunction.
Require Import Category.Monad.Kleisli.Comparison.
Require Import Category.Theory.Skeleton.Separation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.One.
Require Import Category.Monad.Kleisli.Comparison.Examples.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** The instrument *)

(* The instrument *)
Fail Check p475_absent_name.

(* ------------------------------------------------------------------------ *)
(** ** Construction 1: the restricted adjunction and its monad *)

Section Restrict.

Context {X A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).
Context (S : Subcategory A) (full : Full A S).
Context (mem : ∀ x : X, sobj A S (F x)).

(* C1: G_B F_B and G F agree on objects. *)
Example p475_c1_monad_obj (x : X) :
  fobj[Restricted_Right G S ◯ Restricted_Left S full mem] x = fobj[G ◯ F] x
  := eq_refl.

(* C2: ... and on arrows. *)
Example p475_c2_monad_map (x y : X) (f : x ~> y) :
  fmap[Restricted_Right G S ◯ Restricted_Left S full mem] f = fmap[G ◯ F] f
  := eq_refl.

(* R1 *)
Fail Example p475_r1_functors :
  Restricted_Right G S ◯ Restricted_Left S full mem = G ◯ F := eq_refl.

(* C3: the two composites are naturally isomorphic. *)
Definition p475_c3_functors_equiv :
  Restricted_Right G S ◯ Restricted_Left S full mem ≈ G ◯ F :=
  Restricted_Monad_agrees S full mem.

(* C4: ... by the identity at every object. *)
Example p475_c4_functors_equiv_iso (x : X) :
  `1 (Restricted_Monad_agrees S full mem) x = iso_id := eq_refl.

(* C5: η of the restricted monad is η. *)
Example p475_c5_unit (x : X) :
  @ret X (Restricted_Right G S ◯ Restricted_Left S full mem)
       (Adjunction_Induced_Monad (Restricted_Adjunction Adj S full mem)) x
    = @ret X (G ◯ F) (Adjunction_Induced_Monad Adj) x := eq_refl.

(* C6: μ of the restricted monad is μ. *)
Example p475_c6_join (x : X) :
  @join X (Restricted_Right G S ◯ Restricted_Left S full mem)
        (Adjunction_Induced_Monad (Restricted_Adjunction Adj S full mem)) x
    = @join X (G ◯ F) (Adjunction_Induced_Monad Adj) x := eq_refl.

(* R2 *)
Fail Example p475_r2_monad_records :
  Adjunction_Induced_Monad (Restricted_Adjunction Adj S full mem)
    = Adjunction_Induced_Monad Adj := eq_refl.

(* R3 *)
Fail Example p475_r3_monads_objects :
  ((Restricted_Right G S ◯ Restricted_Left S full mem;
    Adjunction_Induced_Monad (Restricted_Adjunction Adj S full mem))
     : Monads X)
    = (G ◯ F; Adjunction_Induced_Monad Adj) := eq_refl.

(* C7: the two monads are isomorphic in [Monads X]... *)
Definition p475_c7_monads_iso :
  ((Restricted_Right G S ◯ Restricted_Left S full mem;
    Adjunction_Induced_Monad (Restricted_Adjunction Adj S full mem))
     : Monads X)
    ≅ (G ◯ F; Adjunction_Induced_Monad Adj) :=
  Restricted_Monad_iso Adj S full mem.

(* C8: ... with the identity as every component of [to]... *)
Example p475_c8_monads_iso_to (x : X) :
  transform[mh_transform (to (Restricted_Monad_iso Adj S full mem))] x = id
  := eq_refl.

(* C9: ... and of [from]. *)
Example p475_c9_monads_iso_from (x : X) :
  transform[mh_transform (from (Restricted_Monad_iso Adj S full mem))] x
    = id := eq_refl.

End Restrict.

(* ------------------------------------------------------------------------ *)
(** ** Theorem 2: L by transposition, and its two triangles *)

Section Comparison.

Context {X A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).

Notation T := (Adjunction_Induced_Monad Adj).
Notation XT := (@Kleisli X (G ◯ F) T).

(* C10: L x = F x. *)
Example p475_c10_obj (x : X) : fobj[Kleisli_Comparison Adj] x = F x
  := eq_refl.

(* C11: L f is the transpose of f. *)
Example p475_c11_map (x y : X) (f : x ~{XT}~> y) :
  fmap[Kleisli_Comparison Adj] f = from (@adj _ _ _ _ Adj x (F y)) f
  := eq_refl.

(* R4 *)
Fail Example p475_r4_map_counit (x y : X) (f : x ~{XT}~> y) :
  fmap[Kleisli_Comparison Adj] f = @counit _ _ _ _ Adj (F y) ∘ fmap[F] f
  := eq_refl.

(* C12: L f = ε ∘ F f up to ≈. *)
Definition p475_c12_map_counit (x y : X) (f : x ~{XT}~> y) :
  fmap[Kleisli_Comparison Adj] f ≈ @counit _ _ _ _ Adj (F y) ∘ fmap[F] f :=
  Kleisli_Comparison_map_counit Adj x y f.

(* C13: G L = G_T on objects. *)
Example p475_c13_forget_obj (x : X) :
  fobj[G ◯ Kleisli_Comparison Adj] x = fobj[@Kleisli_Forget X (G ◯ F) T] x
  := eq_refl.

(* R5 *)
Fail Example p475_r5_forget_map (x y : X) (f : x ~{XT}~> y) :
  fmap[G ◯ Kleisli_Comparison Adj] f = fmap[@Kleisli_Forget X (G ◯ F) T] f
  := eq_refl.

(* C14: G L ≈ G_T with the identity at every object. *)
Example p475_c14_forget_iso (x : X) :
  `1 (Kleisli_Comparison_Forget Adj) x = iso_id := eq_refl.

(* C15: G L = G_T strictly, with eq_refl at every object. *)
Example p475_c15_forget_strict_obj (x : X) :
  `1 (Kleisli_Comparison_Forget_strict Adj) x = eq_refl := eq_refl.

(* C16: L F_T = F on objects. *)
Example p475_c16_free_obj (x : X) :
  fobj[Kleisli_Comparison Adj ◯ @Kleisli_Free X (G ◯ F) T] x = fobj[F] x
  := eq_refl.

(* R6 *)
Fail Example p475_r6_free_map (x y : X) (f : x ~> y) :
  fmap[Kleisli_Comparison Adj ◯ @Kleisli_Free X (G ◯ F) T] f = fmap[F] f
  := eq_refl.

(* C17: L F_T ≈ F with the identity at every object. *)
Example p475_c17_free_iso (x : X) :
  `1 (Kleisli_Comparison_Free Adj) x = iso_id := eq_refl.

(* C18: L F_T = F strictly, with eq_refl at every object. *)
Example p475_c18_free_strict_obj (x : X) :
  `1 (Kleisli_Comparison_Free_strict Adj) x = eq_refl := eq_refl.

End Comparison.

(* ------------------------------------------------------------------------ *)
(** ** Exercise 1's image and Exercise 2 at FX *)

Section Image.

Context {X A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).

Notation T := (Adjunction_Induced_Monad Adj).
Notation XT := (@Kleisli X (G ◯ F) T).

(* C19: F_B at B = FX is [ImageTo] on objects... *)
Example p475_c19_restricted_image_obj (x : X) :
  fobj[Restricted_Left (@LaliImageSub X A F) image_full
         (fun x => (x; eq_refl))] x
    = fobj[@ImageTo X A F] x := eq_refl.

(* C20: ... and on arrows. *)
Example p475_c20_restricted_image_map (x y : X) (f : x ~> y) :
  fmap[Restricted_Left (@LaliImageSub X A F) image_full
         (fun x => (x; eq_refl))] f
    = fmap[@ImageTo X A F] f := eq_refl.

(* C21: L' is [ImageTo] of L on objects... *)
Example p475_c21_image_is_imageto_obj (x : X) :
  fobj[Kleisli_Comparison_Image Adj] x
    = fobj[@ImageTo XT A (Kleisli_Comparison Adj)] x := eq_refl.

(* C22: ... and on arrows. *)
Example p475_c22_image_is_imageto_map (x y : X) (f : x ~{XT}~> y) :
  fmap[Kleisli_Comparison_Image Adj] f
    = fmap[@ImageTo XT A (Kleisli_Comparison Adj)] f := eq_refl.

(* C23: L = Incl ◯ L' on objects... *)
Example p475_c23_incl_obj (x : X) :
  fobj[Incl A (@LaliImageSub X A F) ◯ Kleisli_Comparison_Image Adj] x
    = fobj[Kleisli_Comparison Adj] x := eq_refl.

(* C24: ... and on arrows. *)
Example p475_c24_incl_map (x y : X) (f : x ~{XT}~> y) :
  fmap[Incl A (@LaliImageSub X A F) ◯ Kleisli_Comparison_Image Adj] f
    = fmap[Kleisli_Comparison Adj] f := eq_refl.

(* C25: the chosen preimage of (a; (x; e)) is x. *)
Example p475_c25_surjective_obj (y : Sub A (@LaliImageSub X A F)) :
  `1 (Kleisli_Comparison_Image_surjective Adj y) = `1 (`2 y).
Proof. destruct y as [a [x e]]; reflexivity. Qed.

End Image.

(* ------------------------------------------------------------------------ *)
(** ** Riehl, Lemma 5.2.14: K : C_T ⟶ C^T *)

Section Riehl.

Context {C : Category} (T : C ⟶ C) `{H : @Monad C T}.

Notation KT := (@Kleisli C T H).
Notation KI := (@Kleisli C (EM_Forget T ◯ EM_Free T)
                  (Adjunction_Induced_Monad (EM_Adjunction T))).

(* C26: K c = (T c, μ_c). *)
Example p475_c26_em_obj (c : C) :
  fobj[@Kleisli_EM C T H] c = (T c; {| t_alg := @join C T H c |}) := eq_refl.

(* C27: K c is the free algebra on c. *)
Example p475_c27_em_obj_free (c : C) :
  fobj[@Kleisli_EM C T H] c = fobj[EM_Free T] c := eq_refl.

(* C28: K f has underlying arrow μ ∘ T f. *)
Example p475_c28_em_map (x y : C) (f : x ~{KT}~> y) :
  t_alg_hom[fmap[@Kleisli_EM C T H] f] = join ∘ fmap[T] f := eq_refl.

(* C29: U^T K = U_T on arrows. *)
Example p475_c29_em_forget_map (x y : C) (f : x ~{KT}~> y) :
  fmap[EM_Forget T ◯ @Kleisli_EM C T H] f = fmap[@Kleisli_Forget C T H] f
  := eq_refl.

(* C30: K f is the transpose of f under F^T ⊣ U^T. *)
Example p475_c30_em_transpose (x y : C) (f : x ~{KT}~> y) :
  fmap[@Kleisli_EM C T H] f
    = from (@adj _ _ _ _ (EM_Adjunction T) x (EM_Free T y)) f := eq_refl.

(* C31: K and L at the Eilenberg-Moore resolution agree on objects... *)
Example p475_c31_em_is_l_obj (c : C) :
  fobj[@Kleisli_EM C T H] c = fobj[Kleisli_Comparison (EM_Adjunction T)] c
  := eq_refl.

(* C32: ... and on arrows. *)
Example p475_c32_em_is_l_map (x y : C) (f : x ~{KT}~> y) :
  fmap[@Kleisli_EM C T H] f = fmap[Kleisli_Comparison (EM_Adjunction T)] f
  := eq_refl.

(* R7 *)
Fail Example p475_r7_em_is_l :
  @Kleisli_EM C T H = Kleisli_Comparison (EM_Adjunction T) := eq_refl.

(* R8 *)
Fail Example p475_r8_kleisli_categories : KT = KI := eq_refl.

(* R9 *)
Fail Example p475_r9_kleisli_ids (c : C) : @id KT c = @id KI c := eq_refl.

(* C33: the two identities agree up to ≈. *)
Example p475_c33_kleisli_ids_equiv (c : C) : @id KT c ≈ @id KI c.
Proof. simpl. symmetry. exact (@EM_unit_agrees C T H c). Qed.

(* R10 *)
Fail Example p475_r10_kleisli_compose (x y z : C)
  (f : y ~> T z) (g : x ~> T y) :
  @compose KT x y z f g = @compose KI x y z f g := eq_refl.

(* C34: the two composites agree up to ≈. *)
Example p475_c34_kleisli_compose_equiv (x y z : C)
  (f : y ~> T z) (g : x ~> T y) :
  @compose KT x y z f g ≈ @compose KI x y z f g.
Proof. simpl. rewrite fmap_id, id_right. reflexivity. Qed.

End Riehl.

(* ------------------------------------------------------------------------ *)
(** ** Exercise 3: the one-point monad *)

(* C35: T S is the one-point set. *)
Example p475_c35_point_monad_obj (S : Sets) :
  fobj[PointAt (@terminal_obj Sets Sets_Terminal) ◯ Erase Sets] S
    = @terminal_obj Sets _ := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Riehl's K as her proof builds it, and L at the Kleisli resolution *)

Section RiehlEMComparison.

Context {C : Category} (T : C ⟶ C) `{H : @Monad C T}.

Notation KT := (@Kleisli C T H).

(* C36: EM_Comparison at the Kleisli adjunction forgets to K's functor on
   objects... *)
Example p475_c36_riehl_k_obj (c : C) :
  fobj[EM_Forget _ ◯ EM_Comparison (@Kleisli_Adjunction C T H)] c
    = fobj[EM_Forget T ◯ @Kleisli_EM C T H] c := eq_refl.

(* C37: ... and on arrows. *)
Example p475_c37_riehl_k_map (x y : C) (f : x ~{KT}~> y) :
  fmap[EM_Forget _ ◯ EM_Comparison (@Kleisli_Adjunction C T H)] f
    = fmap[EM_Forget T ◯ @Kleisli_EM C T H] f := eq_refl.

(* R11 *)
Fail Example p475_r11_riehl_k_codomain : KT ⟶ EilenbergMoore T :=
  EM_Comparison (@Kleisli_Adjunction C T H).

(* C38: its codomain is the algebras of the monad the Kleisli adjunction
   induces. *)
Example p475_c38_riehl_k_codomain :
  KT ⟶ @EilenbergMoore C (@Kleisli_Forget C T H ◯ @Kleisli_Free C T H)
         (Adjunction_Induced_Monad (@Kleisli_Adjunction C T H)) :=
  EM_Comparison (@Kleisli_Adjunction C T H).

(* C39: its structure map at c is μ ∘ T id. *)
Example p475_c39_riehl_k_alg (c : C) :
  t_alg[`2 (fobj[EM_Comparison (@Kleisli_Adjunction C T H)] c)]
    = @join C T H c ∘ fmap[T] (@id C (T c)) := eq_refl.

(* R12 *)
Fail Example p475_r12_riehl_k_alg_join (c : C) :
  t_alg[`2 (fobj[EM_Comparison (@Kleisli_Adjunction C T H)] c)]
    = @join C T H c := eq_refl.

(* C40: the structure map is μ up to ≈. *)
Definition p475_c40_riehl_k_alg_join (c : C) :
  t_alg[`2 (fobj[EM_Comparison (@Kleisli_Adjunction C T H)] c)]
    ≈ @join C T H c := EM_Comparison_Kleisli_alg_join T c.

(* R13 *)
Fail Example p475_r13_l_at_kleisli : KT ⟶ KT :=
  Kleisli_Comparison (@Kleisli_Adjunction C T H).

(* C41: L at the Kleisli resolution of T goes out of the Kleisli category of
   the monad that resolution induces. *)
Example p475_c41_l_at_kleisli :
  @Kleisli C (@Kleisli_Forget C T H ◯ @Kleisli_Free C T H)
      (Adjunction_Induced_Monad (@Kleisli_Adjunction C T H)) ⟶ KT :=
  Kleisli_Comparison (@Kleisli_Adjunction C T H).

End RiehlEMComparison.

(* ------------------------------------------------------------------------ *)
(** ** Uniqueness from the strict triangles *)

Section UniqueStrict.

Context {X A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).

(* C42: the strict triangles L delivers satisfy the hypotheses of
   [Kleisli_Comparison_unique_of_strict] at L0 := L, coh at eq_refl. *)
Definition p475_c42_unique_of_strict_at_l :
  @equiv _ (@Functor_StrictEq_Setoid _ A) (Kleisli_Comparison Adj)
    (Kleisli_Comparison Adj) :=
  Kleisli_Comparison_unique_of_strict Adj (Kleisli_Comparison Adj)
    (Kleisli_Comparison_Free_strict Adj)
    (Kleisli_Comparison_Forget_strict Adj) (fun x => eq_refl).

End UniqueStrict.

(* ------------------------------------------------------------------------ *)
(** ** Guard: every constant of the two targets, by name *)

Check @Category.Monad.Kleisli.Comparison.Restricted_Left_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Restricted_Left_obligation_2.
Check @Category.Monad.Kleisli.Comparison.Restricted_Left_obligation_3.
Check @Category.Monad.Kleisli.Comparison.Restricted_Left.
Check @Category.Monad.Kleisli.Comparison.Restricted_Right.
Check @Category.Monad.Kleisli.Comparison.Restricted_adj_iso_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Restricted_adj_iso_obligation_2.
Check @Category.Monad.Kleisli.Comparison.Restricted_adj_iso_obligation_3.
Check @Category.Monad.Kleisli.Comparison.Restricted_adj_iso_obligation_4.
Check @Category.Monad.Kleisli.Comparison.Restricted_adj_iso.
Check @Category.Monad.Kleisli.Comparison.Restricted_Adjunction.
Check @Category.Monad.Kleisli.Comparison.Restricted_monad_obj.
Check @Category.Monad.Kleisli.Comparison.Restricted_monad_map.
Check @Category.Monad.Kleisli.Comparison.Restricted_unit_agrees.
Check @Category.Monad.Kleisli.Comparison.Restricted_join_agrees.
Check @Category.Monad.Kleisli.Comparison.Restricted_Monad_agrees.
Check @Category.Monad.Kleisli.Comparison.Restricted_Monad_agrees_iso.
Check @Category.Monad.Kleisli.Comparison.Restricted_Monad_to.
Check @Category.Monad.Kleisli.Comparison.Restricted_Monad_from.
Check @Category.Monad.Kleisli.Comparison.Restricted_Monad_iso.
Check @Category.Monad.Kleisli.Comparison.Restricted_Monad_iso_to.
Check @Category.Monad.Kleisli.Comparison.Restricted_Monad_iso_from.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_fmap_id.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_fmap_comp.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_obligation_2.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_obligation_3.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_obj.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_map.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_map_counit.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Forget.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Forget_iso.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Free.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Free_iso.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Forget_strict.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Forget_strict_obj.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Free_strict.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Free_strict_obj.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Full_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Full.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Faithful_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Faithful.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_unique_map.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_unique.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_unique_strict.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_unique_of_strict.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Squares_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Squares_obligation_2.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Squares.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Squares_unit.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Map.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Squares_of.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Squares_of_unit.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_unique_via_map.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Restrict_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Restrict_obligation_2.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Restrict_obligation_3.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Restrict.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Restrict_Full_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Restrict_Full.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Restrict_Faithful_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Restrict_Faithful.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Restrict_ESO.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Restrict_Equivalence.
Check @Category.Monad.Kleisli.Comparison.Restricted_Left_Image_obj.
Check @Category.Monad.Kleisli.Comparison.Restricted_Left_Image_map.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_is_ImageTo_obj.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_is_ImageTo_map.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_incl_obj.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_incl_map.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_surjective.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_surjective_obj.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_pick.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_Equivalence.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_AdjointEquivalence.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_injective.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_inv_left.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_inv_right_obj.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_inv_right.
Check @Category.Monad.Kleisli.Comparison.Kleisli_Comparison_Image_StrictIso.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_obligation_2.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_obligation_3.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_obj.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_obj_free.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_map.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_Forget_map.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_is_transpose.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_Full_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_Full.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_Faithful_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_Faithful.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_Image.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_Image_Full_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_Image_Full.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_Image_Faithful_obligation_1.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_Image_Faithful.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_Image_surjective.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_Image_Equivalence.
Check @Category.Monad.Kleisli.Comparison.EveryAlgebraFree.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_equivalence_iff.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_is_comparison_obj.
Check @Category.Monad.Kleisli.Comparison.Kleisli_EM_is_comparison_map.
Check @Category.Monad.Kleisli.Comparison.EM_Comparison_Kleisli_obj.
Check @Category.Monad.Kleisli.Comparison.EM_Comparison_Kleisli_map.
Check @Category.Monad.Kleisli.Comparison.EM_Comparison_Kleisli_alg.
Check @Category.Monad.Kleisli.Comparison.EM_Comparison_Kleisli_alg_join.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_FX.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_FX_full.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_FX_skeletal.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_adj.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_monad_obj.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_empty.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_one.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_distinct.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_F_not_injective.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_L_not_injective.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_surjective.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_equivalence.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_not_skeletal.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_not_iso.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_FX_pick.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_FX_equivalence.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_FX_not_iso.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_every_algebra_free.
Check @Category.Monad.Kleisli.Comparison.Examples.kleisli_point_K_equivalence.
