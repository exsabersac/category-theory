(*
   本文件为测试：ProbeMonadicity469。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Identity.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Instance.Top.Monadicity.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Monadicity.TypeValued.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Construction.Reflective.Monadic.
Require Import Category.Instance.Pos.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Pos.Monadicity.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** Monad/Identity.v *)

(* C5: 函子 [IdMonad C] 恒等 对象. （已译） *)
Example p469_c5_id_fobj@{o h | +} (C : Category@{o h h}) (x : C) :
  @fobj C C Id[C] x = x := eq_refl.

(* C6: and on arrows. *)
Example p469_c6_id_fmap@{o h | +} (C : Category@{o h h}) (x y : C)
  (f : x ~> y) : @fmap C C Id[C] x y f = f := eq_refl.

(* C7: its unit is [id]. *)
Example p469_c7_id_ret@{o h | +} (C : Category@{o h h}) (x : C) :
  @ret C Id[C] (IdMonad@{o h} C) x = @id C x := eq_refl.

(* C8: its multiplication is [id]. *)
Example p469_c8_id_join@{o h | +} (C : Category@{o h h}) (x : C) :
  @join C Id[C] (IdMonad@{o h} C) x = @id C x := eq_refl.

(* C9: both legs unit 同构 at algebra [id]. （已译） *)
Example p469_c9_em_unit_legs@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h})
  (X : @EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C)) :
  (@t_alg_hom _ _ _ _ _ _ _ (to (IdMonad_EM_unit_iso@{o h s e} C X)),
   @t_alg_hom _ _ _ _ _ _ _ (from (IdMonad_EM_unit_iso@{o h s e} C X)))
    = (@id C (`1 X), @id C (`1 X)) := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** Instance/Top/Monadicity.v: induced 单子 （已译） *)

(* 相关说明。 （已译） *)
Example p469_c1_fobj_field@{o so s | o < so, o < s +} :
  @fobj _ _ PDiscT@{o so s} = @fobj _ _ Id[Sets@{o so}] := eq_refl.

(* C2: their [fmap] fields. *)
Example p469_c2_fmap_field@{o so s | o < so, o < s +} :
  @fmap _ _ PDiscT@{o so s} = @fmap _ _ Id[Sets@{o so}] := eq_refl.

(* C10: PForget ◯ PDisc is the identity on objects. *)
Example p469_c10_T_fobj@{o so s | o < so, o < s +} (x : Sets@{o so}) :
  fobj[PForget@{o so} ◯ PDisc@{o so}] x = x := eq_refl.

(* C11: and on arrows. *)
Example p469_c11_T_fmap@{o so s | o < so, o < s +} (x y : Sets@{o so})
  (f : x ~> y) : fmap[PForget@{o so} ◯ PDisc@{o so}] f = f := eq_refl.

(* C12: unit 伴随 恒等箭头. （已译） *)
Example p469_c12_unit@{o so u u0 | o < so, o < u +} (x : Sets@{o so}) :
  @Category.Theory.Adjunction.unit _ _ _ _ PDisc_PForget@{o so u u0} x
    = @id Sets@{o so} x := eq_refl.

(* C13: counit at space 恒等 points. （已译） *)
Example p469_c13_counit@{o so u u0 | o < so, o < u +}
  (X : PTopCat@{o so}) :
  pmap (@Category.Theory.Adjunction.counit _ _ _ _
          PDisc_PForget@{o so u u0} X) = setoid_morphism_id := eq_refl.

(* C14: unit induced 单子 [id]. （已译） *)
Example p469_c14_ret@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) :
  @ret _ _ (@Adjunction_Induced_Monad _ _ _ _ PDisc_PForget@{o so u u0}) x
    = @id Sets@{o so} x := eq_refl.

(* C15: its multiplication is [id]. *)
Example p469_c15_join@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) :
  @join _ _ (@Adjunction_Induced_Monad _ _ _ _ PDisc_PForget@{o so u u0}) x
    = @id Sets@{o so} x := eq_refl.

(* C37: unit multiplication, functions, those the
 恒等 单子. （已译） *)
Example p469_c37_monad_fields@{o so s u u0 | o < so, o < s, o < u +} :
  (@ret _ _ (@Adjunction_Induced_Monad _ _ _ _ PDisc_PForget@{o so u u0}),
   @join _ _ (@Adjunction_Induced_Monad _ _ _ _ PDisc_PForget@{o so u u0}))
    = ((fun x : Sets@{o so} => @id Sets@{o so} x),
       (fun x : Sets@{o so} => @id Sets@{o so} x)) := eq_refl.

(* R1 *)
Fail Example p469_r1_functor_eq@{o so s | o < so, o < s +} :
  PDiscT@{o so s} = Id[Sets@{o so}] := eq_refl.

(* R1a *)
Fail Example p469_r1a_fmap_respects@{o so s | o < so, o < s +} :
  @fmap_respects _ _ PDiscT@{o so s} = @fmap_respects _ _ Id[Sets@{o so}]
  := eq_refl.

(* R1b *)
Fail Example p469_r1b_fmap_id@{o so s | o < so, o < s +} :
  @fmap_id _ _ PDiscT@{o so s} = @fmap_id _ _ Id[Sets@{o so}] := eq_refl.

(* R1c *)
Fail Example p469_r1c_fmap_comp@{o so s | o < so, o < s +} :
  @fmap_comp _ _ PDiscT@{o so s} = @fmap_comp _ _ Id[Sets@{o so}]
  := eq_refl.

(* C36: at Leibniz setoid [bool], body standard
 library's obligation behind R1a, transitivity after reflexivity,
 converts 论元. （已译） *)
Example p469_c36_unfolded_bool@{o so | o < so +} :
  (fun (x0 y0 : bool_setoid_object@{o o} ~{Sets@{o so}}~>
                  bool_setoid_object@{o o})
       (X : ∀ x1 : bool, x0 x1 ≈ y0 x1) (x2 : bool) =>
     @transitivity _ _ _ (x0 x2) (y0 x2) (y0 x2) (X x2)
       (@reflexivity _ _ _ (y0 x2)))
  = (fun (x0 y0 : bool_setoid_object@{o o} ~{Sets@{o so}}~>
                    bool_setoid_object@{o o})
         (X : ∀ x1 : bool, x0 x1 ≈ y0 x1) (x2 : bool) => X x2) := eq_refl.

(* R13 *)
Fail Example p469_r13_unfolded_variable@{o so | o < so +} :
  (fun (x y : Sets@{o so}) (x0 y0 : x ~> y) (X : ∀ x1 : x, x0 x1 ≈ y0 x1)
       (x2 : x) =>
     @transitivity _ _ _ (x0 x2) (y0 x2) (y0 x2) (X x2)
       (@reflexivity _ _ _ (y0 x2)))
  = (fun (x y : Sets@{o so}) (x0 y0 : x ~> y) (X : ∀ x1 : x, x0 x1 ≈ y0 x1)
         (x2 : x) => X x2) := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** Instance/Top/Monadicity.v: 同构 [Monads Sets] （已译） *)

(* C16: both morphisms of monads have identity components. *)
Example p469_c16_hom_components@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) :
  (transform[mh_transform disc_id_hom@{o so s u u0}] x,
   transform[mh_transform id_disc_hom@{o so s u u0}] x)
    = (@id Sets@{o so} x, @id Sets@{o so} x) := eq_refl.

(* C17: so have two legs 同构. （已译） *)
Example p469_c17_iso_components@{o so s u u0 m1 m2 |
  o < so, o < s, o < u, so <= m1, o <= m1, so <= m2, o <= m2 +}
  (x : Sets@{o so}) :
  (transform[mh_transform (to disc_id_iso@{o so s u u0 m1 m2})] x,
   transform[mh_transform (from disc_id_iso@{o so s u u0 m1 m2})] x)
    = (@id Sets@{o so} x, @id Sets@{o so} x) := eq_refl.

(* R3 *)
Fail Example p469_r3_monad_eq@{o so s u u0 | o < so, o < s, o < u +} :
  existT (fun T : Sets@{o so} ⟶ Sets@{o so} => @Monad Sets@{o so} T)
    PDiscT@{o so s} PDiscMonad@{o so s u u0}
  = existT (fun T : Sets@{o so} ⟶ Sets@{o so} => @Monad Sets@{o so} T)
    Id[Sets@{o so}] (IdMonad@{so o} Sets@{o so}) := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** Instance/Top/Monadicity.v: comparison 函子 （已译） *)

(* 相关说明。 （已译） *)
Example p469_c3_forget_fobj_field@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  @fobj _ _ (EM_Forget _ ◯ PDiscK@{o so s u u0 e}) = @fobj _ _ PForget@{o so}
  := eq_refl.

(* C4: their [fmap] fields. *)
Example p469_c4_forget_fmap_field@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  @fmap _ _ (EM_Forget _ ◯ PDiscK@{o so s u u0 e}) = @fmap _ _ PForget@{o so}
  := eq_refl.

(* C18: the carrier of K X is PForget X. *)
Example p469_c18_forget_obj@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X : PTopCat@{o so}) :
  `1 (fobj[EM_Comparison PDisc_PForget@{o so u u0}] X) = fobj[PForget@{o so}] X
  := eq_refl.

(* C19: the underlying arrow of K f is PForget f. *)
Example p469_c19_forget_map@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X Y : PTopCat@{o so}) (f : X ~> Y) :
  t_alg_hom[fmap[EM_Comparison PDisc_PForget@{o so u u0}] f]
    = fmap[PForget@{o so}] f := eq_refl.

(* C20: the object equation of [PDiscK_forget_strict] IS [eq_refl]. *)
Example p469_c20_strict_obj@{o so s u u0 e a b |
  o < so, o < s, o < u, so <= e, o < b, so <= a, o <= a +}
  (X : PTopCat@{o so}) :
  `1 PDiscK_forget_strict@{o so s u u0 e a b} X = eq_refl := eq_refl.

(* C38: structure map K X 恒等 setoid 态射. （已译） *)
Example p469_c38_K_alg@{o so s u u0 e | o < so, o < s, o < u, so <= e +}
  (X : PTopCat@{o so}) :
  t_alg[`2 (fobj[EM_Comparison PDisc_PForget@{o so u u0}] X)]
    = @setoid_morphism_id (pt_carrier X) := eq_refl.

(* R2 *)
Fail Example p469_r2_forget_eq@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  EM_Forget _ ◯ PDiscK@{o so s u u0 e} = PForget@{o so} := eq_refl.

(* R2a *)
Fail Example p469_r2a_fmap_respects@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  @fmap_respects _ _ (EM_Forget _ ◯ PDiscK@{o so s u u0 e})
    = @fmap_respects _ _ PForget@{o so} := eq_refl.

(* R2b *)
Fail Example p469_r2b_fmap_id@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  @fmap_id _ _ (EM_Forget _ ◯ PDiscK@{o so s u u0 e})
    = @fmap_id _ _ PForget@{o so} := eq_refl.

(* R2c *)
Fail Example p469_r2c_fmap_comp@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  @fmap_comp _ _ (EM_Forget _ ◯ PDiscK@{o so s u u0 e})
    = @fmap_comp _ _ PForget@{o so} := eq_refl.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Example p469_c39_K_free_parts@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X : PTopCat@{o so}) :
  (`1 (fobj[PDiscK@{o so s u u0 e}] X),
   t_alg[`2 (fobj[PDiscK@{o so s u u0 e}] X)])
    = (`1 (fobj[@EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
                 PDiscMonad@{o so s u u0} ◯ PForget@{o so}] X),
       t_alg[`2 (fobj[@EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
                       PDiscMonad@{o so s u u0} ◯ PForget@{o so}] X)])
  := eq_refl.

(* R14 *)
Fail Example p469_r14_K_free_obj@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X : PTopCat@{o so}) :
  fobj[PDiscK@{o so s u u0 e}] X
    = fobj[@EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
             PDiscMonad@{o so s u u0} ◯ PForget@{o so}] X := eq_refl.

(* C21: KI after forgetful 函子 PForget 对象 arrows. （已译） *)
Example p469_c21_KI_forget@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X Y : PTopCat@{o so}) (f : X ~> Y) :
  (`1 (fobj[PDiscKI@{o so s u u0 e}] X),
   t_alg_hom[fmap[PDiscKI@{o so s u u0 e}] f])
    = (fobj[PForget@{o so}] X, fmap[PForget@{o so}] f) := eq_refl.

(* C22: structure map KI X 恒等 function. （已译） *)
Example p469_c22_KI_alg@{o so s u u0 e | o < so, o < s, o < u, so <= e +}
  (X : PTopCat@{o so}) (x : X) :
  t_alg[`2 (fobj[mh_EM@{so o e s} id_disc_hom@{o so s u u0}
                   ◯ EM_Comparison PDisc_PForget@{o so u u0}] X)] x = x
  := eq_refl.

(* R15 *)
Example p469_r15_KI_alg_setoid@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X : PTopCat@{o so}) :
  t_alg[`2 (fobj[PDiscKI@{o so s u u0 e}] X)] = setoid_morphism_id
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* C23: 含入 first projection 对象. （已译） *)
Example p469_c23_incl_fobj@{o so | o < so +} (X : PropSets@{o so}) :
  fobj[PropSets_Incl@{o so}] X = projT1 X := eq_refl.

(* C40: and on arrows. *)
Example p469_c40_incl_fmap@{o so | o < so +} (X Y : PropSets@{o so})
  (f : X ~{PropSets@{o so}}~> Y) :
  fmap[Incl@{so o so o so so} Sets@{o so} PropSets_sub@{o so}] f = `1 f
  := eq_refl.

(* C41: [PropSets_lift F P] keeps F's object in its first component. *)
Example p469_c41_lift_obj@{co o so | o < so +}
  {C : Category@{co o o}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) (c : C) :
  projT1 (fobj[PropSets_lift@{co o o so} F P] c) = fobj[F] c := eq_refl.

(* C42: and F's arrow. *)
Example p469_c42_lift_map@{co o so | o < so +}
  {C : Category@{co o o}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) (x y : C) (f : x ~> y) :
  projT1 (fmap[PropSets_lift@{co o o so} F P] f) = fmap[F] f := eq_refl.

(* C24: unit reflection 恒等 function. （已译） *)
Example p469_c24_trunc_unit@{o so a | o < so +} (S : Sets@{o so}) :
  @Sets.morphism _ _ _ _
    (@Category.Theory.Adjunction.unit _ _ _ _
       PropSets_trunc_Incl@{o so a} S) = (fun x : carrier S => x)
  := eq_refl.

(* C43: so is its counit. *)
Example p469_c43_trunc_counit@{o so a | o < so +} (X : PropSets@{o so}) :
  @Sets.morphism _ _ _ _
    (projT1 (@Category.Theory.Adjunction.counit _ _ _ _
               PropSets_trunc_Incl@{o so a} X))
    = (fun x : carrier (projT1 X) => x) := eq_refl.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* C25: PropSets_Incl ◯ PosPForget is Pos_Forget on objects. *)
Example p469_c25_factor_obj@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (P : Pos@{po p0 p1 p2 p3 c}) :
  fobj[PropSets_Incl@{c so} ◯ PosPForget@{c so po p0 p1 p2 p3}] P
    = fobj[Pos_Forget@{po so p0 p2 p1 p3 c}] P := eq_refl.

(* C44: and on arrows, read on first projections. *)
Example p469_c44_factor_map@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +}
  (P Q : Pos@{po p0 p1 p2 p3 c}) (f : P ~{Pos@{po p0 p1 p2 p3 c}}~> Q) :
  projT1 (fmap[PosPForget@{c so po p0 p1 p2 p3}] f)
    = fmap[Pos_Forget@{po so p0 p2 p1 p3 c}] f := eq_refl.

(* R18 *)
Fail Example p469_r18_factor_eq@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} :
  PropSets_Incl@{c so} ◯ PosPForget@{c so po p0 p1 p2 p3}
    = Pos_Forget@{po so p0 p2 p1 p3 c} := eq_refl.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* C26: 单子 keeps setoid 对象. （已译） *)
Example p469_c26_TPosP_setoid@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (X : PropSets@{c so}) :
  projT1 (fobj[TPosP@{c so po p0 p1 p2 p3 s}] X) = projT1 X := eq_refl.

(* 相关说明。 （已译） *)
Example p469_c45_TPosP_fmap@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (X Y : PropSets@{c so})
  (f : X ~{PropSets@{c so}}~> Y) :
  projT1 (fmap[PosPForget@{c so po p0 p1 p2 p3}
               ◯ PosDiscP@{c so po p0 p1 p2 p3}] f) = projT1 f := eq_refl.

(* C34: its [PropEquiv] witness is recomputed as the two-way order. *)
Example p469_c34_TPosP_pequiv@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (X : PropSets@{c so}) (x y : carrier (projT1 X)) :
  @pequiv _ _ (projT2 (fobj[TPosP@{c so po p0 p1 p2 p3 s}] X)) x y
    = (@pequiv _ _ (projT2 X) x y /\ @pequiv _ _ (projT2 X) y x)
  := eq_refl.

(* C35: at a pair (S; P) the first components agree. *)
Example p469_c35_pair_setoid@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S : Sets@{c so}) (P : PropEquivObj@{so c c} S) :
  projT1 (fobj[TPosP@{c so po p0 p1 p2 p3 s}]
            (existT _ S P : PropSets@{c so})) = S := eq_refl.

(* C27: unit 恒等 function. （已译） *)
Example p469_c27_MPosP_ret@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (X : PropSets@{c so}) :
  projT1 (@ret _ _ MPosP@{c so po p0 p1 p2 p3 s a} X) = id := eq_refl.

(* C46: so is the multiplication. *)
Example p469_c46_MPosP_join@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (X : PropSets@{c so}) :
  projT1 (@join _ _ (Adjunction_Induced_Monad
                       PosDiscP_PosPForget@{c so po p0 p1 p2 p3 a}) X)
    = id := eq_refl.

(* C28: 态射 单子 恒等 单子 has 恒等
 components. （已译） *)
Example p469_c28_to_Id_component@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (X : PropSets@{c so}) :
  projT1 (transform[mh_transform MPosP_to_Id@{c so po p0 p1 p2 p3 s a}] X)
    = id := eq_refl.

(* C47: so has the one back. *)
Example p469_c47_Id_to_component@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (X : PropSets@{c so}) :
  projT1 (transform[id_to_TPosP@{c so po p0 p1 p2 p3 s}] X) = id
  := eq_refl.

(* R7 *)
Fail Example p469_r7_pair_obj@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S : Sets@{c so}) (P : PropEquivObj@{so c c} S) :
  fobj[TPosP@{c so po p0 p1 p2 p3 s}] (existT _ S P : PropSets@{c so})
    = (existT _ S P : PropSets@{c so}) := eq_refl.

(* R12 *)
Fail Example p469_r12_pequiv@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (X : PropSets@{c so}) (x y : carrier (projT1 X)) :
  @pequiv _ _ (projT2 (fobj[TPosP@{c so po p0 p1 p2 p3 s}] X)) x y
    = @pequiv _ _ (projT2 X) x y := eq_refl.

(* R20 *)
Fail Example p469_r20_variable_obj@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (X : PropSets@{c so}) :
  fobj[TPosP@{c so po p0 p1 p2 p3 s}] X = X := eq_refl.

(* R8 *)
Fail Example p469_r8_TPosP_eq@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} :
  TPosP@{c so po p0 p1 p2 p3 s} = Id[PropSets@{c so}] := eq_refl.

(* R9 *)
Fail Example p469_r9_monads_eq@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +} :
  @eq (obj[Monads@{so c m1 m2} PropSets@{c so}])
    (existT _ TPosP@{c so po p0 p1 p2 p3 s} MPosP@{c so po p0 p1 p2 p3 s a})
    (existT _ Id[PropSets@{c so}] (IdMonad@{so c} PropSets@{c so}))
  := eq_refl.

(* 相关说明。 （已译） *)
Example p469_c52_setoid_eta@{c | +} (S : SetoidObject@{c c}) :
  {| carrier := carrier S; is_setoid := is_setoid S |} = S := eq_refl.

(* R21 *)
Fail Example p469_r21_sigT_eta@{c so | c < so +} (X : PropSets@{c so}) :
  X = (existT _ (projT1 X) (projT2 X) : PropSets@{c so}) := eq_refl.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Example p469_c48_disc_le@{c so p0 p1 p2 p3 |
  c < so, Set < p2, p2 <= p0, p3 <= p1, c <= p0, c <= p1 +}
  (S : Sets@{c so}) (x y : carrier S) :
  pos_le (PosDiscPObj@{c so p0 p1 p2 p3} (PropSets_trunc@{c so} S)) x y
    = inhabited (x ≈ y) := eq_refl.

(* C32: [PosDisc] is [PosDiscP] after the reflector on objects. *)
Example p469_c32_PosDisc_obj@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S : Sets@{c so}) :
  fobj[PosDisc@{c so po p0 p1 p2 p3}] S
    = fobj[PosDiscP@{c so po p0 p1 p2 p3}] (fobj[PropSets_trunc@{c so}] S)
  := eq_refl.

(* C49: and on arrows. *)
Example p469_c49_PosDisc_map@{c so po p0 p1 p2 p3 |
  c < so, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S T : Sets@{c so}) (f : S ~{Sets@{c so}}~> T) :
  fmap[PosDisc@{c so po p0 p1 p2 p3}] f
    = PosDiscP_fmap@{c so p0 p1 p2 p3} (fmap[PropSets_trunc@{c so}] f)
  := eq_refl.

(* R19 *)
Fail Example p469_r19_PosDisc_eq@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} :
  PosDisc@{c so po p0 p1 p2 p3}
    = PosDiscP@{c so po p0 p1 p2 p3} ◯ PropSets_trunc@{c so} := eq_refl.

(* C29: 单子's 函子 reflection's 对象. （已译） *)
Example p469_c29_TPos_fobj@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S : Sets@{c so}) :
  fobj[TPos@{c so po p0 p1 p2 p3 s}] S
    = fobj[PropSets_Incl@{c so} ◯ PropSets_trunc@{c so}] S := eq_refl.

(* C50: and on arrows. *)
Example p469_c50_TPos_fmap@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S T : Sets@{c so}) (f : S ~{Sets@{c so}}~> T) :
  fmap[Pos_Forget@{po so p0 p2 p1 p3 c} ◯ PosDisc@{c so po p0 p1 p2 p3}] f
    = fmap[PropSets_Incl@{c so} ◯ PropSets_trunc@{c so}] f := eq_refl.

(* R16 *)
Fail Example p469_r16_TPos_trunc_eq@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} :
  TPos@{c so po p0 p1 p2 p3 s} = PropSets_Incl@{c so} ◯ PropSets_trunc@{c so}
  := eq_refl.

(* R17 *)
Fail Example p469_r17_trunc_monads_eq@{c so po p0 p1 p2 p3 s a r m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +} :
  @eq (obj[Monads@{so c m1 m2} Sets@{c so}])
    (existT _ TPos@{c so po p0 p1 p2 p3 s} MPos@{c so po p0 p1 p2 p3 s a})
    (existT _ (PropSets_Incl@{c so} ◯ PropSets_trunc@{c so})
       (Adjunction_Induced_Monad PropSets_trunc_Incl@{c so r})) := eq_refl.

(* C30: the monad keeps the carrier. *)
Example p469_c30_TPos_carrier@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S : Sets@{c so}) :
  carrier (fobj[TPos@{c so po p0 p1 p2 p3 s}] S) = carrier S := eq_refl.

(* C33: its ≈ is the truncation of S's. *)
Example p469_c33_TPos_equiv@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S : Sets@{c so}) (x y : carrier S) :
  @equiv _ (is_setoid (fobj[TPos@{c so po p0 p1 p2 p3 s}] S)) x y
    = inhabited (x ≈ y) := eq_refl.

(* R4 *)
Fail Example p469_r4_TPos_obj@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S : Sets@{c so}) :
  fobj[TPos@{c so po p0 p1 p2 p3 s}] S = S := eq_refl.

(* R11 *)
Fail Example p469_r11_TPos_equiv@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S : Sets@{c so}) (x y : carrier S) :
  @equiv _ (is_setoid (fobj[TPos@{c so po p0 p1 p2 p3 s}] S)) x y
    = (x ≈ y) := eq_refl.

(* R5 *)
Fail Example p469_r5_TPos_eq@{c so po p0 p1 p2 p3 s |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} :
  TPos@{c so po p0 p1 p2 p3 s} = Id[Sets@{c so}] := eq_refl.

(* C31: unit 恒等 function. （已译） *)
Example p469_c31_MPos_ret@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S : Sets@{c so}) :
  @Sets.morphism _ _ _ _ (@ret _ _ MPos@{c so po p0 p1 p2 p3 s a} S)
    = (fun x : carrier S => x) := eq_refl.

(* C51: so is the multiplication. *)
Example p469_c51_MPos_join@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S : Sets@{c so}) :
  @Sets.morphism _ _ _ _
    (@join _ _ (Adjunction_Induced_Monad
                  PosDisc_Pos_Forget@{c so po p0 p1 p2 p3 a}) S)
    = (fun x : carrier S => x) := eq_refl.

(* R6 *)
Fail Example p469_r6_MPos_ret@{c so po p0 p1 p2 p3 s a |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1,
  c <= p0, c <= p1 +} (S : Sets@{c so}) :
  @ret _ _ MPos@{c so po p0 p1 p2 p3 s a} S = id := eq_refl.

(* R10 *)
Fail Definition p469_r10_naive_elim@{c so | c < so +} :
  SetsTruncElim@{c so} :=
  fun S x y H => match H with inhabits h => h end.

(* ------------------------------------------------------------------------ *)
(* * ** The guard: every 常值 five targets （已译） *)

Check @Category.Monad.Identity.IdMonad.
Check @Category.Monad.Identity.IdMonad_fobj.
Check @Category.Monad.Identity.IdMonad_fmap.
Check @Category.Monad.Identity.IdMonad_ret.
Check @Category.Monad.Identity.IdMonad_join.
Check @Category.Monad.Identity.IdMonad_alg_id.
Check @Category.Monad.Identity.IdMonad_EM_counit.
Check @Category.Monad.Identity.IdMonad_EM_unit_iso.
Check @Category.Monad.Identity.IdMonad_EM_unit_iso_id.
Check @Category.Monad.Identity.IdMonad_EM_unit.
Check @Category.Monad.Identity.IdMonad_EM_equivalence.
Check @Category.Instance.Top.Monadicity.PDiscT.
Check @Category.Instance.Top.Monadicity.PDiscMonad.
Check @Category.Instance.Top.Monadicity.PDiscT_fobj.
Check @Category.Instance.Top.Monadicity.PDiscT_fmap.
Check @Category.Instance.Top.Monadicity.PDisc_PForget_unit.
Check @Category.Instance.Top.Monadicity.PDisc_PForget_counit.
Check @Category.Instance.Top.Monadicity.PDiscMonad_ret.
Check @Category.Instance.Top.Monadicity.PDiscMonad_join.
Check @Category.Instance.Top.Monadicity.PDiscT_fields.
Check @Category.Instance.Top.Monadicity.PDiscMonad_fields.
Check @Category.Instance.Top.Monadicity.disc_to_id.
Check @Category.Instance.Top.Monadicity.id_to_disc.
Check @Category.Instance.Top.Monadicity.disc_id_hom.
Check @Category.Instance.Top.Monadicity.id_disc_hom.
Check @Category.Instance.Top.Monadicity.disc_id_hom_component.
Check @Category.Instance.Top.Monadicity.id_disc_hom_component.
Check @Category.Instance.Top.Monadicity.disc_id_iso.
Check @Category.Instance.Top.Monadicity.PDiscK.
Check @Category.Instance.Top.Monadicity.PDiscK_forget_obj.
Check @Category.Instance.Top.Monadicity.PDiscK_forget_map.
Check @Category.Instance.Top.Monadicity.PDiscK_alg.
Check @Category.Instance.Top.Monadicity.PDiscK_forget_strict.
Check @Category.Instance.Top.Monadicity.PDiscK_forget.
Check @Category.Instance.Top.Monadicity.PDiscMonad_alg_id.
Check @Category.Instance.Top.Monadicity.EM_PDisc_counit.
Check @Category.Instance.Top.Monadicity.EM_PDisc_unit_iso.
Check @Category.Instance.Top.Monadicity.EM_PDisc_unit.
Check @Category.Instance.Top.Monadicity.EM_PDisc_equivalence.
Check @Category.Instance.Top.Monadicity.PDiscK_free_iso.
Check @Category.Instance.Top.Monadicity.PDiscK_free.
Check @Category.Instance.Top.Monadicity.PDiscKI.
Check @Category.Instance.Top.Monadicity.PDiscKI_forget_obj.
Check @Category.Instance.Top.Monadicity.PDiscKI_forget_map.
Check @Category.Instance.Top.Monadicity.PDiscKI_alg.
Check @Category.Instance.Top.Monadicity.pbool_to_indisc.
Check @Category.Instance.Top.Monadicity.no_pindisc_to_bool.
Check @Category.Instance.Top.Monadicity.PForget_not_Full.
Check @Category.Instance.Top.Monadicity.PForget_not_ReflectsIsos.
Check @Category.Instance.Top.Monadicity.PDiscK_not_Full.
Check @Category.Instance.Top.Monadicity.PDiscK_not_Equivalence.
Check @Category.Instance.Top.Monadicity.PDiscKI_not_Full.
Check @Category.Instance.Top.Monadicity.PDiscKI_not_Equivalence.
Check @Category.Instance.Top.Monadicity.PDiscK_not_Cat_iso.
Check @Category.Instance.Top.Monadicity.PForget_not_Monadic.
Check @Category.Instance.Top.Monadicity.TypeValued.top_bool_to_indisc.
Check @Category.Instance.Top.Monadicity.TypeValued.no_top_indisc_to_bool.
Check @Category.Instance.Top.Monadicity.TypeValued.Top_Forget_not_Monadic.
Check @Category.Instance.Sets.Propositional.Full.PropSets_sub.
Check @Category.Instance.Sets.Propositional.Full.PropSets.
Check @Category.Instance.Sets.Propositional.Full.PropSets_Incl.
Check @Category.Instance.Sets.Propositional.Full.PropSets_Incl_fobj.
Check @Category.Instance.Sets.Propositional.Full.PropSets_Incl_fmap.
Check @Category.Instance.Sets.Propositional.Full.PropSets_Full.
Check @Category.Instance.Sets.Propositional.Full.PropSets_Incl_Full.
Check @Category.Instance.Sets.Propositional.Full.PropSets_Incl_Faithful.
Check @Category.Instance.Sets.Propositional.Full.PropSets_LocallyPropositional.
Check @Category.Instance.Sets.Propositional.Full.PropSets_lift.
Check @Category.Instance.Sets.Propositional.Full.PropSets_lift_obj.
Check @Category.Instance.Sets.Propositional.Full.PropSets_lift_map.
Check @Category.Instance.Sets.Propositional.Full.PropSets_lift_Incl.
Check @Category.Instance.Sets.Propositional.Full.trunc_equivalence.
Check @Category.Instance.Sets.Propositional.Full.trunc_setoid.
Check @Category.Instance.Sets.Propositional.Full.trunc_PropEquiv.
Check @Category.Instance.Sets.Propositional.Full.PropSets_trunc_obj.
Check @Category.Instance.Sets.Propositional.Full.PropSets_trunc.
Check @Category.Instance.Sets.Propositional.Full.trunc_transpose.
Check @Category.Instance.Sets.Propositional.Full.trunc_extend.
Check @Category.Instance.Sets.Propositional.Full.PropSets_trunc_iso_obligation_1.
Check @Category.Instance.Sets.Propositional.Full.PropSets_trunc_iso_obligation_2.
Check @Category.Instance.Sets.Propositional.Full.PropSets_trunc_iso_obligation_3.
Check @Category.Instance.Sets.Propositional.Full.PropSets_trunc_iso_obligation_4.
Check @Category.Instance.Sets.Propositional.Full.PropSets_trunc_iso.
Check @Category.Instance.Sets.Propositional.Full.PropSets_trunc_Incl.
Check @Category.Instance.Sets.Propositional.Full.PropSets_trunc_unit.
Check @Category.Instance.Sets.Propositional.Full.PropSets_trunc_counit.
Check @Category.Instance.Sets.Propositional.Full.PropSets_Reflective.
Check @Category.Instance.Sets.Propositional.Full.untr_of_choice.
Check @Category.Instance.Sets.Propositional.Full.choice_of_untr.
Check @Category.Instance.Sets.Propositional.Full.squash_rel.
Check @Category.Instance.Sets.Propositional.Full.squash_sym.
Check @Category.Instance.Sets.Propositional.Full.squash_trans.
Check @Category.Instance.Sets.Propositional.Full.SquashSetoid.
Check @Category.Instance.Pos.Monadicity.pos_PropEquiv.
Check @Category.Instance.Pos.Monadicity.PosPForget.
Check @Category.Instance.Pos.Monadicity.Pos_Forget_factor_obj.
Check @Category.Instance.Pos.Monadicity.Pos_Forget_factor_map.
Check @Category.Instance.Pos.Monadicity.Pos_Forget_factor.
Check @Category.Instance.Pos.Monadicity.PosDiscPObj.
Check @Category.Instance.Pos.Monadicity.PosDiscP_fmap.
Check @Category.Instance.Pos.Monadicity.PosDiscP.
Check @Category.Instance.Pos.Monadicity.posdiscP_from.
Check @Category.Instance.Pos.Monadicity.posdiscP_to.
Check @Category.Instance.Pos.Monadicity.posdiscP_iso_obligation_1.
Check @Category.Instance.Pos.Monadicity.posdiscP_iso_obligation_2.
Check @Category.Instance.Pos.Monadicity.posdiscP_iso_obligation_3.
Check @Category.Instance.Pos.Monadicity.posdiscP_iso_obligation_4.
Check @Category.Instance.Pos.Monadicity.posdiscP_iso.
Check @Category.Instance.Pos.Monadicity.PosDiscP_PosPForget.
Check @Category.Instance.Pos.Monadicity.TPosP.
Check @Category.Instance.Pos.Monadicity.MPosP.
Check @Category.Instance.Pos.Monadicity.TPosP_setoid.
Check @Category.Instance.Pos.Monadicity.TPosP_fmap.
Check @Category.Instance.Pos.Monadicity.TPosP_pequiv.
Check @Category.Instance.Pos.Monadicity.MPosP_ret.
Check @Category.Instance.Pos.Monadicity.MPosP_join.
Check @Category.Instance.Pos.Monadicity.TPosP_to_id.
Check @Category.Instance.Pos.Monadicity.id_to_TPosP.
Check @Category.Instance.Pos.Monadicity.MPosP_to_Id.
Check @Category.Instance.Pos.Monadicity.Id_to_MPosP.
Check @Category.Instance.Pos.Monadicity.MPosP_to_Id_component.
Check @Category.Instance.Pos.Monadicity.Id_to_MPosP_component.
Check @Category.Instance.Pos.Monadicity.MPosP_Id_iso.
Check @Category.Instance.Pos.Monadicity.PropSets_EM_Id_equivalence.
Check @Category.Instance.Pos.Monadicity.PosDiscObj.
Check @Category.Instance.Pos.Monadicity.PosDiscObj_le.
Check @Category.Instance.Pos.Monadicity.PosDisc.
Check @Category.Instance.Pos.Monadicity.PosDisc_obj.
Check @Category.Instance.Pos.Monadicity.PosDisc_map.
Check @Category.Instance.Pos.Monadicity.posdisc_from.
Check @Category.Instance.Pos.Monadicity.posdisc_to.
Check @Category.Instance.Pos.Monadicity.posdisc_iso_obligation_1.
Check @Category.Instance.Pos.Monadicity.posdisc_iso_obligation_2.
Check @Category.Instance.Pos.Monadicity.posdisc_iso_obligation_3.
Check @Category.Instance.Pos.Monadicity.posdisc_iso_obligation_4.
Check @Category.Instance.Pos.Monadicity.posdisc_iso.
Check @Category.Instance.Pos.Monadicity.PosDisc_Pos_Forget.
Check @Category.Instance.Pos.Monadicity.TPos.
Check @Category.Instance.Pos.Monadicity.MPos.
Check @Category.Instance.Pos.Monadicity.TPos_fobj.
Check @Category.Instance.Pos.Monadicity.TPos_fmap.
Check @Category.Instance.Pos.Monadicity.TPos_carrier.
Check @Category.Instance.Pos.Monadicity.TPos_equiv.
Check @Category.Instance.Pos.Monadicity.MPos_ret.
Check @Category.Instance.Pos.Monadicity.MPos_join.
Check @Category.Instance.Pos.Monadicity.TPos_to_trunc.
Check @Category.Instance.Pos.Monadicity.trunc_to_TPos.
Check @Category.Instance.Pos.Monadicity.MPos_to_trunc.
Check @Category.Instance.Pos.Monadicity.trunc_to_MPos.
Check @Category.Instance.Pos.Monadicity.MPos_trunc_iso.
Check @Category.Instance.Pos.Monadicity.id_to_TPos.
Check @Category.Instance.Pos.Monadicity.Id_to_MPos.
Check @Category.Instance.Pos.Monadicity.SetsTruncElim.
Check @Category.Instance.Pos.Monadicity.MPos_to_Id_trunc.
Check @Category.Instance.Pos.Monadicity.TPos_to_id.
Check @Category.Instance.Pos.Monadicity.MPos_to_Id.
Check @Category.Instance.Pos.Monadicity.MPos_Id_iso.
Check @Category.Instance.Pos.Monadicity.choice_setoid.
Check @Category.Instance.Pos.Monadicity.trunc_choice.
Check @Category.Instance.Pos.Monadicity.choice_trunc.
Check @Category.Instance.Pos.Monadicity.MPos_Id_iff.
Check @Category.Instance.Pos.Monadicity.all_PropEquiv_trunc.
Check @Category.Instance.Pos.Monadicity.trunc_all_PropEquiv.
Check @Category.Instance.Pos.Monadicity.any_adj_to_Id_trunc.
Check @Category.Instance.Pos.Monadicity.choice_of_IEM.
Check @Category.Instance.Pos.Monadicity.MPos_IEM_Id_iso.
Check @Category.Instance.Pos.Monadicity.bool_le_antisym.
Check @Category.Instance.Pos.Monadicity.BoolDiscPos.
Check @Category.Instance.Pos.Monadicity.BoolChainPos.
Check @Category.Instance.Pos.Monadicity.bool_disc_to_chain.
Check @Category.Instance.Pos.Monadicity.no_bool_chain_to_disc.
Check @Category.Instance.Pos.Monadicity.Pos_Forget_not_Full.
Check @Category.Instance.Pos.Monadicity.Pos_Forget_not_ReflectsIsos.
Check @Category.Instance.Pos.Monadicity.Pos_Forget_not_Monadic.
Check @Category.Instance.Pos.Monadicity.PosPForget_not_Monadic.
Check @Category.Instance.Pos.Monadicity.PropSets_Incl_Monadic.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Require Import Category.Instance.Sets.Classifier.OneLevel.

(* 相关说明。 （已译） *)
Example p469_c53_untr_iem_unfold@{c t | c < t +} :
  @eq Type@{t} Untruncate@{c}
    (∀ P : Type@{c}, (∀ Q : Prop, (P → Q) → Q) → P)
  /\ @eq Type@{t} IEM@{c} (∀ P : Type@{c}, P + (P → False))
  := conj eq_refl eq_refl.

(* C54: under OneLevel.v's [IEM] induced 单子 over [Sets] the
 恒等 单子, [MPos_IEM_Id_iso] route through
 [untruncate_of_IEM] [choice_of_untr]. （已译） *)
Definition p469_c54_iem_routes@{c so po p0 p1 p2 p3 s a m1 m2 |
  c < so, c < s, c < po, Set < p2, p1 <= po, p2 <= p0, p3 <= p1, c <= p0,
  c <= p1, so <= m1, c <= m1, so <= m2, c <= m2 +} (E : IEM@{c}) :=
  (MPos_IEM_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2} E,
   MPos_Id_iso@{c so po p0 p1 p2 p3 s a m1 m2}
     (choice_trunc@{c so}
        (choice_of_untr@{c} (untruncate_of_IEM@{c} E)))).

(* ------------------------------------------------------------------------ *)
(* * ** The 单子 Id ⊣ Id, measured at end （已译） *)

Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.Compose.
Require Import Category.Monad.Monadicity.Examples.

(* C55: 单子 Id ⊣ Id induces has unit multiplication [id]. （已译） *)
Example p469_c55_IdId_monad@{o h s a | h < s +} (C : Category@{o h h})
  (x : C) :
  (@ret _ _ (@Adjunction_Induced_Monad@{o h o h s a s} _ _ _ _
               (@Adjunction_Id@{s a o h} C)) x,
   @join _ _ (@Adjunction_Induced_Monad@{o h o h s a s} _ _ _ _
                (@Adjunction_Id@{s a o h} C)) x)
    = (@id C x, @id C x) := eq_refl.
