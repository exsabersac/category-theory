Require Import Category.Lib.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Structure.Generator.Dual.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Generator.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Sets.WellPowered.
Require Import Category.Instance.Sets.Cogenerator.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.InitialObject.

Generalizable All Variables.

(*
 nLab:  https://ncatlab.org/nlab/show/initial+object
 nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Sets^op *)

Definition setsop_comp@{o so +| o < so +} :
  @Complete@{o o o so} (Sets@{o so}^op) :=
  Complete_op_of_Cocomplete Sets_Cocomplete.

Definition setsop_cog@{c o so +| o < so +} :
  Cogenerator@{c so o} (Sets@{o so}^op) :=
  cog_of_gen Sets_Generator.

Definition setsop_point@{o so +| o < so +} :
  carrier (@cogen_prod (Sets@{o so}^op) setsop_comp setsop_cog).
Proof.
  exact (iprod_proj (cog_obj setsop_cog)
           (cogen_prod_limit setsop_comp setsop_cog) tt ttt).
Defined.

Definition setsop_L@{o so +| o < so +} :
  @SubObj (Sets@{o so}^op)
    (@cogen_prod (Sets@{o so}^op) setsop_comp setsop_cog).
Proof.
  unshelve refine
    (@Build_SubObj (Sets^op) (cogen_prod setsop_comp setsop_cog)
       (@terminal_obj Sets Sets_Terminal)
       (@one Sets Sets_Terminal (cogen_prod setsop_comp setsop_cog)) _).
  constructor; intros z g1 g2 H u.
  destruct u.
  exact (H setsop_point).
Defined.

Definition setsop_L_least@{o so +| o < so +}
  (v : @SubObj (Sets@{o so}^op)
         (@cogen_prod (Sets@{o so}^op) setsop_comp setsop_cog)) :
  sub_le setsop_L v.
Proof.
  exists (@one Sets Sets_Terminal (Subobject.sub_dom v)).
  intros p; exact eq_refl.
Defined.

Definition setsop_special_initial@{o so +| o < so +} :
  @Initial (Sets@{o so}^op) :=
  special_initial_object setsop_comp setsop_cog setsop_L
    (intersection_all_of_least setsop_L setsop_L_least).

Example setsop_special_obj@{o so +| o < so +} :
  @initial_obj (Sets@{o so}^op) setsop_special_initial
    = @terminal_obj Sets@{o so} Sets_Terminal := eq_refl.

Definition setsop_special_vs_known@{o so +| o < so +} :
  @initial_obj (Sets@{o so}^op) setsop_special_initial
    ≅[Sets@{o so}^op] @initial_obj (Sets@{o so}^op) Sets_Terminal :=
  initial_unique setsop_special_initial Sets_Terminal.

Definition setsop_terminal_IsInitialObj@{o so +| o < so +} :
  @IsInitialObj (Sets@{o so}^op) (@terminal_obj Sets@{o so} Sets_Terminal) :=
  special_initial_IsInitialObj setsop_comp setsop_cog setsop_L
    (intersection_all_of_least setsop_L setsop_L_least).

(** ** Sets, under Untruncate: the least subobject *)

Definition sets_special_initial_untruncate@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : @Initial Sets@{o so} :=
  special_initial_object Sets_Complete (Sets_Cogenerator_untruncate U)
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

Example sets_special_untruncate_obj@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_untruncate U)
    = @initial_obj Sets@{o so} Sets_Initial := eq_refl.

(** ** Sets, under Untruncate: the well-powered corollary *)

Definition sets_special_initial_wellpowered@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : @Initial Sets@{o so} :=
  special_initial_object_wellpowered (Sets_WellPowered_untruncate U)
    Sets_Complete (Sets_Cogenerator_untruncate U).

Example sets_special_wellpowered_obj@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_wellpowered U)
    = Subobject.sub_dom
        (complete_intersection Sets_Complete
           (wp_class_family
              (Sets_WellPowered_untruncate U
                 (cogen_prod Sets_Complete (Sets_Cogenerator_untruncate U)))
              (fun _ => True))) := eq_refl.

Definition sets_special_wellpowered_vs_known@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_wellpowered U)
    ≅ @initial_obj Sets@{o so} Sets_Initial :=
  initial_unique (sets_special_initial_wellpowered U) Sets_Initial.

Definition sets_special_wellpowered_empty@{o so +| Set < o, o < so +}
  (U : Untruncate@{o})
  (a : carrier
         (@initial_obj Sets@{o so} (sets_special_initial_wellpowered U))) :
  False :=
  match @zero Sets@{o so} (sets_special_initial_wellpowered U)
          (@initial_obj Sets@{o so} Sets_Initial) a with end.

(** ** Sets, under Untruncate: the book's blanket hypothesis *)

Definition Sets_HasClassIntersections_untruncate@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : HasClassIntersections Sets@{o so} :=
  fun X P HP => Sets_wellpowered_intersection U X P HP.

Definition sets_special_initial_book@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : @Initial Sets@{o so} :=
  special_initial_object_book Sets_Complete (Sets_Cogenerator_untruncate U)
    (Sets_HasClassIntersections_untruncate U).

Example sets_special_book_obj@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_book U)
    = Subobject.sub_dom
        (`1 (Sets_wellpowered_intersection U
               (cogen_prod Sets_Complete (Sets_Cogenerator_untruncate U))
               (fun _ => unit) (fun _ _ _ t => t))) := eq_refl.

Definition sets_special_book_vs_known@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_book U)
    ≅ @initial_obj Sets@{o so} Sets_Initial :=
  initial_unique (sets_special_initial_book U) Sets_Initial.

(** ** Sets, under IEM *)

Definition sets_special_initial_IEM@{o so +| o < so +}
  (E : IEM@{o}) : @Initial Sets@{o so} :=
  special_initial_object Sets_Complete (Sets_Cogenerator_IEM E)
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

Example sets_special_IEM_obj@{o so +| o < so +} (E : IEM@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_IEM E)
    = @initial_obj Sets@{o so} Sets_Initial := eq_refl.

Definition sets_special_initial_IEM_at_Set@{so +| Set < so +}
  (E : IEM@{Set}) : @Initial Sets@{Set so} :=
  sets_special_initial_IEM E.
