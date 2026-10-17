Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Concrete.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Adjunction.SAFT.

Generalizable All Variables.

(*
 nLab:  https://ncatlab.org/nlab/show/separator
 nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Under [Untruncate]: truth values in [Prop] *)

Definition Sets_Cogenerator_untruncate@{c o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : Cogenerator@{c so o} Sets@{o so}.
Proof.
  refine (@Build_Cogenerator Sets@{o so} unit
            (fun _ => Powerset_Prop_truth@{o}) _).
  intros x y f g H a.
  pose proof (H tt (Powerset_Prop_singleton_pred@{o} (f a)) a) as Ha.
  simpl in Ha.
  apply U.
  exact (proj1 Ha (Powerset_squash_intro@{o} (reflexivity (f a)))).
Defined.

Example sets_cogenerator_untruncate_obj@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  cog_obj (Sets_Cogenerator_untruncate U : Cogenerator Sets@{o so}) tt
    = Powerset_Prop_truth@{o} := eq_refl.

(** ** Under [IEM]: truth values in [poly_bool] *)

(* The characteristic map of the point [y0], decided by [E]. *)
Definition sets_bool_char@{o so +| o < so +} {Y : SetoidObject@{o o}}
  (E : IEM@{o}) (y0 : carrier Y) : Y ~{Sets@{o so}}~> BoolSetoid@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier Y) (is_setoid Y) poly_bool@{o} (is_setoid BoolSetoid@{o})
       (fun b => match E (@equiv _ (is_setoid Y) y0 b) with
                 | Datatypes.inl _ => ptrue@{o}
                 | Datatypes.inr _ => pfalse@{o}
                 end) _).
  intros b b' Hbb'; simpl.
  destruct (E (y0 ≈ b)) as [h|n], (E (y0 ≈ b')) as [h'|n']; try reflexivity.
  - destruct (n' (transitivity h Hbb')).
  - destruct (n (transitivity h' (symmetry Hbb'))).
Defined.

Definition Sets_Cogenerator_IEM@{c o so +| o < so +}
  (E : IEM@{o}) : Cogenerator@{c so o} Sets@{o so}.
Proof.
  refine (@Build_Cogenerator Sets@{o so} unit (fun _ => BoolSetoid@{o}) _).
  intros x y f g H a.
  pose proof (H tt (sets_bool_char E (f a)) a) as Ha.
  simpl in Ha.
  destruct (E (f a ≈ f a)) as [_|n]; [|destruct (n (reflexivity _))].
  destruct (E (f a ≈ g a)) as [h|_]; [exact h|discriminate Ha].
Defined.

Example sets_cogenerator_IEM_obj@{o so +| o < so +} (E : IEM@{o}) :
  cog_obj (Sets_Cogenerator_IEM E : Cogenerator Sets@{o so}) tt
    = BoolSetoid@{o} := eq_refl.

(** ** Unconditionally, but large: every object tested by its identity *)

Definition Sets_Cogenerator_large@{c o so +| o < so, o < c +} :
  Cogenerator@{c so o} Sets@{o so}.
Proof.
  refine (@Build_Cogenerator Sets@{o so} SetoidObject@{o o} (fun Y => Y) _).
  intros x y f g H a.
  exact (H y (@id Sets@{o so} y) a).
Defined.

(** ** The condition is genuine *)

(* A family of copies of the terminal object never cogenerates [Sets]:
   every two arrows into it agree, while the identity and negation of the
   two-element setoid differ. *)
Lemma Sets_terminal_not_cogenerates@{c o so +| o < so +} (I : Type@{c})
  (H : ∀ (x y : SetoidObject@{o o}) (f g : x ~{Sets@{o so}}~> y),
         (∀ (j : I)
            (k : y ~{Sets@{o so}}~> @terminal_obj Sets@{o so} Sets_Terminal),
            k ∘ f ≈ k ∘ g) → f ≈ g) : False.
Proof.
  apply Sets_two_arrows.
  apply H; intros j k.
  exact (@one_unique Sets@{o so} Sets_Terminal _ _ _).
Qed.
