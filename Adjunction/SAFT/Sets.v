Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.SAFT.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * SAFT's covering datum is refutable at the identity of [Sets] *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Cantor%27s_theorem

   本文件给出集合相关实例或构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma SubobjectCover_Id_Sets_absurd@{r g w u c h cobj |
    Set < h, h < cobj, h < u +}
  (comp : @Complete@{r g h cobj} Sets@{h cobj})
  (G : Cogenerator@{g cobj h} Sets@{h cobj})
  (WP : ∀ x : Sets@{h cobj}, SubobjectIndex@{w cobj h} x) :
  SubobjectCover@{c w g u r cobj cobj h} (@Id Sets@{h cobj}) comp G WP →
  False.
Proof.
  intros cover.
  set (Q := cogen_prod comp G).
  (* The Prop-valued predicates on the carrier of [Q], compared pointwise
     by logical equivalence. *)
  unshelve epose (PQ := {| carrier := carrier Q → Prop;
                           is_setoid :=
                             {| equiv := fun A B : carrier Q → Prop =>
                                           ∀ a, iff (A a) (B a) |} |}
                  : obj[Sets]).
  { constructor.
    - intros A a; exact (conj (fun h => h) (fun h => h)).
    - intros A B H a; exact (conj (proj2 (H a)) (proj1 (H a))).
    - intros A B C0 H1 H2 a;
        exact (conj (fun h => proj1 (H2 a) (proj1 (H1 a) h))
                    (fun h => proj2 (H1 a) (proj2 (H2 a) h))). }
  destruct (SubobjectCover_Id_retract comp G WP cover PQ) as [i [s [t e]]].
  set (m := sub_dom (WP Q) i) in *.
  set (mono := sub_mono (WP Q) i).
  pose proof (snd (injectivity_is_monic mono) (sub_monic (WP Q) i)) as inj.
  simpl in e.
  (* Cantor's diagonal: the points of [Q] that do not satisfy the predicate
     their preimage names. *)
  pose (Dg := fun a : carrier Q => ∀ y : carrier m, mono y ≈ a → ~ (t y a)).
  pose (a := mono (s Dg)).
  assert (notD : ~ Dg a).
  { intros H.
    apply (H (s Dg) (reflexivity _)).
    exact (proj2 (e Dg a) H). }
  apply notD.
  intros y Hy Hty.
  apply notD.
  pose proof (inj y (s Dg) Hy) as Hys.
  apply (proj1 (e Dg a)).
  exact (proj1 (proper_morphism t y (s Dg) Hys a) Hty).
Qed.

(* Positive control: the lemma applied at the instance [SAFT] itself
   consumes (SAFT.v's readback, at [C = D = Sets@{h cobj}]), with the
   [cogen_prod] slot [u] held strictly above the object universe [cobj].
   Left unannotated, the lemma had that slot minimized to [cobj], and this
   application was refused. *)
Definition SubobjectCover_Id_Sets_absurd_at_SAFT@{cobj h u u2 u3 |
    Set < h, h < cobj, cobj < u, u3 <= h +}
  (comp : @Complete@{h h h cobj} Sets@{h cobj})
  (G : Cogenerator@{h cobj h} Sets@{h cobj})
  (WP : ∀ x : Sets@{h cobj}, SubobjectIndex@{u3 cobj h} x)
  (cover : SubobjectCover@{u2 u3 h u h cobj cobj h}
             (@Id Sets@{h cobj}) comp G WP) : False :=
  SubobjectCover_Id_Sets_absurd comp G WP cover.
