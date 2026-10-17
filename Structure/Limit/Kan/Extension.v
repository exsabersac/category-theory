Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cone.Const.

Generalizable All Variables.

(** * Limits as right Kan extensions along the terminal functor *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Kan_extension

   本文件给出 Kan 扩张：沿函子 F 的左/右 Kan 扩张分别为预复合诱导函子的左/右伴随（当存在时）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Kan_Limit `(F : J ⟶ C) `{Lim : @Limit _ _ F} `{@RightKan _ _ (Erase J) C} :
  Lim ≅ Ran (Erase J) F ttt.
Proof.
  given (cone : Cone F). {
    pose (from ((@adj _ _ _ _ ran_adjoint
                   (Ran (Erase J) F) F)) nat_id) as adj_from.
    simpl carrier in adj_from.
    unshelve (refine {| vertex_obj := Ran (Erase J) F ttt |});
      [ assumption | unshelve econstructor ].
    - apply adj_from.
    - abstract (intros; rewrite (naturality[adj_from]); simpl; cat).
  }
  given (nat : Δ(Lim) ◯ Erase J ⟹ F). {
    transform; simpl.
    + exact vertex_map.
    + abstract(rewrite id_right; apply cone_coherence).
    + abstract(rewrite id_right; symmetry; apply cone_coherence).
  }
  pose (to (@adj _ _ _ _ ran_adjoint (Δ(Lim)) F) nat)
    as adj_to; simpl in adj_to.

  assert (to_from : adj_to ttt ∘ unique_obj (ump_limits cone) ≈ id). {
    simpl.
    spose (iso_to_from
             ((@adj _ _ _ _ ran_adjoint
                    (Ran (Erase J) F) F)) nat_id ttt) as X.
    rewrite fmap_id in X.
    rewrites.
    unfold adj_to; simpl.

    given (from_ran : Ran (Erase J) F ⟹ Δ(Lim)). {
      transform; simpl; intros.
      - destruct x.
        apply (unique_obj (ump_limits cone)).
      - destruct x, y, f; simpl.
        abstract cat.
      - destruct x, y, f; simpl.
        abstract cat.
    }

    spose (@to_adj_nat_l _ _ _ _ ran_adjoint
                         (Ran (Erase J) F) (Δ(Lim))
                         F nat from_ran ttt) as X0.
    rewrites.

    assert (∀ f g, f ≈ g
              → to (@adj _ _ _ _ ran_adjoint (Ran (Erase J) F) F) f
               ≈ to (@adj _ _ _ _ ran_adjoint (Ran (Erase J) F) F) g). {
      intros; rewrites; reflexivity.
    }
    simpl in X.
    rewrite <- X.
    - rewrite <- X0.
      apply X; simpl.
      apply (unique_property (ump_limits cone)).
    - simpl; reflexivity.
  }

  isomorphism; simpl.
  - apply adj_to.
  - apply (unique_obj (ump_limits cone)).
  - apply to_from.
  - simpl in *.
    (*
   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

    assert (∀ (f g : Lim ~{ C }~> Lim),
              (∀ x, vertex_map[Lim] ∘ f ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ Lim) x) ->
              (∀ x, vertex_map[Lim] ∘ g ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ Lim) x) ->
              f ∘ unique_obj (ump_limits cone) ≈
              g ∘ unique_obj (ump_limits cone) → f ≈ g) as HA. {
      intros; clear adj_to to_from nat.
      rewrite <- (uniqueness (ump_limits Lim) _ X).
      rewrite <- (uniqueness (ump_limits Lim) _ X0).
      reflexivity.
    }

    (*
   本节说明伴随、（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    apply HA; simpl; intros; cat; swap 1 2.
    + rewrite <- comp_assoc.
      rewrite to_from; cat.

    + rewrite comp_assoc.
      srewrite (unique_property (ump_limits cone)).
      srewrite_r (iso_from_to
                    ((@adj _ _ _ _ ran_adjoint (Δ(Lim)) F)) nat x).
      unfold adj_to.
      srewrite_r (@from_adj_nat_l _ _ _ _ ran_adjoint
                    (Δ(Lim)) (Ran (Erase J) F) F nat_id
                    (to (@adj _ _ _ _ ran_adjoint (Δ(Lim)) F) nat) x).
      sapply (@from_adj_respects
                _ _ _ _ (@ran_adjoint _ _ _ _ H) (Δ(Lim)) F).
      simpl; intros; cat.
Qed.
