Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Construction.FCoalg.

Generalizable All Variables.

(** * Lambek's lemma *)

(* nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

   Lambek 引理断言：初始 F-代数的结构映射是同构。若 [(μ, α)] 是 [FAlg F] 的初始对象，
   则 [α : F μ ~> μ] 可逆，故 [F μ ≅ μ] 且 [μ] 是 [F] 的不动点（「最小不动点」）。
   经典一行论证完全在 [FAlg F] 内进行：

     - 形成代数 [(F μ, fmap α)]；
     - 进入它的初始中介 [h : μ ~> F μ] 是代数映射，故交换：[h ∘ α ≈ fmap α ∘ fmap h]；
     - 把 [α] 读作代数映射 [(F μ, fmap α) ~> (μ, α)]，与中介复合得初始对象的自同态，
       由初始性即为恒等：[α ∘ h ≈ id]；
     - 把 [α ∘ h ≈ id] 经中介交换方块与函子性回推得 [h ∘ α ≈ id]。

   故 [α] 与 [h] 互逆且 [F μ ≅ μ]。对偶地，终结 F-余代数也有可逆结构映射，
   [ν ≅ F ν]（最大不动点）；[lambek_final] 通过对 [F^op] 应用 [lambek]
   （终结 F-余代数即初始 [F^op]-代数）并取对称同构得到。 *)

Theorem lambek `(F : C ⟶ C) (I : @Initial (FAlg F)) :
  F (`1 (@initial_obj (FAlg F) I)) ≅ `1 (@initial_obj (FAlg F) I).
Proof.
  (* The initial algebra [(μ, α)] and the auxiliary algebra [(F μ, fmap α)]. *)
  pose (iobj := @initial_obj (FAlg F) I).
  pose (Falg := ((F (`1 iobj))
                   ; (fmap[F] (`2 iobj) : FAlgebra F (F (`1 iobj))))).
  (* [α] itself is an algebra map [(F μ, fmap α) ~> (μ, α)]. *)
  pose (αHom := {| falg_hom := `2 iobj; falg_commutes := ltac:(reflexivity) |}
                : Falg ~{FAlg F}~> iobj).
  (* The unique mediator [h : μ ~> F μ] out of the initial algebra. *)
  pose (hHom := @zero (FAlg F) I Falg).
  (* The mediator is an algebra map, so its carrier commutes with structures. *)
  assert (Hcomm : falg_hom[hHom] ∘ (`2 iobj)
                    ≈ fmap[F] (`2 iobj) ∘ fmap[F] falg_hom[hHom]).
  { exact (@falg_commutes _ _ _ _ _ _ hHom). }
  (* [α ∘ h] is an endomorphism of the initial algebra, hence the identity. *)
  assert (Hαh : (`2 iobj) ∘ falg_hom[hHom] ≈ id).
  { pose proof (zero_unique (αHom ∘ hHom) id) as Huniq; simpl in Huniq;
      exact Huniq. }
  (* Pushing [α ∘ h ≈ id] through the commuting square gives [h ∘ α ≈ id]. *)
  assert (Hhα : falg_hom[hHom] ∘ (`2 iobj) ≈ id).
  { rewrite Hcomm.
    transitivity (fmap[F] ((`2 iobj) ∘ falg_hom[hHom])).
    - symmetry; apply fmap_comp.
    - rewrite Hαh; apply fmap_id. }
  (* [α] and [h] are mutually inverse: [F μ ≅ μ]. *)
  exact {| to := `2 iobj; from := falg_hom[hHom];
           iso_to_from := Hαh; iso_from_to := Hhα |}.
Qed.

(*
   Dually, the structure map of the final F-余代数 is an 同构. The

   本节：范畴 [FCoalg F] is [(FAlg (F^op))^op], so [@Terminal (FCoalg F)] is definitionally [@Initial (FAlg (F^op))] final F-余代数 is initial [F^op]-代数. Its carrier [ν] is 对象 [C^op], so this 同构 lives [C^op];

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem lambek_final `(F : C ⟶ C) (T : @Terminal (FCoalg F)) :
  `1 (@terminal_obj (FCoalg F) T) ≅ F (`1 (@terminal_obj (FCoalg F) T)).
Proof.
  exact (iso_sym (lambek (F^op) T)).
Qed.
