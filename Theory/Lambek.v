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

(** * Lambek's lemma / * 兰贝克引理 *)

(*
nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

   Lambek's lemma states that the structure map of an initial F-algebra is an
   isomorphism: if [(μ, α)] is the initial object of [FAlg F], then
   [α : F μ ~> μ] is invertible, so [F μ ≅ μ] and [μ] is a fixed point of [F]
   (“the least fixed point”). The classical one-line argument runs entirely
   inside [FAlg F]:

     - form the algebra [(F μ, fmap α)];
     - the initial mediator [h : μ ~> F μ] into it is an algebra map, so it
       commutes: [h ∘ α ≈ fmap α ∘ fmap h];
     - [α], read as an algebra map [(F μ, fmap α) ~> (μ, α)], composes with the
       mediator to give an endomorphism of the initial object, which by
       initiality is the identity: [α ∘ h ≈ id];
     - feeding [α ∘ h ≈ id] back through the mediator's commuting square and
       functoriality yields [h ∘ α ≈ id].

   Hence [α] and [h] are mutually inverse and [F μ ≅ μ]. By duality the final
   F-coalgebra has an invertible structure map as well, [ν ≅ F ν] (the greatest
   fixed point); [lambek_final] obtains this by applying [lambek] to [F^op] (the
   final F-coalgebra being the initial [F^op]-algebra) and taking the symmetric
   isomorphism.

--------
nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
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
   （终结 F-余代数即初始 [F^op]-代数）并取对称同构得到。
*)

Theorem lambek `(F : C ⟶ C) (I : @Initial (FAlg F)) :
  F (`1 (@initial_obj (FAlg F) I)) ≅ `1 (@initial_obj (FAlg F) I).
Proof.
  (* The initial algebra [(μ, α)] and the auxiliary algebra [(F μ, fmap α)]. / 初始代数 [(μ, α)] 和辅助代数 [(F μ, fmap α)]。 *)
  pose (iobj := @initial_obj (FAlg F) I).
  pose (Falg := ((F (`1 iobj))
                   ; (fmap[F] (`2 iobj) : FAlgebra F (F (`1 iobj))))).
  (* [α] itself is an algebra map [(F μ, fmap α) ~> (μ, α)]. / [α] 本身是一个代数映射 [(F μ, fmap α) ~> (μ, α)]。 *)
  pose (αHom := {| falg_hom := `2 iobj; falg_commutes := ltac:(reflexivity) |}
                : Falg ~{FAlg F}~> iobj).
  (* The unique mediator [h : μ ~> F μ] out of the initial algebra. / 来自初始代数的唯一调解器 [h : μ ~> F μ]。 *)
  pose (hHom := @zero (FAlg F) I Falg).
  (* The mediator is an algebra map, so its carrier commutes with structures. / 中介是一个代数映射，因此它的承载体与结构交换。 *)
  assert (Hcomm : falg_hom[hHom] ∘ (`2 iobj)
                    ≈ fmap[F] (`2 iobj) ∘ fmap[F] falg_hom[hHom]).
  { exact (@falg_commutes _ _ _ _ _ _ hHom). }
  (* [α ∘ h] is an endomorphism of the initial algebra, hence the identity. / [α ∘ h] 是初始代数的自同态，因此是恒等映射。 *)
  assert (Hαh : (`2 iobj) ∘ falg_hom[hHom] ≈ id).
  { pose proof (zero_unique (αHom ∘ hHom) id) as Huniq; simpl in Huniq;
      exact Huniq. }
  (* Pushing [α ∘ h ≈ id] through the commuting square gives [h ∘ α ≈ id]. / 将 [α ∘ h ≈ id] 推过通勤广场得到 [h ∘ α ≈ id]。 *)
  assert (Hhα : falg_hom[hHom] ∘ (`2 iobj) ≈ id).
  { rewrite Hcomm.
    transitivity (fmap[F] ((`2 iobj) ∘ falg_hom[hHom])).
    - symmetry; apply fmap_comp.
    - rewrite Hαh; apply fmap_id. }
  (* [α] and [h] are mutually inverse: [F μ ≅ μ]. / [α] 和 [h] 是相互逆的：[F μ ≅ μ]。 *)
  exact {| to := `2 iobj; from := falg_hom[hHom];
           iso_to_from := Hαh; iso_from_to := Hhα |}.
Qed.

(*
Dually, the structure map of the final F-coalgebra is an isomorphism. The
   category [FCoalg F] is [(FAlg (F^op))^op], so [@Terminal (FCoalg F)] is
   definitionally [@Initial (FAlg (F^op))] and the final F-coalgebra is the
   initial [F^op]-algebra. Its carrier [ν] is an object of [C^op], so this
   isomorphism lives in [C^op]; applying [lambek] to [F^op] gives
   [F^op ν ≅[C^op] ν], and its symmetric form [iso_sym] is the required
   [ν ≅ F ν].

--------
同样，最终 F-余代数的结构映射是一个同构。范畴 [FCoalg F] 是 [(FAlg (F^op))^op]，因此 [@Terminal (FCoalg F)] 在定义上是 [@Initial (FAlg (F^op))]，最终 F-余代数是初始 [F^op]-代数。它的承载 [ν] 是 [C^op] 的一个对象，所以这个同构存在于 [C^op]；将 [lambek] 应用于 [F^op] 得到 [F^op ν ≅[C^op] ν]，其对称形式 [iso_sym] 是所需的 [ν ≅ F ν]。
*)
Theorem lambek_final `(F : C ⟶ C) (T : @Terminal (FCoalg F)) :
  `1 (@terminal_obj (FCoalg F) T) ≅ F (`1 (@terminal_obj (FCoalg F) T)).
Proof.
  exact (iso_sym (lambek (F^op) T)).
Qed.
