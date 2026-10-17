Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.

Generalizable All Variables.

(** The Kleisli category of a monad. *)

(* nLab: https://ncatlab.org/nlab/show/Kleisli+category
   Wikipedia: https://en.wikipedia.org/wiki/Kleisli_category

   范畴 C 上单子 (M, ret, join) = (T, η, μ) 的 Kleisli 范畴 C_T 与 C 有相同对象，
   而 Kleisli 态射 a ⇸ b 是普通 C-态射 a ~> M b。x 上的恒等是单位 ret（η_x），
   f : b ~> M c 在 g : a ~> M b 之后的 Kleisli 复合是

       f ∘_K g  ≈  join ∘ fmap[M] f ∘ g    (μ_c ∘ T(f) ∘ g),

   恰是 f 的 bind 前复合 g（g >>= f）。范畴定律由单子定律推出：左/右单位律用
   join_fmap_ret 与 join_ret（及单位自然性 fmap_ret），结合律用单子结合律
   join_fmap_join 及乘法自然性 join_fmap_fmap。

   此处 objects = obj C，hom a ⇸ b = a ~> M b，id = ret（η），compose = bind。

   此范畴上的自由/遗忘伴随 F_T ⊣ U_T 以 M 为其单子，且 C_T 是 Eilenberg–Moore 范畴中
   自由代数的满子范畴（见 Monad/Eilenberg/Moore.v）。

   更正 (#475)。撰写时树中尚无函子 C_T ⟶ C^T。嵌入是 Monad/Kleisli/Comparison.v 的
   [Kleisli_EM]（Riehl, Lemma 5.2.14）：满忠实，把 c 送到自由代数 (T c, μ_c)。 *)

Section Kleisli.

Context `{@Monad C M}.

#[local] Obligation Tactic := program_simpl.

Program Definition Kleisli : Category := {|
  obj     := C;
  hom     := fun x y => x ~> M y;
  homset  := fun x y => @homset C x (M y);
  id      := @ret C M _;
  compose := fun x y z f g => join ∘ fmap[M] f ∘ g
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. rewrite join_fmap_ret; cat. Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite <- fmap_ret; cat.
  rewrite comp_assoc.
  rewrite join_ret; cat.
Qed.
Next Obligation.
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  rewrite join_fmap_join.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc join (fmap (fmap _))).
  rewrite join_fmap_fmap; cat.
Qed.
Next Obligation.
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  rewrite join_fmap_join.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc join (fmap (fmap _))).
  rewrite join_fmap_fmap; cat.
Qed.

Definition kleisli_compose `(f : b ~> M c) `(g : a ~> M b) :
  a ~> M c := @compose Kleisli _ _ _ f g.

Notation "f <=< g" :=
  (kleisli_compose f g) (at level 40, left associativity) : morphism_scope.
Notation "f >=> g" :=
  (kleisli_compose g f) (at level 40, left associativity) : morphism_scope.

(* We can now re-express the monad laws in terms of this category, making the
   monoid relationship clearer. *)

Corollary monad_id_left `(f : x ~{C}~> M y) : ret <=< f ≈ f.
Proof. unfold kleisli_compose; cat. Qed.

Corollary monad_id_right `(f : x ~> M y) : f <=< ret ≈ f.
Proof. unfold kleisli_compose; cat. Qed.

Corollary monad_comp_assoc `(f : z ~> M w) `(g : y ~> M z) `(h : x ~> M y) :
  f <=< (g <=< h) ≈ (f <=< g) <=< h.
Proof.
  unfold kleisli_compose; cat.
  now rewrite comp_assoc.
Qed.

End Kleisli.

Notation "f <=< g" :=
  (@compose Kleisli _ _ _ f g) (at level 40, left associativity) : morphism_scope.
Notation "f >=> g" :=
  (@compose Kleisli _ _ _ g f) (at level 40, left associativity) : morphism_scope.

Notation "f >=[ M ]=> g" := (@kleisli_compose _ M _ _ _ f _ g)
  (at level 40, left associativity) : morphism_scope.
Notation "f <=[ M ]=< g" := (@kleisli_compose _ M _ _ _ g _ f)
  (at level 40, left associativity) : morphism_scope.
