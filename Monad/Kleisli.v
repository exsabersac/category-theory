Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.

Generalizable All Variables.

(** The Kleisli category of a monad.  / 单子的Kleisli范畴。*)

(*
nLab: https://ncatlab.org/nlab/show/Kleisli+category
   Wikipedia: https://en.wikipedia.org/wiki/Kleisli_category

   The Kleisli category C_T of a monad (M, ret, join) = (T, η, μ) on C has the
   same objects as C, while a Kleisli morphism a ⇸ b is an ordinary C-morphism
   a ~> M b. The identity on x is the unit ret (η_x), and the Kleisli composite
   of f : b ~> M c after g : a ~> M b is

       f ∘_K g  ≈  join ∘ fmap[M] f ∘ g    (μ_c ∘ T(f) ∘ g),

   which is exactly the bind of f precomposed with g (g >>= f). The category
   laws follow from the monad laws: the left/right unit laws use join_fmap_ret
   and join_ret (with the unit naturality fmap_ret), and associativity uses the
   monad associativity join_fmap_join together with the multiplication
   naturality join_fmap_fmap.

   Here objects = obj C, hom a ⇸ b = a ~> M b, id = ret (η), compose = bind.

   The free/forgetful adjunction F_T ⊣ U_T on this category has M as its monad,
   and C_T is the full subcategory of free algebras inside the Eilenberg–Moore
   category (see Monad/Eilenberg/Moore.v).

   CORRECTION (#475).  When this was written no functor C_T ⟶ C^T existed in
   the tree.  The embedding is Monad/Kleisli/Comparison.v's [Kleisli_EM]
   (Riehl, Lemma 5.2.14): full and faithful, sending c to the free algebra
   (T c, μ_c) at [eq_refl], so that C_T is equivalent to the full subcategory
   of free algebras ([Kleisli_EM_Image_Equivalence]).  The “is” above says
   too much: C_T is equivalent to that subcategory and is not shown to be
   one, and Mac Lane says of his construction of the Kleisli category that
   it “really gives this category directly and not as a subcategory (cf.
   Exercise 3)” (§VI.5, p. 147).  [Kleisli_EM_equivalence_iff] adds that
   [Kleisli_EM] is an equivalence onto all of C^T exactly when every algebra
   is free. 

--------
nLab: https://ncatlab.org/nlab/show/Kleisli+category
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
   [Kleisli_EM]（Riehl, Lemma 5.2.14）：满忠实，把 c 送到自由代数 (T c, μ_c)。 
*)

Section Kleisli.

Context `{@Monad C M}.

#[local] Obligation Tactic := program_simpl.

(*
   【Kleisli 范畴定义展开】/ Definition walkthrough
   （口吻对齐 Theory/Functor.v @ c826572；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      Kleisli 范畴 C_T：对象同 C；态射 a ⇸ b 是 C 中的 a ~> M b；
      恒等 = ret；复合 = bind（join ∘ fmap f ∘ g）。
      Same objects as C; homs are a ~> M b; id = ret; compose = bind.
      Haskell 对照：Kleisli 箭头 a -> m b，合成是 (<=<) / (>>> )；
      范畴版把这套提升为真正的 Category 实例，定律由单子定律推出。
      Haskell analogy: Kleisli arrows a → m b with (<=<); here a real Category.

   2) 关键字段 / Key Category fields
      - obj := C
      - hom x y := x ~> M y
      - id := ret
      - compose f g := join ∘ fmap[M] f ∘ g   （即 g >>= f）
      全部相等是 ≈（Hom-Setoid 继承自 C）。
      Equality is ≈ throughout (Hom-setoids from C).

   3) 与 EM 的关系 / Relation to Eilenberg–Moore
      C_T 经 Kleisli_EM 嵌入自由代数满子范畴（见 Monad/Kleisli/Comparison.v）。
      Embeds into free algebras in C^T via Kleisli_EM.

   阅读顺序：hom/id/compose → Obligation（单子律）→ 后文伴随。
   Reading order: hom/id/compose → obligations (monad laws) → adjunction later.
*)

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

(*
We can now re-express the monad laws in terms of this category, making the
   monoid relationship clearer. 

--------
我们现在可以用这个范畴重新表达单子法则，使得
 幺半群关系更清晰。 
*)

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
