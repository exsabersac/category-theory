Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Monad.Kleisli.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(**
* The Kleisli free/forgetful adjunction

    nLab: https://ncatlab.org/nlab/show/Kleisli+category
    Wikipedia: https://en.wikipedia.org/wiki/Kleisli_category

    Monad/Adjunction.v shows that every adjunction F ⊣ U induces a monad
    U ◯ F on the domain of F.  This file provides the converse resolution
    through the Kleisli category C_M of a monad M on C (Monad/Kleisli.v):

    - [Kleisli_Free] F_M : C ⟶ C_M is the identity on objects and sends
      f : x ~> y to the pure Kleisli morphism ret ∘ f;
    - [Kleisli_Forget] U_M : C_M ⟶ C sends x to M x, and a Kleisli
      morphism f : x ~> M y to its extension join ∘ fmap[M] f (its bind);
    - [Kleisli_Adjunction] F_M ⊣ U_M: because F_M x = x and U_M y = M y,
      the two hom-setoids of the transposition are literally the same
      setoid x ~> M y, and the adjunction isomorphism [Kleisli_adj_iso]
      is the identity map in both directions.

    The adjunction presents the monad we started with:
    [Kleisli_Monad_agrees] identifies the composite U_M ◯ F_M with M (a
    natural isomorphism whose components are identities),
    [Kleisli_unit_agrees] identifies the adjunction unit with ret, and
    [Kleisli_join_agrees] identifies the U_M-image of the counit — which
    is exactly the multiplication of the monad that Monad/Adjunction.v
    extracts from this adjunction — with join.

    The other canonical resolution of a monad, through the Eilenberg–Moore
    category of algebras, lives in Monad/Eilenberg/Moore/Adjunction.v. 

--------
* Kleisli 自由/健忘附属词

nLab：https://ncatlab.org/nlab/show/Kleisli+category
 维基百科：https://en.wikipedia.org/wiki/Kleisli_category

Monad/Adjunction.v 表明每个附加词 F ⊣ U 都会引发一个 monad
 U ◯ F 在 F 的定义域上。该文件提供逆解析
 通过 C 上单子 M 的 Kleisli 范畴 C_M (Monad/Kleisli.v)：

- [Kleisli_Free] F_M : C ⟶ C_M 是对象上的标识并发送
 f : x ~> y 到纯Kleisli态射 ret ∘ f;
 - [Kleisli_Forget] U_M : C_M ⟶ C 将 x 发送到 M x，以及 Kleisli
 态射 f : x ~> M y 与其扩展 join ∘ fmap[M] f （其绑定）；
 - [Kleisli_Adjunction] F_M ⊣ U_M：因为 F_M x = x 且 U_M y = M y，
 转座的两个 hom-setoids 实际上是相同的
 setoid x ~> M y，以及附加同构 [Kleisli_adj_iso]
 是两个方向上的恒等映射。

附加词呈现了我们开始的单子：
 [Kleisli_Monad_agrees] 识别复合 U_M ◯ F_M 与 M (a
 自然同构，其组成部分是恒等式），
 [Kleisli_unit_agrees] 通过 ret 识别附加单元，并且
 [Kleisli_join_agrees] 识别该单位的 U_M 映像 — 其中
 正是 Monad/Adjunction.v 的 monad 的乘法
 摘自这个附加词——with join。

单子的另一种规范解析，通过艾伦伯格-摩尔
 代数类别，位于 Monad/Eilenberg/Moore/Adjunction.v 中。 
*)

Section KleisliAdjunction.

Context `{@Monad C M}.

#[local] Obligation Tactic := program_simpl.

(**
The free functor C ⟶ C_M: identity on objects; a morphism f becomes
    the pure Kleisli computation ret ∘ f.  Identity preservation is the
    right unit law of composition, and functoriality is the unit
    naturality [fmap_ret] against the left unit law [join_fmap_ret]. 

--------
自由函子 C ⟶ C_M：对象上的恒等式； 态射 f 变为
 纯 Kleisli 计算 ret ∘ f。 身份保存是
 正确的单位组合律，函子性是单位
 自然性[fmap_ret]对抗左单位法[join_fmap_ret]。 
*)

Program Definition Kleisli_Free : C ⟶ Kleisli := {|
  fobj := fun x => x;
  fmap := fun x y f => ret ∘ f
|}.
Next Obligation. proper. Qed.
Next Obligation. cat. Qed.
Next Obligation.
  (* ret ∘ (f ∘ g) ≈ join ∘ fmap[M] (ret ∘ f) ∘ (ret ∘ g) *)
  rewrite fmap_comp.
  rewrite (comp_assoc join).
  rewrite join_fmap_ret.
  rewrite id_left.
  rewrite (comp_assoc (fmap f)).
  rewrite <- fmap_ret.
  now rewrite comp_assoc.
Qed.

(**
The forgetful functor C_M ⟶ C: on objects, the carrier M x of the free
    algebra on x; on morphisms, Kleisli extension.  Identity preservation
    is the left unit law [join_fmap_ret], and functoriality combines the
    associativity [join_fmap_join] with the multiplication naturality
    [join_fmap_fmap], exactly as in the composition law of Kleisli. 

--------
健忘函子 C_M ⟶ C：在对象上，自由的载体 M x
 x 上的代数； 关于态射，Kleisli 扩展。 身份保存
 是左单位律 [join_fmap_ret]，函数性结合了
 [join_fmap_join] 与乘法自然性的结合性
 [join_fmap_fmap]，与 Kleisli 的组成定律完全相同。 
*)

Program Definition Kleisli_Forget : Kleisli ⟶ C := {|
  fobj := fun x => M x;
  fmap := fun x y f => join ∘ fmap[M] f
|}.
Next Obligation. proper. now rewrites. Qed.
Next Obligation. apply join_fmap_ret. Qed.
Next Obligation.
  (*
join ∘ fmap[M] (join ∘ fmap[M] f ∘ g)
       ≈ (join ∘ fmap[M] f) ∘ (join ∘ fmap[M] g) 

--------
加入 ∘ fmap[M] （加入 ∘ fmap[M] f ∘ g）
 ≈ (加入 ∘ fmap[M] f) ∘ (加入 ∘ fmap[M] g) 
*)
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  rewrite join_fmap_join.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc join (fmap (fmap _))).
  rewrite join_fmap_fmap; cat.
Qed.

(**
The transposition isomorphism: a Kleisli morphism F_M x ~{C_M}~> y and
    a C-morphism x ~> U_M y are one and the same arrow x ~> M y, so the
    hom-setoid isomorphism of the adjunction is the identity map. 

--------
转置同构：Kleisli态射 F_M x ~{C_M}~> y 和
 a C-态射 x ~> U_M y 是 1 并且相同的箭头 x ~> M y，所以
 附加词的 hom-setoid 同构是恒等图。 
*)

Program Definition Kleisli_adj_iso (x y : C) :
  @Isomorphism Sets
    {| carrier   := @hom Kleisli (Kleisli_Free x) y
     ; is_setoid := @homset Kleisli (Kleisli_Free x) y |}
    {| carrier   := @hom C x (Kleisli_Forget y)
     ; is_setoid := @homset C x (Kleisli_Forget y) |} := {|
  to   := {| morphism := fun f => f |};
  from := {| morphism := fun f => f |}
|}.
Next Obligation. proper. Qed.
Next Obligation. proper. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(**
Naturality of the transposition in the source argument, stated on the
    underlying arrows: precomposing a Kleisli morphism with a pure one is
    plain precomposition in C. 

--------
源论证中换位的自然性，在
 底层箭头：将Kleisli态射与纯态射预组合为
 C 中的简单预合成. 
*)

Lemma kleisli_transpose_nat_l {x y z : C} (f : y ~{C}~> M z) (g : x ~{C}~> y) :
  join ∘ fmap[M] f ∘ (ret ∘ g) ≈ f ∘ g.
Proof.
  rewrite comp_assoc.
  rewrite <- (comp_assoc join (fmap[M] f) ret).
  rewrite <- fmap_ret.
  rewrite (comp_assoc join ret f).
  rewrite join_ret.
  cat.
Qed.

Program Definition Kleisli_Adjunction : Kleisli_Free ⊣ Kleisli_Forget :=
  @Build_Adjunction' Kleisli C Kleisli_Free Kleisli_Forget Kleisli_adj_iso _ _.
Next Obligation. apply kleisli_transpose_nat_l. Qed.
Next Obligation. reflexivity. Qed.

(** The unit of the adjunction is the unit of the monad.  / 附加词的单位是单子的单位。*)

Lemma Kleisli_unit_agrees {x : C} :
  @unit _ _ _ _ Kleisli_Adjunction x ≈ ret[M].
Proof. reflexivity. Qed.

(**
The counit at x is the identity arrow on M x, read as the Kleisli
    morphism F_M (U_M x) ~{C_M}~> x that runs the computation. 

--------
x 处的计数是 M x 上的恒等箭头，读作 Kleisli
 态射 F_M (U_M x) ~{C_M}~> x 运行计算。 
*)

Lemma Kleisli_counit_agrees {x : C} :
  @counit _ _ _ _ Kleisli_Adjunction x ≈ id[M x].
Proof. reflexivity. Qed.

(**
The multiplication of the monad induced by this adjunction (per
    Monad/Adjunction.v it is the U_M-image of the counit) is join. 

--------
由该附加引起的单子的倍增（每
 Monad/Adjunction.v 它是 counit 的 U_M 图像）是 join。 
*)

Lemma Kleisli_join_agrees {x : C} :
  fmap[Kleisli_Forget] (@counit _ _ _ _ Kleisli_Adjunction x) ≈ join[M].
Proof.
  simpl.
  rewrite fmap_id.
  cat.
Qed.

(**
The resolution recovers M: the composite U_M ◯ F_M is naturally
    isomorphic to M, with identity components. 

--------
分辨率恢复M：合成的U_M ◯ F_M 自然是
 与 M 同构，具有恒等分量。 
*)

Theorem Kleisli_Monad_agrees : Kleisli_Forget ◯ Kleisli_Free ≈ M.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite join_fmap_ret.
  cat.
Qed.

End KleisliAdjunction.
