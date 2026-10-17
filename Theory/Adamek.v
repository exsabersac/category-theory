Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Instance.Omega.
Require Import Category.Construction.Chain.

Generalizable All Variables.

(* * * Adámek's initial-algebra 定理 over ω-chain （已译） *)

(* nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

   对带初始对象 [0] 的范畴 [C] 上的自函子 [F]，Adámek 定理把初始 [F]-代数建为
   ω-指标链的余极限

       0 --¡--> F 0 --F¡--> F² 0 --F²¡--> ...

   （[Construction/Chain.v]，打包为 [Chain F : Omega ⟶ C]）。写 [A] 为余极限
   [L : Colimit (Chain F)] 的顶点，结构映射 [α : F A ~> A] 是出自平移余锥的中介态射，
   且 [(A, α)] 在 [F]-代数范畴 [FAlg F] 中初始。

   当且仅当 [F] 保持该余极限时，[A] 是平移图 [F ◯ Chain F] 以 [F A] 为顶点的余极限。
   然而抽象 [PreservesColimit] 见证只记录 [F A] 携带 [F ◯ Chain F] 的*某个*余极限；
   共享顶点 [F A] 上的两余极限余锥相差自由的顶点自同构，故不暴露 [F A] 处的余锥腿是
   像腿 [fmap[F] (colimit_inj HL n)]。该腿一致性是初始性论证真正消耗的数据，故此处打包为
   诚实假设 [AdamekData]，并由其直接证明 [adamek]。

   因此 [PreservesColimit -> AdamekData] 的消解不在本文件中，[Theory/Adamek/Corollaries.v]
   也不提供：留作快速后续（ledger 17；见该文件对应注记）。余锥层类
   [PreservesColimitCocone]（Structure/Limit/Preservation.v）是陈述该消解的词汇；
   在写出之前 ledger 条目保持开放。过渡期内 [AdamekData] 接口是承重契约。 *)

(* Shift order 证明 [m ≤ n] [S m ≤ S n], recursion the
 derivation. It mentions [le_t] (Instance/Omega.v), so it lives above
 范畴-indexed development. （已译） *)
Fixpoint le_S_shift@{u} {m n} (p : le_t@{u} m n) : le_t@{u} (S m) (S n) :=
  match p in le_t _ n' return le_t@{u} (S m) (S n') with
  | le_t_n    => le_t_n
  | le_t_S p' => le_t_S (le_S_shift p')
  end.

(*
   本节说明 Adamek 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

Section Adamek.

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Universe cobj.
Context {C : Category@{cobj Set Set}}.
Context `{HI : @Initial C}.
Context (F : C ⟶ C).
Context (L : Colimit (Chain F)).

(* 相关说明。 （已译） *)
Definition A : C := colimit_apex L.
Definition HL := colimit_is_acolimit L.

(* 相关说明。 （已译） *)
Lemma chain_hom_n {m} : chain_hom F (@le_t_n m) = id.
Proof. reflexivity. Qed.

Lemma chain_hom_step {m n} (p : le_t m n) :
  chain_hom F (le_t_S p) = chain_step F n ∘ chain_hom F p.
Proof. reflexivity. Qed.

Lemma chain_step_step (n : nat) :
  chain_step F (S n) = fmap[F] (chain_step F n).
Proof. reflexivity. Qed.

(* Transporting shifted order 证明 image under [F] transporting
 original: [chain_hom (S p) ≈ F (chain_hom p)]. （已译） *)
Lemma chain_hom_S {m n} (p : le_t m n) :
  chain_hom F (le_S_shift p) ≈ fmap[F] (chain_hom F p).
Proof.
  induction p as [| n' p' IH].
  - cbn [le_S_shift chain_hom]. now rewrite fmap_id.
  - cbn [le_S_shift chain_hom].
    rewrite chain_step_step.
    rewrite IH.
    now rewrite fmap_comp.
Qed.

(* The honest 假设: [F A] carries colimit shifted diagram whose
 injections exactly image legs [fmap[F] (colimit_inj HL n)]. （已译） *)
Record AdamekData : Type := {
  adamek_colim : IsAColimit (F ◯ Chain F) (F A) ;
  adamek_legs  : ∀ n : nat,
    colimit_inj adamek_colim n ≈ fmap[F] (colimit_inj HL n)
}.

Section WithData.

Context (D : AdamekData).

Local Notation HFL := (adamek_colim D).

(* 相关说明。 （已译） *)
Program Definition Ashift : Cocone (F ◯ Chain F) :=
  @Build_Cone (Omega^op) (C^op) ((F ◯ Chain F)^op) A
    (@Build_ACone (Omega^op) (C^op) A ((F ◯ Chain F)^op)
       (fun n => colimit_inj HL (S n)) _).
Next Obligation.
  intros x y f.
  change (colimit_inj HL (S x) ∘ fmap[F] (chain_hom F f)
            ≈ colimit_inj HL (S y)).
  rewrite <- chain_hom_S.
  exact (colimit_inj_coherence HL (le_S_shift f)).
Qed.

(* 相关说明。 （已译） *)
Definition alpha : F A ~> A := colimit_med HFL Ashift.

(* The defining step 关系 structure map, phrased through image
 legs folding leg agreement [adamek_legs]. （已译） *)
Lemma STEP (n : nat) :
  alpha ∘ fmap[F] (colimit_inj HL n) ≈ colimit_inj HL (S n).
Proof.
  rewrite <- (adamek_legs D n).
  exact (colimit_med_commutes HFL Ashift n).
Qed.

Section Mediator.

Context (aβ : FAlg F).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint lam (n : nat) : chain_obj F n ~> ``aβ :=
  match n with
  | O   => zero
  | S k => `2 aβ ∘ fmap[F] (lam k)
  end.

(* 相关说明。 （已译） *)
Lemma LAMSTEP (n : nat) : lam (S n) ∘ chain_step F n ≈ lam n.
Proof.
  induction n as [| k IH].
  - apply zero_unique.
  - transitivity (`2 aβ ∘ (fmap[F] (lam (S k)) ∘ fmap[F] (chain_step F k))).
    + change (lam (S (S k))) with (`2 aβ ∘ fmap[F] (lam (S k))).
      change (chain_step F (S k)) with (fmap[F] (chain_step F k)).
      now rewrite <- comp_assoc.
    + rewrite <- fmap_comp.
      rewrite IH.
      reflexivity.
Qed.

(* [lam] is a cocone over the whole chain: it respects every transport. *)
Lemma lam_coh {m n} (f : le_t m n) : lam n ∘ chain_hom F f ≈ lam m.
Proof.
  induction f as [| n' f' IH].
  - rewrite chain_hom_n. now rewrite id_right.
  - rewrite (chain_hom_step f').
    rewrite comp_assoc.
    rewrite LAMSTEP.
    exact IH.
Qed.

(* 相关说明。 （已译） *)
Program Definition Lam : Cocone (Chain F) :=
  @Build_Cone (Omega^op) (C^op) ((Chain F)^op) (``aβ)
    (@Build_ACone (Omega^op) (C^op) (``aβ) ((Chain F)^op) lam _).
Next Obligation.
  intros x y f.
  change (lam x ∘ chain_hom F f ≈ lam y).
  exact (lam_coh f).
Qed.

(* 相关说明。 （已译） *)
Definition u : A ~> ``aβ := colimit_med HL Lam.

Lemma u_inj (n : nat) : u ∘ colimit_inj HL n ≈ lam n.
Proof. exact (colimit_med_commutes HL Lam n). Qed.

(* 相关说明。 （已译） *)
Program Definition T : Cocone (F ◯ Chain F) :=
  @Build_Cone (Omega^op) (C^op) ((F ◯ Chain F)^op) (``aβ)
    (@Build_ACone (Omega^op) (C^op) (``aβ) ((F ◯ Chain F)^op)
       (fun n => lam (S n)) _).
Next Obligation.
  intros x y f.
  change (lam (S x) ∘ fmap[F] (chain_hom F f) ≈ lam (S y)).
  rewrite <- chain_hom_S.
  exact (lam_coh (le_S_shift f)).
Qed.

(* The mediator [u] 态射 [F]-algebras [(A, α) ~> (`⟦0⟧2 aβ)]:
 both [u ∘ α] [`2 aβ ∘ F u] mediate shifted cocone [T]. （已译） *)
Lemma u_alg : u ∘ alpha ≈ `2 aβ ∘ fmap[F] u.
Proof.
  apply (colimit_med_eq HFL T).
  (* 相关说明。 （已译） *)
  - intro n.
    rewrite (adamek_legs D n).
    rewrite <- comp_assoc.
    change ((F ◯ Chain F) n) with (F ((Chain F) n)).
    rewrite STEP.
    exact (u_inj (S n)).
  - intro n.
    rewrite (adamek_legs D n).
    rewrite <- comp_assoc.
    change ((F ◯ Chain F) n) with (F ((Chain F) n)).
    rewrite <- fmap_comp.
    rewrite u_inj.
    reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma hom_is_u (h : @FAlgHom C F A (``aβ) alpha (`2 aβ)) :
  falg_hom[h] ≈ u.
Proof.
  destruct h as [hh hcomm]; simpl.
  symmetry.
  unfold u.
  apply (colimit_med_unique HL Lam).
  intro n.
  induction n as [| k IH].
  - apply zero_unique.
  - rewrite <- STEP.
    rewrite comp_assoc.
    rewrite hcomm.
    rewrite <- comp_assoc.
    change ((Chain F) (S k)) with (F ((Chain F) k)).
    rewrite <- fmap_comp.
    rewrite IH.
    reflexivity.
Qed.

End Mediator.

(* The candidate initial algebra [(A, α)], as an object of [FAlg F].  Naming it
   with an explicit carrier type pins the sigma predicate to
   [fun a => FAlgebra F a], which bare [(A; alpha)] would otherwise leave
   ambiguous. *)
Definition muF : FAlg F := existT (fun a : C => FAlgebra F a) A alpha.

(*
   本节说明函子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition adamek_one (y : FAlg F) :
  muF ~{FAlg F}~> y :=
  {| falg_hom := u y ; falg_commutes := u_alg y |}.

Lemma adamek_one_unique (y : FAlg F)
  (f g : muF ~{FAlg F}~> y) : f ≈ g.
Proof.
  simpl.
  transitivity (u y).
  - exact (hom_is_u y f).
  - symmetry. exact (hom_is_u y g).
Qed.

(* [(A, α)] is initial in [FAlg F], i.e. terminal in [(FAlg F)^op].  The
   opposite category is named explicitly through [Opposite]: [FAlg F] and its
   opposite share objects, so a bare record literal cannot recover which side
   the terminal object lives on. *)
Definition adamek : @Initial (FAlg F) :=
  @Build_Terminal (Opposite (FAlg F)) muF adamek_one adamek_one_unique.

End WithData.

End Adamek.
