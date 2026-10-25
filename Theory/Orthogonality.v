Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.

Generalizable All Variables.

(*
Orthogonality of morphisms (the unique lifting property).

   nLab:      https://ncatlab.org/nlab/show/orthogonality
   Wikipedia: https://en.wikipedia.org/wiki/Lifting_property

   A morphism e : a ~> b is (left) orthogonal to m : x ~> y, written e ⫫ m,
   when every commuting square

            u
        a ----> x
        |       |
      e |       | m
        v       v
        b ----> y
            v

   (that is, m ∘ u ≈ v ∘ e) has a unique diagonal filler d : b ~> x with
   d ∘ e ≈ u and m ∘ d ≈ v. Orthogonality is the uniqueness-strengthened
   form of the weak lifting property that underlies weak factorization
   systems; with the uniqueness clause it characterizes the two classes of
   an orthogonal factorization system (nLab: orthogonal factorization
   system). Here we record the notion itself together with the closure
   properties of the left class that need no (co)limits: isomorphisms are
   orthogonal to everything (on either side), and the left class is closed
   under composition and under retracts in the arrow category.

   Stability of the left class under cobase change (pushout) needs the
   pullback/pushout toolkit and lives there: [ortho_left_cobase_change] in
   Theory/Morphisms/Stability.v.

--------
态射的正交性 (orthogonality)（唯一提升性质）。

   nLab:      https://ncatlab.org/nlab/show/orthogonality
   Wikipedia: https://en.wikipedia.org/wiki/Lifting_property

   态射 e : a ~> b （左）正交于 m : x ~> y，写作 e ⫫ m，当每个交换方块

            u
        a ----> x
        |       |
      e |       | m
        v       v
        b ----> y
            v

   （即 m ∘ u ≈ v ∘ e）都有唯一对角填充 d : b ~> x 满足 d ∘ e ≈ u 与 m ∘ d ≈ v。
   正交性是弱提升性质加强唯一性后的形式，后者支撑弱分解系统；带唯一性子句时它刻画
   正交分解系统的两类（nLab: orthogonal factorization system）。此处记录概念本身，
   以及左类无需（余）极限的闭包性质：同构正交于一切（任一侧），左类对复合与箭头范畴中的
   收缩封闭。

   左类在余基变换（推出）下的稳定性需要拉回/推出工具箱，见 Theory/Morphisms/Stability.v
   的 [ortho_left_cobase_change]。
*)

(*
The ∃!-with-∧ shape below mirrors [ump_pullbacks] in Structure/Pullback.v:
   [∃!] is the Type-valued [Unique] record of Lib/Setoid.v, and [∧] is the
   Type-valued conjunction, so fillers can be extracted and used in
   definitions.

--------
下方的 ∃!-with-∧ 形状在 Structure/Pullback.v 中反映了 [ump_pullbacks]：
   [∃!] 是 Lib/Setoid.v 中类型值的 [Unique] 记录，[∧] 是类型值的合取，因此可以提取填充物并在定义中使用。
*)

Class Orthogonal {C : Category} {a b x y : C} (e : a ~> b) (m : x ~> y) := {
  ortho_lift {u : a ~> x} {v : b ~> y} (comm : m ∘ u ≈ v ∘ e) :
    ∃! d : b ~> x, (d ∘ e ≈ u) ∧ (m ∘ d ≈ v)
}.

Notation "e ⫫ m" := (Orthogonal e m) (at level 70) : category_theory_scope.

(*
Any isomorphism is left orthogonal to every morphism: the filler of a
   square (u, v) over e is u ∘ e⁻¹, and any filler d' recovers it via
   d' ≈ d' ∘ e ∘ e⁻¹ ≈ u ∘ e⁻¹.

--------
任何同构都与每个态射左正交：在 e 上的方形 (u, v) 的填充是 u ∘ e⁻¹，任何填充 d' 都可以通过 d' ≈ d' ∘ e ∘ e⁻¹ ≈ u ∘ e⁻¹ 恢复它。
*)
Lemma iso_ortho_left {C : Category} {a b x y : C} (e : a ~> b) (m : x ~> y) :
  IsIsomorphism e → e ⫫ m.
Proof.
  intros He.
  constructor; intros u v comm.
  unshelve refine {| unique_obj := u ∘ @two_sided_inverse _ _ _ e He |}.
  - split.
    + (* (u ∘ e⁻¹) ∘ e ≈ u / (u ∘ e⁻¹) ∘ e ≈ u *)
      rewrite <- comp_assoc.
      rewrite (@is_left_inverse _ _ _ e He).
      cat.
    + (* m ∘ (u ∘ e⁻¹) ≈ v / m ∘ (u ∘ e⁻¹) ≈ v *)
      rewrite comp_assoc.
      rewrite comm.
      rewrite <- comp_assoc.
      rewrite (@is_right_inverse _ _ _ e He).
      cat.
  - intros d' [Hd'e Hmd'].
    (* u ∘ e⁻¹ ≈ d' / u ∘ e⁻¹ ≈ d' *)
    rewrite <- Hd'e.
    rewrite <- comp_assoc.
    rewrite (@is_right_inverse _ _ _ e He).
    cat.
Qed.

(*
Dually, any isomorphism is right orthogonal to every morphism: the filler
   is m⁻¹ ∘ v, and uniqueness follows by cancelling m on the left.

--------
同样，任何同构都是对每个态射右正交的：填充物是 m⁻¹ ∘ v，唯一性通过在左侧消去 m 得出。
*)
Lemma iso_ortho_right {C : Category} {a b x y : C} (e : a ~> b) (m : x ~> y) :
  IsIsomorphism m → e ⫫ m.
Proof.
  intros Hm.
  constructor; intros u v comm.
  unshelve refine {| unique_obj := @two_sided_inverse _ _ _ m Hm ∘ v |}.
  - split.
    + (* (m⁻¹ ∘ v) ∘ e ≈ u / (m⁻¹ ∘ v) ∘ e ≈ u *)
      rewrite <- comp_assoc.
      rewrite <- comm.
      rewrite comp_assoc.
      rewrite (@is_left_inverse _ _ _ m Hm).
      cat.
    + (* m ∘ (m⁻¹ ∘ v) ≈ v / m ∘ (m⁻¹ ∘ v) ≈ v *)
      rewrite comp_assoc.
      rewrite (@is_right_inverse _ _ _ m Hm).
      cat.
  - intros d' [Hd'e Hmd'].
    (* m⁻¹ ∘ v ≈ d', by composing m⁻¹ with m ∘ d' ≈ v / m⁻¹ ∘ v ≈ d'，通过将 m⁻¹ 与 m ∘ d' ≈ v 组合 *)
    rewrite <- Hmd'.
    rewrite comp_assoc.
    rewrite (@is_left_inverse _ _ _ m Hm).
    cat.
Qed.

(*
The left class is closed under composition: a square over e2 ∘ e1 lifts
   first through e1 (against the top-right corner v ∘ e2) and then through
   e2; uniqueness threads back the same way.

--------
左类在复合下是封闭的：e2 ∘ e1 上的一个方块首先通过 e1 提升（相对于右上角 v ∘ e2），然后通过 e2；唯一性以相同的方式回溯。
*)
Lemma ortho_left_compose {C : Category} {a b c x y : C}
  (e1 : a ~> b) (e2 : b ~> c) (m : x ~> y) :
  e1 ⫫ m → e2 ⫫ m → (e2 ∘ e1) ⫫ m.
Proof.
  intros H1 H2.
  constructor; intros u v comm.
  (* The outer square, reassociated as a square over e1. / 外部的正方形，重新关联为位于 e1 上的正方形。 *)
  assert (comm1 : m ∘ u ≈ (v ∘ e2) ∘ e1). {
    rewrite <- comp_assoc.
    exact comm.
  }
  pose proof (@ortho_lift _ _ _ _ _ e1 m H1 u (v ∘ e2) comm1) as U1.
  destruct (unique_property U1) as [U1e U1m].
  (* The lift through e1 forms a square over e2; lift again. / 通过 e1 的升力在 e2 上形成一个方形；再次升起。 *)
  pose proof (@ortho_lift _ _ _ _ _ e2 m H2 (unique_obj U1) v U1m) as U2.
  destruct (unique_property U2) as [U2e U2m].
  unshelve refine {| unique_obj := unique_obj U2 |}.
  - split.
    + (* d2 ∘ (e2 ∘ e1) ≈ u / d2 ∘ (e2 ∘ e1) ≈ u *)
      rewrite comp_assoc.
      rewrite U2e.
      exact U1e.
    + exact U2m.
  - intros d [Hde Hdm].
    (*
Any filler d of the outer square: d ∘ e2 fills the e1-square, so
       d ∘ e2 ≈ d1 by e1-uniqueness; then d fills the e2-square, so d ≈ d2
       by e2-uniqueness.

--------
外平方的任意填充 d：d ∘ e2 填充了 e1-平方，因此 d ∘ e2 ≈ d1，依据 e1 唯一性；然后 d 填充了 e2-平方，因此 d ≈ d2，依据 e2 唯一性。
*)
    apply (uniqueness U2); split.
    + symmetry.
      apply (uniqueness U1); split.
      * rewrite <- comp_assoc.
        exact Hde.
      * rewrite comp_assoc.
        rewrite Hdm.
        reflexivity.
    + exact Hdm.
Qed.

(*
The left class is closed under retracts in the arrow category: if e' is a
   retract of e — witnessed by a section (ia, ib) and a retraction (ra, rb)
   of arrows with ra ∘ ia ≈ id, rb ∘ ib ≈ id, e ∘ ia ≈ ib ∘ e' and
   e' ∘ ra ≈ rb ∘ e — then e ⫫ m entails e' ⫫ m: a square over e' is
   whiskered by (ra, rb) into a square over e, lifted there, and the filler
   is restricted along ib.

--------
在箭头范畴中，左类在收缩下是封闭的：如果 e' 是 e 的一个收缩——由一个箭头的截面 (ia, ib) 和一个重traction (ra, rb) 证明，其中 ra ∘ ia ≈ id，rb ∘ ib ≈ id，e ∘ ia ≈ ib ∘ e' 并且 e' ∘ ra ≈ rb ∘ e——那么 e ⫫ m 推出 e' ⫫ m：在 e' 上的一个方框通过 (ra, rb) 被“胡须化”成在 e 上的方框，在那里被提升，并且填充被沿 ib 限制。
*)
Lemma ortho_left_retract {C : Category} {a b a' b' x y : C}
  (e : a ~> b) (e' : a' ~> b') (m : x ~> y)
  (ia : a' ~> a) (ib : b' ~> b) (ra : a ~> a') (rb : b ~> b')
  (ra_ia : ra ∘ ia ≈ id) (rb_ib : rb ∘ ib ≈ id)
  (sq_i : e ∘ ia ≈ ib ∘ e') (sq_r : e' ∘ ra ≈ rb ∘ e) :
  e ⫫ m → e' ⫫ m.
Proof.
  intros He.
  constructor; intros u v comm.
  (*
The whiskered square over e commutes:
     m ∘ (u ∘ ra) ≈ (v ∘ e') ∘ ra ≈ v ∘ (rb ∘ e) ≈ (v ∘ rb) ∘ e.

--------
带胡子的平方在 e 上交换：
     m ∘ (u ∘ ra) ≈ (v ∘ e') ∘ ra ≈ v ∘ (rb ∘ e) ≈ (v ∘ rb) ∘ e。
*)
  assert (comm0 : m ∘ (u ∘ ra) ≈ (v ∘ rb) ∘ e). {
    rewrite comp_assoc.
    rewrite comm.
    rewrite <- comp_assoc.
    rewrite sq_r.
    rewrite comp_assoc.
    reflexivity.
  }
  pose proof (@ortho_lift _ _ _ _ _ e m He (u ∘ ra) (v ∘ rb) comm0) as U.
  destruct (unique_property U) as [Ue Um].
  unshelve refine {| unique_obj := unique_obj U ∘ ib |}.
  - split.
    + (* (d ∘ ib) ∘ e' ≈ u, via ib ∘ e' ≈ e ∘ ia / (d ∘ ib) ∘ e' ≈ u，通过 ib ∘ e' ≈ e ∘ ia *)
      rewrite <- comp_assoc.
      rewrite <- sq_i.
      rewrite comp_assoc.
      rewrite Ue.
      rewrite <- comp_assoc.
      rewrite ra_ia.
      cat.
    + (* m ∘ (d ∘ ib) ≈ v / m ∘ (d ∘ ib) ≈ v *)
      rewrite comp_assoc.
      rewrite Um.
      rewrite <- comp_assoc.
      rewrite rb_ib.
      cat.
  - intros g [Hge Hgm].
    (*
Any filler g of the e'-square: g ∘ rb fills the e-square, so
       g ∘ rb ≈ d by e-uniqueness, whence g ≈ g ∘ rb ∘ ib ≈ d ∘ ib.

--------
e'-方格的任意补充 g：g ∘ rb 补充了 e-方格，因此由 e-唯一性，g ∘ rb ≈ d，故 g ≈ g ∘ rb ∘ ib ≈ d ∘ ib。
*)
    assert (Hgrb : unique_obj U ≈ g ∘ rb). {
      apply (uniqueness U); split.
      - (* (g ∘ rb) ∘ e ≈ u ∘ ra, via rb ∘ e ≈ e' ∘ ra / (g ∘ rb) ∘ e ≈ u ∘ ra，通过 rb ∘ e ≈ e' ∘ ra *)
        rewrite <- comp_assoc.
        rewrite <- sq_r.
        rewrite comp_assoc.
        rewrite Hge.
        reflexivity.
      - rewrite comp_assoc.
        rewrite Hgm.
        reflexivity.
    }
    rewrite Hgrb.
    rewrite <- comp_assoc.
    rewrite rb_ib.
    cat.
Qed.
