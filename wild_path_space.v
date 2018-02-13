Require Import HoTT.
Require Import ED.polynomial.
Require Import ED.hit_structure.
Require Import ED.wild_groupoid.

Definition path_prod'_inv
           {A B : Type}
           {a₁ a₂ : A} {b₁ b₂ : B}
           (p₁ : a₁ = a₂) (p₂ : b₁ = b₂)
  : path_prod' p₁^ p₂^ = (path_prod' p₁ p₂)^.
Proof.
  induction p₁, p₂ ; simpl.
  reflexivity.
Defined.

Definition path_prod'_concat
           {A B : Type}
           {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
           (p₁ : a₁ = a₂) (p₂ : b₁ = b₂)
           (q₁ : a₂ = a₃) (q₂ : b₂ = b₃)
  : path_prod' (p₁ @ q₁) (p₂ @ q₂)
    =
    (path_prod' p₁ p₂) @ (path_prod' q₁ q₂).
Proof.
  induction p₁, p₂, q₁, q₂ ; simpl.
  reflexivity.
Defined.

Definition test
           {P : polynomial} {A : Type}
  : relation_morph
      idmap
      (hom (lift_groupoid (path_groupoid A) P))
      (hom (path_groupoid (poly_act P A))).
Proof.
  intros ? ? p.
  induction P ; simpl in *.
  - exact p.
  - exact p.
  - specialize (IHP1 (fst x) (fst y) (fst p)).
    specialize (IHP2 (snd x) (snd y) (snd p)).
    exact (path_prod' IHP1 IHP2).
  - destruct x as [x | x], y as [y | y].
    + exact (ap inl (IHP1 x y p)).
    + contradiction.
    + contradiction.
    + exact (ap inr (IHP2 x y p)).
Defined.

Global Instance wat
       {P : polynomial} {A : Type}
  : is_Agrpd_morph (@test P A).
Proof.
  unshelve esplit.
  - induction P.
    + reflexivity.
    + reflexivity.
    + intros.
      specialize (IHP1 (fst x)).
      specialize (IHP2 (snd x)).
      simpl.
      rewrite IHP1, IHP2.
      reflexivity.
    + intros.
      destruct x as [x | x] ; simpl.
      * specialize (IHP1 x).
        rewrite IHP1.
        reflexivity.
      * specialize (IHP2 x).
        rewrite IHP2.
        reflexivity.
  - induction P.
    + reflexivity.
    + reflexivity.
    + intros x y p.
      specialize (IHP1 (fst x) (fst y) (fst p)).
      specialize (IHP2 (snd x) (snd y) (snd p)).
      simpl.
      rewrite IHP1, IHP2.
      apply path_prod'_inv.
    + intros [x | x] [y | y] p ; try contradiction.
      * specialize (IHP1 x y p).
        simpl.
        rewrite IHP1.
        apply ap_V.
      * specialize (IHP2 x y p).
        simpl.
        rewrite IHP2.
        apply ap_V.
  - induction P.
    + reflexivity.
    + reflexivity.
    + intros x y z p q.
      specialize (IHP1 (fst x) (fst y) (fst z) (fst p) (fst q)).
      specialize (IHP2 (snd x) (snd y) (snd z) (snd p) (snd q)).
      simpl.
      rewrite IHP1, IHP2.
      apply path_prod'_concat.
    + intros [x | x] [y | y] [z | z] p q ; try contradiction.
      * specialize (IHP1 x y z p q).
        simpl.
        rewrite IHP1.
        apply ap_pp.
      * specialize (IHP2 x y z p q).
        simpl.
        rewrite IHP2.
        apply ap_pp.
Defined.

Definition lift_constr
           {P : polynomial} {A : Type}
           (f : poly_act P A -> A)
  : relation_morph f
                   (hom (lift_groupoid (path_groupoid A) P))
                   (hom (path_groupoid A)).
Proof.
  intros ? ? p.
  simpl.
  refine (ap f _).
  exact (test _ _ p).
Defined.

Global Instance constr_grpd
       {P : polynomial} {A : Type}
       (f : poly_act P A -> A)
  : is_grpd_morph f (lift_constr f).
Proof.
  unshelve esplit.
  - intros.
    unfold lift_constr.
    rewrite morph_e ; try (apply _).
    reflexivity.
  - intros.
    unfold lift_constr.
    rewrite morph_i ; try (apply _).
    apply ap_V.
  - intros.
    unfold lift_constr.
    rewrite morph_c ; try (apply _).
    apply ap_pp.
Defined.


Definition inv_e (X : Type) (G : groupoid X) (x : X)
  : inv (e x) = e x
  := (ec _ _ _ _ _)^ @ ci _ G _ _ _.

Section path_algebra.
  Variable (Σ : hit_signature) (H : HIT Σ).

  Definition path_alg : Halg Σ H.
  Proof.
    unshelve esplit.
    - exact (path_groupoid H).
    - intros i u x p.
      apply lift_constr.
      apply p.
    - intros j u.
      exact (hit_path j u).
    - intros.
      apply constr_grpd.
    - intros j u ; simpl.
      rewrite transport_paths_FlFr.
      hott_simpl.
  Defined.

  Variable (G : Halg Σ H).
  Context `{Univalence}.

  Definition unique_initial
             (F₁ F₂ : relation_morph idmap (hom (H_grpd Σ H path_alg)) (hom (H_grpd Σ H G)))
             `{is_Agrpd_morph _ _ _ F₁}
             `{is_Agrpd_morph _ _ _ F₂}
    : F₁ = F₂.
  Proof.
    apply path_forall ; intro.
    apply path_forall ; intro.
    apply path_forall ; intro p.
    induction p ; simpl.
    rewrite (morph_e _ F₁), (morph_e _ F₂).
    reflexivity.
  Defined.

  Definition weak_initial_map
    : relation_morph idmap (hom (H_grpd Σ H path_alg)) (hom (H_grpd Σ H G)).
  Proof.
    intros ? ? p.
    refine (transport (fun z => hom (H_grpd _ _ G) x z) p (e x)).
  Defined.

  Global Instance idd_grpd_morph
    : is_Agrpd_morph weak_initial_map.
  Proof.
    unshelve esplit.
    - reflexivity.
    - intros ? ? p.
      induction p.
      exact (inv_e _ _ x)^.
    - intros ? ? ? p q.
      induction p, q.
      simpl.
      apply (ce _ _ _ _ _)^.
  Defined.

  Global Instance idd_Halg_morph
    : isHalg_morph Σ H path_alg G weak_initial_map.
  Proof.
    unshelve esplit.
    - intros i ? ? p.
      simpl in *.
      unfold lift_constr.
      admit.
    - intros j u.
      simpl.
      exact (coherent_alg Σ H _ j u).
  Admitted.
End path_algebra.