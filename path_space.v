Require Import HoTT.
Require Import ED.polynomial.
Require Import ED.hit_structure.
Require Import ED.groupoid.

Definition ap_tr
           {A B : Type}
           (f : A -> B)
           {a₁ a₂ : A}
           (p : hom (path_groupoid A) a₁ a₂)
  : hom (path_groupoid B) (f a₁) (f a₂).
Proof.
  simple refine (Trunc_rec _ p).
  exact (tr o (ap f)).
Defined.

Definition ap_tr_inv
           {A B : Type}
           (f : A -> B)
           {a₁ a₂ : A}
           (p : hom (path_groupoid A) a₁ a₂)
  : ap_tr f (inv p) = inv (ap_tr f p).
Proof.
  simple refine (Trunc_ind (fun _ => _) _ p) ; intros q ; simpl.
  exact (ap tr (ap_V _ _)).
Defined.

Definition ap_tr_concat
           {A B : Type}
           (f : A -> B)
           {a₁ a₂ a₃ : A}
           (p₁ : hom (path_groupoid A) a₁ a₂)
           (p₂ : hom (path_groupoid A) a₂ a₃)
  : ap_tr f (p₁ · p₂) = (ap_tr f p₁ · ap_tr f p₂).
Proof.
  simple refine (Trunc_ind (fun _ => _) _ p₁) ; intros q₁ ; simpl.
  simple refine (Trunc_ind (fun _ => _) _ p₂) ; intros q₂ ; simpl.
  exact (ap tr (ap_pp _ _ _)).
Defined.

Definition path_prod'_tr
           {A B : Type}
           {a₁ a₂ : A} {b₁ b₂ : B}
           (p₁ : hom (path_groupoid A) a₁ a₂) (p₂ : hom (path_groupoid B) b₁ b₂)
  : hom (path_groupoid (A*B)) (a₁,b₁) (a₂,b₂).
Proof.
  simple refine (Trunc_rec _ p₁) ; intros q₁.
  simple refine (Trunc_rec _ p₂) ; intros q₂.
  exact (tr (path_prod' q₁ q₂)).
Defined.

Definition path_prod'_tr_e
           {A B : Type}
           (a : A) (b : B)
  : path_prod'_tr (e a) (e b) = e (a, b).
Proof.
  simpl.
  reflexivity.
Defined.

Definition path_prod'_inv
           {A B : Type}
           {a₁ a₂ : A} {b₁ b₂ : B}
           (p₁ : a₁ = a₂) (p₂ : b₁ = b₂)
  : path_prod' p₁^ p₂^ = (path_prod' p₁ p₂)^.
Proof.
  induction p₁, p₂ ; simpl.
  reflexivity.
Defined.

Definition path_prod'_tr_inv
           {A B : Type}
           {a₁ a₂ : A} {b₁ b₂ : B}
           (p₁ : hom (path_groupoid A) a₁ a₂) (p₂ : hom (path_groupoid B) b₁ b₂)
  : path_prod'_tr (inv p₁) (inv p₂) = inv (path_prod'_tr p₁ p₂).
Proof.
  simple refine (Trunc_ind (fun _ => _) _ p₁) ; intros q₁.
  simple refine (Trunc_ind (fun _ => _) _ p₂) ; intros q₂.
  simpl.
  apply (ap tr).
  apply path_prod'_inv.
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

Definition path_prod'_tr_concat
           {A B : Type}
           {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
           (p₁ : hom (path_groupoid A) a₁ a₂) (p₂ : hom (path_groupoid B) b₁ b₂)
           (q₁ : hom (path_groupoid A) a₂ a₃) (q₂ : hom (path_groupoid B) b₂ b₃)
  : path_prod'_tr (p₁ · q₁) (p₂ · q₂)
    =
    ((path_prod'_tr p₁ p₂) · (path_prod'_tr q₁ q₂)).
Proof.
  simple refine (Trunc_ind (fun _ => _) _ p₁) ; intros r₁.
  simple refine (Trunc_ind (fun _ => _) _ p₂) ; intros r₂.
  simple refine (Trunc_ind (fun _ => _) _ q₁) ; intros s₁.
  simple refine (Trunc_ind (fun _ => _) _ q₂) ; intros s₂.
  simpl.
  apply (ap tr).
  apply path_prod'_concat.
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
    exact (path_prod'_tr IHP1 IHP2).
  - destruct x as [x | x], y as [y | y].
    + exact (ap_tr inl (IHP1 x y p)).
    + contradiction.
    + contradiction.
    + exact (ap_tr inr (IHP2 x y p)).
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
      apply path_prod'_tr_e.
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
      apply path_prod'_tr_inv.
    + intros [x | x] [y | y] p ; try contradiction.
      * specialize (IHP1 x y p).
        simpl.
        rewrite IHP1.
        apply ap_tr_inv.
      * specialize (IHP2 x y p).
        simpl.
        rewrite IHP2.
        apply ap_tr_inv.
  - induction P.
    + reflexivity.
    + reflexivity.
    + intros x y z p q.
      specialize (IHP1 (fst x) (fst y) (fst z) (fst p) (fst q)).
      specialize (IHP2 (snd x) (snd y) (snd z) (snd p) (snd q)).
      simpl.
      rewrite IHP1, IHP2.
      apply path_prod'_tr_concat.
    + intros [x | x] [y | y] [z | z] p q ; try contradiction.
      * specialize (IHP1 x y z p q).
        simpl.
        rewrite IHP1.
        apply ap_tr_concat.
      * specialize (IHP2 x y z p q).
        simpl.
        rewrite IHP2.
        apply ap_tr_concat.
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
  refine (ap_tr f _).
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
    apply ap_tr_inv.
  - intros.
    unfold lift_constr.
    rewrite morph_c ; try (apply _).
    apply ap_tr_concat.
Defined.

Lemma test2
      {A : Type}
      {B : A -> Type}
      {a b : A}
      (p : a = b)
      (x : B a)
  : transport (fun (z : A) => Trunc 0 (B z)) p (tr x)
    =
    tr (transport B p x).
Proof.
  induction p.
  reflexivity.
Defined.              

Lemma test3
      {A B : Type}
      {f g : A -> B}
      {a₁ a₂ : A}
      (p : a₁ = a₂)
      (q : Trunc 0 (f a₁ = g a₁))
  : transport (fun (z : A) => Trunc 0 (f z = g z)) p q
    = (tr (ap f p^) · q · tr (ap g p)).
Proof.
  strip_truncations.
  rewrite (@test2 A).
  rewrite transport_paths_FlFr.
  hott_simpl.
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
    - intros j u.
      apply tr.
      exact (hit_path j u).
    - intros i.
      unshelve esplit.
      + apply lift_constr.
      + apply tr.
        apply constr_grpd.
    - intros j u ; simpl.
      rewrite test3.
      hott_simpl.
      rewrite !ec.
      reflexivity.
  Defined.

  Variable (G : Halg Σ H).
  Context `{Univalence}.

  Definition unique_initial
             (F₁ F₂ : Agrpd_morph (H_grpd Σ H path_alg) (H_grpd Σ H G))
    : F₁ = F₂.
  Proof.
    simple refine (path_sigma' _ _ _).
    - apply path_forall ; intro.
      apply path_forall ; intro.
      apply path_forall ; intro p.
      destruct F₁ as [F₁ P₁].
      destruct F₂ as [F₂ P₂].
      strip_truncations.
      induction p ; simpl.
      rewrite (morph_e _ F₁), (morph_e _ F₂).
      reflexivity.
    - apply path_ishprop.
  Defined.

  Definition weak_initial_map
    : relation_morph idmap (hom (H_grpd Σ H path_alg)) (hom (H_grpd Σ H G)).
  Proof.
    intros ? ? p.
    refine (Trunc_rec _ p) ; intros q.
    refine (transport (fun z => hom (H_grpd _ _ G) x z) q (e x)).
  Defined.

  Global Instance idd_grpd_morph
    : is_Agrpd_morph weak_initial_map.
  Proof.
    unshelve esplit.
    - reflexivity.
    - intros ? ? p.
      strip_truncations.
      induction p.
      exact (inv_e _ _ x)^.
    - intros ? ? ? p q.
      strip_truncations.
      induction p, q.
      simpl.
      apply (ce _ _ _ _ _)^.
  Defined.

  Definition weak_initial_grpd
    : Agrpd_morph (H_grpd Σ H path_alg) (H_grpd Σ H G)
    := (weak_initial_map;tr _).

  Global Instance idd_Halg_morph
    : isHalg_morph Σ H path_alg G weak_initial_grpd.
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