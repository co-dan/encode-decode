Require Import HoTT.
From ED Require Import polynomial general.path_space.

(** In a quotient one identifies points.
    Our goal is to define 'wild quotients' in which one can identify points, paths, ...
    For this, we define relations.
 *)
Definition relation (A : Type) : Type
  := forall (n : nat) (p q : gset A n), Type.

Definition relation_morph {A : Type} (R₁ R₂ : relation A)
  := forall {n : nat} {p q : gset A n}, R₁ n p q -> R₂ n p q.

Definition relation_id {A : Type} (R₁ : relation A)
  : relation_morph R₁ R₁
  := fun n p q => idmap.

Definition relation_compose
           {A : Type} {R₁ R₂ R₃ : relation A}
           (g : relation_morph R₂ R₃) (f : relation_morph R₁ R₂)
  : relation_morph R₁ R₃
  := fun n p q => (g n p q) o (f n p q).

Definition relation_id_compose
           {A : Type} {R₁ R₂ : relation A}
           (f : relation_morph R₁ R₂)
  : relation_compose f (relation_id R₁) = f
  := idpath.

Definition relation_compose_id
           {A : Type} {R₁ R₂ : relation A}
           (f : relation_morph R₁ R₂)
  : relation_compose (relation_id R₂) f = f
  := idpath.

Definition relation_compose_assoc
           {A : Type} {R₁ R₂ R₃ R₄ : relation A}
           (f : relation_morph R₁ R₂) (g : relation_morph R₂ R₃)
           (h : relation_morph R₃ R₄)
  : relation_compose h (relation_compose g f)
    =
    relation_compose (relation_compose h g) f
  := idpath.

(** Next we look at the structure of the category of relations. *)
Definition constant_relation (A : Type) : relation A
  := fun n p q => p = q.

(** The sum of relations. *)
Section relation_sum.
  Variable (A : Type)
           (R₁ R₂ : relation A).

  Record relation_sum_alg :=
    { S_alg :> relation A ;
      iS_l : relation_morph R₁ S_alg ;
      iS_r : relation_morph R₂ S_alg }.

  Class relation_sum_alg_morph
        {A₁ A₂ : relation_sum_alg}
        (f : relation_morph A₁ A₂)
    := { f_iS_l : forall (n : nat) (p q : gset A n) (x : R₁ n p q),
           f n p q (iS_l A₁ n p q x) = iS_l A₂ n p q x ;
         f_iS_r : forall (n : nat) (p q : gset A n) (x : R₂ n p q),
             f n p q (iS_r A₁ n p q x) = iS_r A₂ n p q x
       }.

  Definition sum_weak_initial (A₁ : relation_sum_alg)
    : Type
    := forall (A₂ : relation_sum_alg),
      {f : relation_morph A₁ A₂ & relation_sum_alg_morph f}.

  Definition sum_unique_initial (A₁ : relation_sum_alg)
    : Type
    := forall (A₂ : relation_sum_alg)
              (f g : relation_morph A₁ A₂),
      relation_sum_alg_morph f -> relation_sum_alg_morph g
      -> forall (n : nat) (p q : gset A n), f n p q == g n p q.

  Definition relation_sum : relation_sum_alg
    := {| S_alg := fun n p q => R₁ n p q + R₂ n p q ;
                     iS_l := fun n p q => inl ;
                     iS_r := fun n p q => inr|}.

  Definition relation_sum_rec
    : forall (Ag : relation_sum_alg), relation_morph relation_sum Ag
    := fun Ag n p q x =>
         match x with
         | inl x => iS_l Ag n p q x
         | inr x => iS_r Ag n p q x
         end.

  Global Instance relation_sum_rec_morph (Ag : relation_sum_alg)
    : relation_sum_alg_morph (relation_sum_rec Ag)
    := {|f_iS_l := fun _ _ _ _ => idpath ;
         f_iS_r := fun _ _ _ _ => idpath|}.

  Definition relation_sum_weak_initial : sum_weak_initial relation_sum.
  Proof.
    refine (fun Ag => (relation_sum_rec Ag;_)).
    apply _.
  Defined.
  
  Definition relation_sum_unique_initial : sum_unique_initial relation_sum
    := fun A f g Hf Hg n p q x =>
         match x with
         | inl x => f_iS_l n p q x @ (f_iS_l n p q x)^
         | inr x => f_iS_r n p q x @ (f_iS_r n p q x)^
         end.
End relation_sum.

Arguments relation_sum {_} _ _.

(** The product of relations. *)
Section relation_prod.
  Variable (A : Type)
           (R₁ R₂ : relation A).

  Record relation_prod_alg :=
    { P_alg :> relation A ;
      pP_l : relation_morph P_alg R₁ ;
      pP_r : relation_morph P_alg R₂ }.

  Class relation_prod_alg_morph
        {A₁ A₂ : relation_prod_alg}
        (f : relation_morph A₁ A₂)
    := { f_pP_l : forall (n : nat) (p q : gset A n) (x : P_alg A₁ n p q),
           pP_l A₂ n p q (f n p q x) = pP_l A₁ n p q x ;
         f_pP_r : forall (n : nat) (p q : gset A n) (x : P_alg A₁ n p q),
           pP_r A₂ n p q (f n p q x) = pP_r A₁ n p q x
       }.

  Definition prod_weak_final (A₂ : relation_prod_alg)
    : Type
    := forall (A₁ : relation_prod_alg),
      {f : relation_morph A₁ A₂ & relation_prod_alg_morph f}.

  Definition prod_unique_final (A₂ : relation_prod_alg)
    : Type
    := forall (A₁ : relation_prod_alg)
              (f g : relation_morph A₁ A₂),
      relation_prod_alg_morph f -> relation_prod_alg_morph g
      -> forall (n : nat) (p q : gset A n), f n p q == g n p q.

  Definition relation_prod : relation_prod_alg
    := {| P_alg := fun n p q => R₁ n p q * R₂ n p q ;
                     pP_l := fun n p q => fst ;
                     pP_r := fun n p q => snd|}.

  Definition relation_prod_rec
    : forall (Ag : relation_prod_alg), relation_morph Ag relation_prod
    := fun Ag n p q x => (pP_l Ag n p q x,pP_r Ag n p q x).

  Global Instance relation_prod_rec_morph (A : relation_prod_alg)
    : relation_prod_alg_morph (relation_prod_rec A).
  Proof.
    esplit ; reflexivity.
  Defined.

  Definition relation_prod_weak_final : prod_weak_final relation_prod.
  Proof.
    intros Ag.
    exists (relation_prod_rec Ag).
    apply _.
  Defined.

  Definition relation_prod_unique_final : prod_unique_final relation_prod
    := fun _ f g Hf Hg n p q z =>
         path_prod
           _
           _
           (@f_pP_l _ _ f _ n p q z @ (@f_pP_l _ _ g _ n p q z)^)
           (@f_pP_r _ _ f _ n p q z @ (@f_pP_r _ _ g _ n p q z)^).
End relation_prod.

Arguments relation_prod {_} _ _.

(** Lifting relations along a polynomial. *)
Definition lift_sum_R {A B : Type} (R : relation A) (S : relation B)
  : relation (A + B)
  := fun n p q
     => match (gset_sum p), (gset_sum q) with
        | inl x, inl y => R n x y
        | inr x, inr y => S n x y
        | _, _ => Empty
        end.

Definition lift_sum_R_map
           {A B : Type} {R₁ R₂ : relation A} {S₁ S₂ : relation B}
           (f : relation_morph R₁ R₂) (g : relation_morph S₁ S₂)
  : relation_morph (lift_sum_R R₁ S₁) (lift_sum_R R₂ S₂).
Proof.
  unfold lift_sum_R ; intros n p q x.
  destruct (gset_sum p), (gset_sum q).
  - exact (f n _ _ x).
  - contradiction.
  - contradiction.
  - exact (g n _ _ x).
Defined.

Definition lift_prod_R {A B : Type} (R : relation A) (S : relation B)
  : relation (A * B)
  := fun n p q =>
       (R n (ap_n fst p) (ap_n fst q)) * (S n (ap_n snd p) (ap_n snd q)).

Definition lift_prod_R_map
           {A B : Type} {R₁ R₂ : relation A} {S₁ S₂ : relation B}
           (f : relation_morph R₁ R₂) (g : relation_morph S₁ S₂)
  : relation_morph (lift_prod_R R₁ S₁) (lift_prod_R R₂ S₂)
  := fun n p q x => (f n _ _ (fst x),g n _ _ (snd x)).

Definition lift_prod_R_id
           {A B : Type} {R : relation A} {S : relation B}
  : forall (n : nat) (p q : gset (A * B) n),
    lift_prod_R_map (relation_id R) (relation_id S) n p q
    == relation_id (lift_prod_R R S) n p q
  := fun n p q z => idpath.

Definition lift_prod_R_compose
           {A B : Type} {R₁ R₂ R₃ : relation A} {S₁ S₂ S₃ : relation B}
           (f₂ : relation_morph R₂ R₃) (f₁ : relation_morph R₁ R₂)
           (g₂ : relation_morph S₂ S₃) (g₁ : relation_morph S₁ S₂)
  : forall (n : nat) (p q : gset (A * B) n),
    lift_prod_R_map (relation_compose f₂ f₁) (relation_compose g₂ g₁) n p q
    == relation_compose (lift_prod_R_map f₂ g₂) (lift_prod_R_map f₁ g₁) n p q
  := fun n p q z => idpath.

Fixpoint lift_relation (P : polynomial) {A : Type} (R : relation A)
  : relation (poly_act P A)
  := match P with
     | poly_var => R
     | poly_const T => constant_relation T
     | poly_times P₁ P₂ => lift_prod_R (lift_relation P₁ R) (lift_relation P₂ R)
     | poly_plus P₁ P₂ => lift_sum_R (lift_relation P₁ R) (lift_relation P₂ R)
     end.

Fixpoint lift_relation_map
           (P : polynomial)
           {A : Type} {R₁ R₂ : relation A}
           (f : relation_morph R₁ R₂)
  : relation_morph (lift_relation P R₁) (lift_relation P R₂)
  := match P with
     | poly_var => f
     | poly_const T => relation_id _
     | poly_times P₁ P₂
       => lift_prod_R_map (lift_relation_map P₁ f) (lift_relation_map P₂ f)
     | poly_plus P₁ P₂
       => lift_sum_R_map (lift_relation_map P₁ f) (lift_relation_map P₂ f)
     end.

(** The direct image of relations. *)
Section relation_image.
  Variable (A B : Type)
           (f : A -> B)
           (R : relation A).

  Record relation_im_alg :=
    { I_alg :> relation B ;
      I_ap : forall (n : nat) (p q : gset A n),
          R n p q -> I_alg n (ap_n f p) (ap_n f q) }.

  Class relation_im_alg_morph
        {A₁ A₂ : relation_im_alg}
        (g : relation_morph A₁ A₂)
    := f_I_ap : forall (n : nat) (p q : gset A n) (H : R n p q),
           g n (ap_n f p) (ap_n f q) (I_ap A₁ n p q H) = I_ap A₂ n p q H.

  Definition im_weak_initial (A₁ : relation_im_alg)
    : Type
    := forall (A₂ : relation_im_alg),
      {f : relation_morph A₁ A₂ & relation_im_alg_morph f}.

  Definition im_unique_initial (A₁ : relation_im_alg)
    : Type
    := forall (A₂ : relation_im_alg)
              (g₁ g₂ : relation_morph A₁ A₂),
      relation_im_alg_morph g₁ -> relation_im_alg_morph g₂
      -> forall (n : nat) (p q : gset B n), g₁ n p q == g₂ n p q.

  Definition relation_im : relation_im_alg
    := {|I_alg := fun n q₁ q₂ =>
                    {p : gset A n * gset A n &
                         (R n (fst p) (snd p))
                         * (q₁ = ap_n f (fst p))
                         * (q₂ = ap_n f (snd p))} ;
         I_ap := fun n p q H => ((p,q);(H,idpath,idpath))|}.

  Definition relation_im_rec
    : forall (Ag : relation_im_alg), relation_morph relation_im Ag.
  Proof.
    intros Ag n p q [[r₁ r₂] [[H s₁] s₂]].
    rewrite s₁, s₂.
    exact (I_ap Ag n _ _ H).
  Defined.

  Global Instance relation_im_rec_morph (A : relation_im_alg)
    : relation_im_alg_morph (relation_im_rec A)
    := fun _ _ _ _ => idpath.

  Definition relation_im_weak_initial : im_weak_initial relation_im.
  Proof.
    intros Ag.
    exists (relation_im_rec Ag).
    apply _.
  Defined.
End relation_image.

Arguments relation_im {_} _ _.

Section relation_eq.
  Variable (A B : Type)
           (f g : A -> B)
           (R : relation A).

  Record relation_eq_alg :=
    { Eq_alg :> relation B ;
      Eq_ap : forall (n : nat) (p : gset A n),
          Eq_alg n (ap_n f p) (ap_n g p) }.

  Class relation_eq_alg_morph
        {A₁ A₂ : relation_eq_alg}
        (h : relation_morph A₁ A₂)
    := f_Eq_ap : forall (n : nat) (p q : gset A n) (H : R n p q),
           h n (ap_n f p) (ap_n g p) (Eq_ap A₁ n p) = Eq_ap A₂ n p.

  Definition eq_weak_initial (A₁ : relation_eq_alg)
    : Type
    := forall (A₂ : relation_eq_alg),
      {f : relation_morph A₁ A₂ & relation_eq_alg_morph f}.

  Definition eq_unique_initial (A₁ : relation_eq_alg)
    : Type
    := forall (A₂ : relation_eq_alg)
              (g₁ g₂ : relation_morph A₁ A₂),
      relation_eq_alg_morph g₁ -> relation_eq_alg_morph g₂
      -> forall (n : nat) (p q : gset B n), g₁ n p q == g₂ n p q.

  Definition relation_eq : relation_eq_alg
    := {|Eq_alg := fun n q₁ q₂ =>
                     {p : gset A n &
                          (q₁ = ap_n f p)
                          * (q₂ = ap_n g p)} ;
         Eq_ap := fun n p => (p;(idpath,idpath))|}.


  Definition relation_eq_rec
    : forall (Ag : relation_eq_alg), relation_morph relation_eq Ag.
  Proof.
    intros Ag n p q [r [s₁ s₂]].
    rewrite s₁, s₂.
    exact (Eq_ap Ag n r).
  Defined.

  Global Instance relation_eq_rec_morph (A : relation_eq_alg)
    : relation_eq_alg_morph (relation_eq_rec A)
    := fun _ _ _ _ => idpath.

  Definition relation_eq_weak_initial : eq_weak_initial relation_eq.
  Proof.
    intros Ag.
    exists (relation_eq_rec Ag).
    apply _.
  Defined.
End relation_eq.
