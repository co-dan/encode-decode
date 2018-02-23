Require Import HoTT.
Require Import polynomial.

(** Every type induces a reflexive globular set.
    This means that we have types `A_n`, maps `s, t : A_{n+1} -> A_n` and `i : A_n -> A_{n+1}`
    such that `s o i = id` and `t o i = id`.
*)
Fixpoint gset (A : Type) (n : nat)
  : Type
  := match n with
     | 0 => A
     | S n => {p : gset A n * gset A n & (fst p) = (snd p)}
     end.

Definition src {A : Type} {n : nat}
  : gset A (S n) -> gset A n
  := fun p => fst p.1.

Definition trgt {A : Type} {n : nat}
  : gset A (S n) -> gset A n
  := fun p => snd p.1.

Definition idt {A : Type} {n : nat}
  : gset A n -> gset A (S n)
  := fun p => ((p,p);idpath).

Definition src_idt {A : Type} {n : nat}
  : forall (p : gset A n), src(idt p) = p
  := fun p => idpath.

Definition trgt_idt {A : Type} {n : nat}
  : forall (p : gset A n), trgt(idt p) = p
  := fun p => idpath.

(** The arrows `src` and `trgt` are composable.
    This allows us to map every `A_n` to `A_0 = A`.
    Thinking of the elements in `A_n` to be cubes, this function calculates a corner.
 *)
Fixpoint corner {A : Type} {n : nat}
  : gset A n -> A
  := match n with
     | 0 => fun p => p
     | S n => fun p => corner (trgt p)
     end.

(** Beside a source an a target, at each stage we also have a path. *)
Definition gset_p {A : Type} {n : nat}
  : forall (p : gset A (S n)), src p = trgt p
  := fun p => p.2.

(** The assignment of the globular set to a type is functorial. *)
Fixpoint ap_n
         {A B : Type} {n : nat}
         (f : A -> B)
  : gset A n -> gset B n
  := match n with
     | 0 => f
     | S n => fun p => ((ap_n f (src p),ap_n f (trgt p));ap (ap_n f) (gset_p p))
     end.

Definition ap_n_src
           {A B : Type} {n : nat}
           (f : A -> B)
  : forall (p : gset A (S n)), src(ap_n f p) = ap_n f (src p)
  := fun p => idpath.

Definition ap_n_trgt
           {A B : Type} {n : nat}
           (f : A -> B)
  : forall (p : gset A (S n)), trgt(ap_n f p) = ap_n f (trgt p)
  := fun p => idpath.

(** Now we look at the corner. *)
Fixpoint ap_n_corner
         {A B : Type} {n : nat}
         (f : A -> B)
  : forall (p q : gset A n),
    ap_n f p = ap_n f q -> f (corner p) = f (corner q)
  := match n with
     | 0 => fun _ _ => idmap
     | S n => fun p q H => ap_n_corner f _ _(ap (fun z => snd z.1) H)
     end.

(** Same for dependent functions. *)
Fixpoint apD_n
         {A : Type} {B : A -> Type} {n : nat}
         (f : forall (x : A), B x)
  : forall (p : gset A n), gset (B (corner p)) n
  := match n with
     | 0 => f
     | S n => fun p => ((_,apD_n f (trgt p));apD (apD_n f) (gset_p p))
     end.

(** The dependent action in constant fibrations. *) 
Definition apD_is_ap
           {A B : Type} {n : nat}
           (f : A -> B)
  : forall (p : gset A n), apD_n f p = ap_n f p.
Proof.
  induction n as [ | n IHn].
  - exact (fun p => idpath).
  - intros p ; cbn.
    induction (gset_p p) ; cbn.
    rewrite !IHn.
    reflexivity.
Defined.

(** Now we look at the structure of the product.
    First we do some computations.
 *)
Fixpoint gset_prod {A B : Type} {n : nat}
  : gset A n * gset B n -> gset (A * B) n
  := match n with
     | 0 => idmap
     | S n =>
       fun p =>
         ((_,_);ap gset_prod (path_prod' (gset_p (fst p)) (gset_p (snd p))))
     end.

Definition ap_n_fst
           {A B : Type} {n : nat}
           (p : gset A n) (q : gset B n)
  : ap_n fst (gset_prod (p,q)) = p.
Proof.
  induction n as [ | n IHn].
  - reflexivity.
  - destruct p as [[? ?] p], q as [[? ?] q] ; simpl in *.
    induction p, q ; cbn.
    rewrite IHn.
    reflexivity.
Defined.

Definition ap_n_snd
           {A B : Type} {n : nat}
           (p : gset A n) (q : gset B n)
  : ap_n snd (gset_prod (p,q)) = q.
Proof.
  induction n as [ | n IHn].
  - reflexivity.
  - destruct p as [[? ?] p], q as [[? ?] q] ; simpl in *.
    induction p, q ; cbn.
    rewrite IHn.
    reflexivity.
Defined.

Definition prod_gset
           {A B : Type} {n : nat}
           (p : gset (A * B) n)
  : gset A n * gset B n
  := (ap_n fst p, ap_n snd p).

Definition ap_n_hpath_prod
           {A₁ A₂ B₁ B₂ : Type} {n : nat}
           (f₁ : A₁ -> B₁) (f₂ : A₂ -> B₂)
           (p : gset A₁ n) (q : gset A₂ n)
  : ap_n (fun z => (f₁ (fst z), f₂ (snd z))) (gset_prod (p,q))
    =
    gset_prod (ap_n f₁ p,ap_n f₂ q).
Proof.
  induction n as [ | n IHn].
  - reflexivity.
  - destruct p as [[? ?] p], q as [[? ?] q] ; simpl in *.
    induction p, q ; cbn.
    rewrite IHn.
    reflexivity.
Defined.

Definition gset_prod_gset {A B : Type} {n : nat}
  : forall (p : gset A n * gset B n), prod_gset (gset_prod p) = p
  := match n with
     | 0 => fun _ => idpath
     | S n => fun _ => path_prod' (ap_n_fst _ _) (ap_n_snd _ _)
     end.

Definition prod_gset_prod {A B : Type} {n : nat}
  : forall (p : gset (A * B) n), gset_prod (prod_gset p) = p.
Proof.
  induction n as [ | n IHn].
  - reflexivity.
  - intros p.
    destruct p as [[? ?] p] ; simpl in *.
    induction p ; cbn.
    rewrite IHn.
    reflexivity.
Defined.

Global Instance gset_prod_equiv {A B : Type} {n : nat}
  : IsEquiv (@gset_prod A B n).
Proof.
  apply isequiv_biinv.
  split ; exists (prod_gset) ; intro.
  - apply gset_prod_gset.
  - apply prod_gset_prod.
Defined.

(** Next we consider sums. *)
Definition sum_gset
           {A B : Type} {n : nat}
           (p : gset A n + gset B n)
  : gset (A + B) n
  := match p with
     | inl p => ap_n inl p
     | inr p => ap_n inr p
     end.

Definition gset_sum
           {A B : Type} {n : nat}
  : gset (A + B) n -> gset A n + gset B n.
Proof.
  induction n as [ | n IHn].
  - exact idmap.
  - intros p.
    destruct p as [[x₁ x₂] p] ; simpl in p.
    induction p.
    destruct (IHn x₁) as [g | g].
    + exact (inl((g,g);idpath)).
    + exact (inr((g,g);idpath)).
Defined.

Definition gset_sum_gset
           {A B : Type} {n : nat}
           (p : gset (A + B) n)
  : sum_gset (gset_sum p) = p.
Proof.
  induction n as [ | n IHn].
  - destruct p ; reflexivity.
  - destruct p as [[x₁ x₂] p] ; simpl in *.
    induction p ; simpl.
    specialize (IHn x₁).
    destruct (gset_sum x₁) ; cbn in *
    ; rewrite IHn ; reflexivity.
Defined.

Definition sum_gset_sum
           {A B : Type} {n : nat}
           (p : gset A n + gset B n)
  : gset_sum (sum_gset p) = p.
Proof.
  induction n as [ | n IHn].
  - destruct p ; reflexivity.
  - destruct p as [[[x₁ x₂] p] | [[x₁ x₂] p]] ; simpl in *
    ; induction p ; simpl.
    + rewrite (IHn (inl x₁)) ; reflexivity.
    + rewrite (IHn (inr x₁)) ; reflexivity.
Defined.

Global Instance gset_sum_equiv {A B : Type} {n : nat}
  : IsEquiv (@gset_sum A B n).
Proof.
  apply isequiv_biinv.
  split ; exists (sum_gset) ; intro.
  - apply gset_sum_gset.
  - apply sum_gset_sum.
Defined.

(** Next we look at sigma types. *)
Definition gset_sig
           {A : Type} {B : A -> Type} {n : nat}
  : gset {x : A & B x} n -> {x : A & gset (B x) n}.
Proof.
  induction n as [ | n IHn].
  - exact idmap.
  - intros [[x₁ x₂] p] ; simpl in *.
    induction p.
    pose (g := IHn x₁).
    exact (g.1;((g.2,_);idpath)).
Defined.

Definition sig_gset
           {A : Type} {B : A -> Type} {n : nat}
  : {x : A & gset (B x) n} -> gset {x : A & B x} n.
Proof.
  induction n as [ | n IHn].
  - exact idmap.
  - intros [x [[y₁ y₂] p]].
    simpl in *.
    refine ((IHn (x;y₁),IHn (x;y₂));ap IHn (path_sigma' _ idpath _)).
    exact p.
Defined.

Definition sig_gset_sig {A : Type} {B : A -> Type} {n : nat}
  : forall (p : {x : A & gset (B x) n}), gset_sig(sig_gset p) = p.
Proof.
  induction n as [ | n IHn].
  - reflexivity.
  - intros [a [[x₁ x₂] p]] ; simpl in *.
    induction p ; simpl in *.
    rewrite IHn.
    reflexivity.
Defined.

Definition gset_sig_gset {A : Type} {B : A -> Type} {n : nat}
  : forall (p : gset {x : A & B x} n), sig_gset(gset_sig p) = p.
Proof.
  induction n as [ | n IHn].
  - reflexivity.
  - destruct p as [[x₁ x₂] p] ; simpl in *.
    induction p ; simpl in *.
    rewrite IHn.
    reflexivity.
Defined.

Global Instance gset_sig_equiv {A : Type} {B : A -> Type} {n : nat}
  : IsEquiv (@gset_sig A B n).
Proof.
  apply isequiv_biinv.
  split ; exists (sig_gset) ; intro.
  - apply gset_sig_gset.
  - apply sig_gset_sig.
Defined.

(** Now dependent products. This requires function extensionality. *)
Fixpoint pi_gset
         `{FE : Funext}
         {A : Type} {B : A -> Type} {n : nat}
  : (forall (x : A), gset (B x) n) -> gset (forall (x : A), B x) n
  := match n with
     | 0 => idmap
     | S n => fun H => ((_,_);ap pi_gset (path_forall _ _ (fun z => (H z).2)))
     end.

Fixpoint gset_pi
           `{FE : Funext}
           {A : Type} {B : A -> Type} {n : nat}
  : gset (forall (x : A), B x) n -> forall (x : A), gset (B x) n
  := match n with
     | 0 => idmap
     | S n =>
       fun p x =>
         match p with
         | ((x₁,x₂);p) =>
           match p with
           | idpath => ((gset_pi x₁ x,_);idpath)
           end
         end
     end.

Definition gset_pi_gset
           `{FE : Funext}
           {A : Type} {B : A -> Type} {n : nat}
           (p : gset (forall (x : A), B x) n)
  : pi_gset (gset_pi p) = p.
Proof.
  induction n as [ | n IHn].
  - reflexivity.
  - destruct p as [[x₁ x₂] p] ; simpl in p.
    specialize (IHn x₁).
    induction p ; cbn.
    simple refine (path_sigma' _ _ _).
    + exact (path_prod' IHn IHn).
    + rewrite transport_paths_FlFr, ap_snd_path_prod, ap_fst_path_prod.
      rewrite path_forall_1.
      hott_simpl.
Defined.

Definition pi_gset_pi
           `{FE : Funext}
           {A : Type} {B : A -> Type} {n : nat}
           (p : forall (x : A), gset (B x) n)
  : gset_pi (pi_gset p) = p.
Proof.
  induction n as [ | n IHn].
  - reflexivity.
  - apply path_forall.
    intro z ; cbn.
    rewrite IHn.
    induction (ap pi_gset
                  (path_forall (fun z0 : A => fst (p z0).1) (fun z0 : A => snd (p z0).1)
                               (fun z0 : A => (p z0).2))).
    destruct (p z) as [[x₁ x₂] q].
    cbn in *.
    induction q.
    reflexivity.
Defined.    

Global Instance gset_pi_equiv `{Funext} {A : Type} {B : A -> Type} {n : nat}
  : IsEquiv (@gset_pi _ A B n).
Proof.
  apply isequiv_biinv.
  split ; exists (pi_gset) ; intro.
  - apply gset_pi_gset.
  - apply pi_gset_pi.
Defined.

(** Now we characterize equality in the globular set *)
Definition gpath_eq
           {A : Type} {n : nat}
           {p₁ p₂ q₁ q₂ : gset A n}
           (r₁ : p₁ = p₂)
           (r₂ : q₁ = q₂)
           (s₁ : p₁ = q₁)
           (s₂ : p₂ = q₂)
           (t : s₁^ @ r₁ @ s₂ = r₂)
  : (((p₁,p₂);r₁) : gset A (S n)) = ((q₁,q₂);r₂).
Proof.
  simple refine (path_sigma' _ (path_prod' s₁ s₂) _).
  refine (transport_paths_FlFr _ _ @ _).
  refine (_ @ t).
  refine (ap _ (ap_snd_path_prod _ _) @ _).
  refine (ap (fun z => (z^ @ r₁) @ s₂) _).
  exact (@ap_fst_path_prod _ _ (p₁,p₂) (q₁,q₂) s₁ s₂).
Defined.

Definition eq_gset_l
           {A : Type} {n : nat}
           {p₁ p₂ q₁ q₂ : gset A n}
           (r₁ : p₁ = p₂)
           (r₂ : q₁ = q₂)
           (s : (((p₁,p₂);r₁) : gset A (S n)) = ((q₁,q₂);r₂))
  : p₁ = q₁
  := ap (fun z => (fst z.1)) s.

Definition eq_gset_r
           {A : Type} {n : nat}
           {p₁ p₂ q₁ q₂ : gset A n}
           (r₁ : p₁ = p₂)
           (r₂ : q₁ = q₂)
           (s : (((p₁,p₂);r₁) : gset A (S n)) = ((q₁,q₂);r₂))
  : p₂ = q₂
  := ap (fun z => (snd z.1)) s.

Definition eq_gset_p
           {A : Type} {n : nat}
           {p₁ p₂ q₁ q₂ : gset A n}
           (r₁ : p₁ = p₂)
           (r₂ : q₁ = q₂)
           (s : (((p₁,p₂);r₁) : gset A (S n)) = ((q₁,q₂);r₂))
  : (eq_gset_l r₁ r₂ s)^ @ r₁ @ (eq_gset_r r₁ r₂ s) = r₂.
Proof.
  pose (@apD (gset A (S n)) _ gset_p _ _ s) as p.
  rewrite transport_paths_FlFr in p.
  exact p.
Defined.