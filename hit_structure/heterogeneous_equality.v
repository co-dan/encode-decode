Require Import HoTT.

Definition coe {A B : Type} (α : A = B) : A -> B := transport idmap α.

Inductive h_eq : forall (A B : Type), A = B -> A -> B -> Type :=
| refl : forall (A : Type) (a : A), h_eq A A idpath a a.

Definition h_eq_l : forall (A B : Type), A = B -> A -> B -> Type
  := fun A B α a b => coe α a = b.

Arguments h_eq {A B} _ _ _.
Arguments refl {A} {a}.
Arguments h_eq_l {A B} _ _ _.

Global Instance reflexive_h_eq
       {A : Type}
  : Reflexive (@h_eq A A idpath)
  := fun a => refl.

Definition h_eq_to_h_eq_l
           {A B : Type}
           {α : A = B}
           {a : A} {b : B}
  : h_eq α a b -> h_eq_l α a b.
Proof.
  induction 1.
  reflexivity.
Defined.

Definition h_eq_l_to_h_eq
           {A B : Type}
           {α : A = B}
           {a : A} {b : B}
  : h_eq_l α a b -> h_eq α a b.
Proof.
  induction 1.
  induction α.
  reflexivity.
Defined.

Global Instance h_eq_to_h_eq_l_equiv
       {A B : Type}
       {α : A = B}
       {a : A} {b : B}
  : IsEquiv (@h_eq_to_h_eq_l A B α a b).
Proof.
  apply isequiv_biinv.
  esplit ; exists h_eq_l_to_h_eq.
  - intros p.
    induction p.
    reflexivity.
  - intros p.
    induction p, α.
    reflexivity.
Defined.




Inductive path_over
          (A : Type) (C : A -> Type)
  : forall (a₁ a₂ : A), a₁ = a₂ -> C a₁ -> C a₂ -> Type
  := refl_po : forall (a : A) (c : C a), path_over A C a a idpath c c.

Arguments path_over {A} C {a₁ a₂} _ _ _.
Arguments refl_po {A C a c}.

Global Instance reflexive_path_over
       {A : Type} (C : A -> Type)
       (a : A)
  : Reflexive (@path_over A C a a idpath)
  := fun c => @refl_po A C a c.

Definition path_over_transport
           {A : Type} (C : A -> Type)
           {a₁ a₂ : A} (α : a₁ = a₂)
           (c₁ : C a₁) (c₂ : C a₂)
  : Type
  := transport C α c₁ = c₂.

Definition path_over_to_transport
           {A : Type} (C : A -> Type)
           {a₁ a₂ : A} (α : a₁ = a₂)
           (c₁ : C a₁) (c₂ : C a₂)
  : path_over C α c₁ c₂ -> path_over_transport C α c₁ c₂.
Proof.
  induction 1.
  reflexivity.
Defined.

Definition transport_to_path_over
           {A : Type} (C : A -> Type)
           {a₁ a₂ : A} (α : a₁ = a₂)
           (c₁ : C a₁) (c₂ : C a₂)
  : path_over_transport C α c₁ c₂ -> path_over C α c₁ c₂.
Proof.
  induction α.
  induction 1.
  reflexivity.
Defined.

Global Instance path_over_to_transport_equiv
       {A : Type} (C : A -> Type)
       {a₁ a₂ : A} (α : a₁ = a₂)
       (c₁ : C a₁) (c₂ : C a₂)
  : IsEquiv (@path_over_to_transport A C a₁ a₂ α c₁ c₂).
Proof.
  apply isequiv_biinv.
  split ; exists (transport_to_path_over C α c₁ c₂).
  - intros p.
    induction p.
    reflexivity.
  - intros p.
    induction α, p.
    reflexivity.
Defined.

Definition path_over_h_eq_l
           {A : Type} (C : A -> Type)
           {a₁ a₂ : A} (α : a₁ = a₂)
           (c₁ : C a₁) (c₂ : C a₂)
  : Type
  := h_eq_l (ap C α) c₁ c₂.

Definition path_over_t_to_h_eq_l
           {A : Type} (C : A -> Type)
           {a₁ a₂ : A} (α : a₁ = a₂)
           (c₁ : C a₁) (c₂ : C a₂)
  : path_over_transport C α c₁ c₂ -> path_over_h_eq_l C α c₁ c₂.
Proof.
  induction α.
  exact idmap.
Defined.

Definition h_eq_l_to_path_over_t
           {A : Type} (C : A -> Type)
           {a₁ a₂ : A} (α : a₁ = a₂)
           (c₁ : C a₁) (c₂ : C a₂)
  : path_over_h_eq_l C α c₁ c₂ -> path_over_transport C α c₁ c₂.
Proof.
  induction α.
  exact idmap.
Defined.

Global Instance path_over_t_to_h_eq_l_equiv
       {A : Type} (C : A -> Type)
       {a₁ a₂ : A} (α : a₁ = a₂)
       (c₁ : C a₁) (c₂ : C a₂)
  : IsEquiv (path_over_t_to_h_eq_l C α c₁ c₂).
Proof.
  apply isequiv_biinv.
  split ; exists (h_eq_l_to_path_over_t C α c₁ c₂).
  - induction α.
    intro.
    reflexivity.
  - induction α.
    intro.
    reflexivity.
Defined.




Inductive square (A : Type)
  : forall (a₁ a₂ a₃ a₄ : A), a₁ = a₂ -> a₂ = a₄ -> a₁ = a₃ -> a₃ = a₄ -> Type
  := id_square : forall (a : A), square A a a a a idpath idpath idpath idpath.

Arguments square {A a₁ a₂ a₃ a₄} _ _ _ _.
Arguments id_square {A a}.

Definition whisker_square
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ q₁ : a₁ = a₂} {p₂ q₂ : a₂ = a₄}
           {p₃ q₃ : a₁ = a₃} {p₄ q₄ : a₃ = a₄}
           (r₁ : p₁ = q₁) (r₂ : p₂ = q₂)
           (r₃ : p₃ = q₃) (r₄ : p₄ = q₄)
           (s : square p₁ p₂ p₃ p₄)
  : square q₁ q₂ q₃ q₄.
Proof.
  induction r₁, r₂, r₃, r₄.
  exact s.
Defined.

Definition square_to_path
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : p₁ @ p₂ = p₃ @ p₄.
Proof.
  induction s.
  reflexivity.
Defined.

Definition square_to_path_l
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : p₃^ @ p₁ @ p₂ = p₄.
Proof.
  induction s.
  reflexivity.
Defined.

Definition square_to_path_r
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : p₁ = p₃ @ p₄ @ p₂^.
Proof.
  induction s.
  reflexivity.
Defined.

Definition path_to_square
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : p₁ @ p₂ = p₃ @ p₄)
  : square p₁ p₂ p₃ p₄.
Proof.
  induction p₁, p₂, p₃ ; simpl in *.
  refine (whisker_square idpath idpath idpath _ id_square).
  exact (s @ concat_1p p₄).
Defined.

Definition path_to_square_r
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : p₃^ @ p₁ @ p₂ = p₄)
  : square p₁ p₂ p₃ p₄.
Proof.
  induction p₁, p₂, p₃ ; simpl in *.
  refine (whisker_square idpath idpath idpath _ id_square).
  exact s.
Defined.

Definition hrefl_square {A : Type} {a₁ a₂ : A} (p : a₁ = a₂)
  : square p idpath idpath p.
Proof.
  induction p.
  exact id_square.
Defined.

Definition vrefl_square {A : Type} {a₁ a₂ : A} (p : a₁ = a₂)
  : square idpath p p idpath.
Proof.
  induction p.
  exact id_square.
Defined.

Definition ap_square
           {A B : Type}
           (f : A -> B)
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : square (ap f p₁) (ap f p₂) (ap f p₃) (ap f p₄).
Proof.
  induction s.
  exact id_square.
Defined.

Definition square_inv_v
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : square p₁^ p₃ p₂ p₄^.
Proof.
  induction s.
  exact id_square.
Defined.

Definition square_inv_h
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : square p₃^ p₁ p₄ p₂^.
Proof.
  induction s.
  exact id_square.
Defined.

Definition pair_square
           {A B : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s₁ : square p₁ p₂ p₃ p₄)
           {b₁ b₂ b₃ b₄ : B}
           {q₁ : b₁ = b₂} {q₂ : b₂ = b₄}
           {q₃ : b₁ = b₃} {q₄ : b₃ = b₄}
           (s₂ : square q₁ q₂ q₃ q₄)
  : square (path_prod' p₁ q₁) (path_prod' p₂ q₂) (path_prod' p₃ q₃) (path_prod' p₄ q₄).
Proof.
  induction s₁, s₂.
  exact id_square.
Defined.

Definition square_v
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s₁ : square p₁ p₂ p₃ p₄)
           {a₅ a₆ : A}
           {p₅ : a₂ = a₅} {p₆ : a₅ = a₆} {p₇ : a₄ = a₆}
           (s₂ : square p₅ p₆ p₂ p₇)
  : square (p₁ @ p₅) p₆ p₃ (p₄ @ p₇).
Proof.
  induction s₁.
  refine (whisker_square _ _ _ _ s₂).
  - exact (concat_1p _)^.
  - reflexivity.
  - reflexivity.
  - exact (concat_1p _)^.
Defined.

Definition square_v'
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s₁ : square p₁ p₂ p₃ p₄)
           {a₅ a₆ : A}
           {p₅ : a₂ = a₅} {p₆ : a₅ = a₆} {p₇ : a₄ = a₆}
           (s₂ : square p₅ p₆ p₂ p₇)
           {q₁ : a₁ = a₅} {q₂ : a₃ = a₆}
           (H₁ : p₁ @ p₅ = q₁) (H₂ : p₄ @ p₇ = q₂)
  : square q₁ p₆ p₃ q₂.
Proof.
  induction s₁.
  refine (whisker_square _ _ _ _ s₂).
  - exact ((concat_1p _)^ @ H₁).
  - reflexivity.
  - reflexivity.
  - exact ((concat_1p _)^ @ H₂).
Defined.

Definition square_h
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s₁ : square p₁ p₂ p₃ p₄)
           {a₅ a₆ : A}
           {p₅ : a₃ = a₅} {p₆ : a₅ = a₆} {p₇ : a₄ = a₆}
           (s₂ : square p₅ p₆ p₄ p₇)
  : square p₁ (p₂ @ p₇) (p₃ @ p₅) p₆.
Proof.
  induction s₂.
  refine (whisker_square _ _ _ _ s₁).
  - reflexivity.
  - exact (concat_p1 _)^.
  - exact (concat_p1 _)^.
  - reflexivity.
Defined.

Definition square_h'
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s₁ : square p₁ p₂ p₃ p₄)
           {a₅ a₆ : A}
           {p₅ : a₃ = a₅} {p₆ : a₅ = a₆} {p₇ : a₄ = a₆}
           (s₂ : square p₅ p₆ p₄ p₇)
           {q₁ : a₂ = a₆} {q₂ : a₁ = a₅}
           (H₁ : p₂ @ p₇ = q₁) (H₂ : p₃ @ p₅ = q₂)
  : square p₁ q₁ q₂ p₆.
Proof.
  induction s₂.
  refine (whisker_square _ _ _ _ s₁).
  - reflexivity.
  - exact ((concat_p1 _)^ @ H₁).
  - exact ((concat_p1 _)^ @ H₂).
  - reflexivity.
Defined.

Definition square_d
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s₁ : square p₁ p₂ p₃ p₄)
           {a₅ : A}
           {p₅ : a₁ = a₅} {p₆ : a₅ = a₄}
           (s₂ : square p₃ p₄ p₅ p₆)
  : square p₁ p₂ p₅ p₆.
Proof.
  induction s₁.
  exact s₂.
Defined.

Definition square_glue
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s₁ : square p₁ p₂ p₃ p₄)
           {a₅ a₆ : A}
           {p₅ : a₄ = a₆} {p₆ : a₃ = a₅} {p₇ : a₅ = a₆}
           (s₂ : square p₄ p₅ p₆ p₇)
           (q₁ : a₂ = a₆) (q₂ : a₁ = a₅)
           (H₁ : p₂ @ p₅ = q₁) (H₂ : p₃ @ p₆ = q₂)
  : square p₁ q₁ q₂ p₇.
Proof.
  induction s₁.
  refine (whisker_square _ _ _ _ s₂).
  - reflexivity.
  - exact ((concat_1p p₅)^ @ H₁).
  - exact ((concat_1p p₆)^ @ H₂).
  - reflexivity.
Defined.

Definition square_squash
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s₁ : square p₁ p₂ p₃ p₄)
           {a₅ : A}
           {p₅ : a₁ = a₅} {p₆ : a₅ = a₄}
           (s₂ : square p₃ p₄ p₅ p₆)
           {a₆ : A}
           {p₇ : a₁ = a₆} {p₈ : a₆ = a₄}
           (s₃ : square p₇ p₈ p₁ p₂)
  : square p₇ p₈ p₅ p₆
  := square_d s₃ (square_d s₁ s₂).

Definition square_symmetry
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : square p₃ p₄ p₁ p₂.
Proof.
  induction s.
  exact id_square.
Defined.

Global Instance square_symmetry_equiv
       {A : Type}
       {a₁ a₂ a₃ a₄ : A}
       {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
       {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
  : IsEquiv (@square_symmetry A a₁ a₂ a₃ a₄ p₁ p₂ p₃ p₄).
Proof.
  apply isequiv_biinv.
  split ; exists square_symmetry
  ; intro s ;induction s ; reflexivity.
Defined.

Definition fill_square
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           (p₁ : a₁ = a₂) (p₂ : a₂ = a₄)
           (p₃ : a₁ = a₃)
  : {p₄ : a₃ = a₄ & square p₁ p₂ p₃ p₄}.
Proof.
  exists (p₃^ @ p₁ @ p₂).
  induction p₁, p₂, p₃.
  exact id_square.
Defined.


Definition ap_square_hrefl
           {A B : Type}
           (f : A -> B)
           {a₁ a₂ :A}
           {p : a₁ = a₂}
  : ap_square f (hrefl_square p) = hrefl_square (ap f p).
Proof.
  induction p ; simpl.
  reflexivity.
Defined.

Definition ap_square_vrefl
           {A B : Type}
           (f : A -> B)
           {a₁ a₂ :A}
           {p : a₁ = a₂}
  : ap_square f (vrefl_square p) = vrefl_square (ap f p).
Proof.
  induction p ; simpl.
  reflexivity.
Defined.

Definition ap_square_v
           {A B : Type}
           (f : A -> B)
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s₁ : square p₁ p₂ p₃ p₄)
           {a₅ a₆ : A}
           {p₅ : a₂ = a₅} {p₆ : a₅ = a₆} {p₇ : a₄ = a₆}
           (s₂ : square p₅ p₆ p₂ p₇)
  : ap_square f (square_v s₁ s₂)
    =
    whisker_square
      ((ap_pp _ _ _)^)
      idpath
      idpath
      ((ap_pp _ _ _)^)
      (square_v (ap_square f s₁) (ap_square f s₂)).
Proof.
  induction s₁ ; simpl.
  induction p₅, p₇ ; simpl.
  reflexivity.
Defined.

Definition ap_square_h
           {A B : Type}
           (f : A -> B)
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s₁ : square p₁ p₂ p₃ p₄)
           {a₅ a₆ : A}
           {p₅ : a₃ = a₅} {p₆ : a₅ = a₆} {p₇ : a₄ = a₆}
           (s₂ : square p₅ p₆ p₄ p₇)
  : ap_square f (square_h s₁ s₂)
    =
    whisker_square
      idpath
      ((ap_pp _ _ _)^)
      ((ap_pp _ _ _)^)
      idpath
      (square_h (ap_square f s₁) (ap_square f s₂)).
Proof.
  induction s₂.
  induction p₂, p₃ ; simpl.
  reflexivity.
Defined.

Definition ap_square_sym
           {A B : Type}
           (f : A -> B)
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : ap_square f (square_symmetry s) = square_symmetry (ap_square f s).
Proof.
  induction s ; simpl.
  reflexivity.
Defined.

(*
Definition ap_square_inv
           {A B : Type}
           (f : A -> B)
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : ap_square f (square_inv s)
    =
    whisker_square
      idpath
      ((ap_V _ _)^)
      ((ap_V _ _)^)
      idpath
      (square_inv (ap_square f s)).
Proof.
  induction s ; simpl.
  reflexivity.
Defined.
*)

Definition concat_pV_v
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : square_v s (square_inv_v s)
    =
    whisker_square
      ((concat_pV p₁)^)
      idpath
      idpath
      ((concat_pV p₄)^)
      (vrefl_square p₃).
Proof.
  induction s.
  reflexivity.
Defined.

Definition concat_Vp_v
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : square_v (square_inv_v s) s
    =
    whisker_square
      ((concat_Vp p₁)^)
      idpath
      idpath
      ((concat_Vp p₄)^)
      (vrefl_square p₂).
Proof.
  induction s.
  reflexivity.
Defined.

Definition concat_pV_h
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : square_h s (square_inv_h s)
    =
    whisker_square
      idpath
      ((concat_pV p₂)^)
      ((concat_pV p₃)^)
      idpath
      (hrefl_square p₁).
Proof.
  induction s.
  reflexivity.
Defined.

Definition concat_Vp_h
           {A : Type}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₄}
           {p₃ : a₁ = a₃} {p₄ : a₃ = a₄}
           (s : square p₁ p₂ p₃ p₄)
  : square_v (square_inv_h s) (square_symmetry s)
    =
    whisker_square
      ((concat_Vp p₃)^)
      idpath
      idpath
      ((concat_Vp p₂)^)
      (vrefl_square p₄).
Proof.
  induction s.
  reflexivity.
Defined.