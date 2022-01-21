---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.12-truncation-levels where

open import foundations.11-fundamental-theorem public

--------------------------------------------------------------------------------

-- Section 12 Propositions, Sets, and general truncation levels

--------------------------------------------------------------------------------

-- Section 12.1 Propositions

{- Definition 12.1.1 -}

is-prop :
  {i : Level} (A : UU i) → UU i
is-prop A = (x y : A) → is-contr (Id x y)

UU-Prop :
  (l : Level) → UU (lsuc l)
UU-Prop l = Σ (UU l) is-prop

module _
  {l : Level}
  where

  type-Prop : UU-Prop l → UU l
  type-Prop P = pr1 P

  abstract
    is-prop-type-Prop : (P : UU-Prop l) → is-prop (type-Prop P)
    is-prop-type-Prop P = pr2 P

{- Example 12.1.2 -}

abstract
  is-prop-unit : is-prop unit
  is-prop-unit = is-prop-is-contr is-contr-unit

unit-Prop : UU-Prop lzero
pr1 unit-Prop = unit
pr2 unit-Prop = is-prop-unit

abstract
  is-prop-empty : is-prop empty
  is-prop-empty ()

empty-Prop : UU-Prop lzero
pr1 empty-Prop = empty
pr2 empty-Prop = is-prop-empty

abstract
  is-prop-leq-Fin :
    {k : ℕ} (x y : Fin k) → is-prop (leq-Fin x y)
  is-prop-leq-Fin {succ-ℕ k} (inl x) (inl y) = is-prop-leq-Fin x y
  is-prop-leq-Fin {succ-ℕ k} (inl x) (inr star) = is-prop-unit
  is-prop-leq-Fin {succ-ℕ k} (inr star) (inl y) = is-prop-empty
  is-prop-leq-Fin {succ-ℕ k} (inr star) (inr star) = is-prop-unit

{- Proposition 12.1.3 -}

module _
  {l : Level} (A : UU l)
  where
  
  all-elements-equal : UU l
  all-elements-equal = (x y : A) → Id x y
  
  is-proof-irrelevant : UU l
  is-proof-irrelevant = A → is-contr A
  
  is-subterminal : UU l
  is-subterminal = is-emb (terminal-map {A = A})

module _
  {l : Level} {A : UU l}
  where
  
  abstract
    is-prop-all-elements-equal : all-elements-equal A → is-prop A
    pr1 (is-prop-all-elements-equal H x y) = (inv (H x x)) ∙ (H x y)
    pr2 (is-prop-all-elements-equal H x .x) refl = left-inv (H x x)

  abstract
    eq-is-prop' : is-prop A → all-elements-equal A
    eq-is-prop' H x y = pr1 (H x y)

  abstract
    eq-is-prop : is-prop A → {x y : A} → Id x y
    eq-is-prop H {x} {y} = eq-is-prop' H x y

  abstract
    is-proof-irrelevant-all-elements-equal :
      all-elements-equal A → is-proof-irrelevant A
    pr1 (is-proof-irrelevant-all-elements-equal H a) = a
    pr2 (is-proof-irrelevant-all-elements-equal H a) = H a

  abstract
    is-proof-irrelevant-is-prop : is-prop A → is-proof-irrelevant A
    is-proof-irrelevant-is-prop =
      is-proof-irrelevant-all-elements-equal ∘ eq-is-prop'

  abstract
    is-prop-is-proof-irrelevant : is-proof-irrelevant A → is-prop A
    is-prop-is-proof-irrelevant H x y = is-prop-is-contr (H x) x y

  abstract
    eq-is-proof-irrelevant : is-proof-irrelevant A → all-elements-equal A
    eq-is-proof-irrelevant H = eq-is-prop' (is-prop-is-proof-irrelevant H)

  abstract
    is-emb-is-emb :
      {l2 : Level} {B : UU l2} {f : A → B} → (A → is-emb f) → is-emb f
    is-emb-is-emb H x y = H x x y

  abstract
    is-subterminal-is-proof-irrelevant :
      is-proof-irrelevant A → is-subterminal A
    is-subterminal-is-proof-irrelevant H =
      is-emb-is-emb
        ( λ x → is-emb-is-equiv (is-equiv-is-contr _ (H x) is-contr-unit))

  abstract
    is-subterminal-all-elements-equal : all-elements-equal A → is-subterminal A
    is-subterminal-all-elements-equal =
      is-subterminal-is-proof-irrelevant ∘
      is-proof-irrelevant-all-elements-equal

  abstract
    is-subterminal-is-prop : is-prop A → is-subterminal A
    is-subterminal-is-prop = is-subterminal-all-elements-equal ∘ eq-is-prop'

  abstract
    is-prop-is-subterminal : is-subterminal A → is-prop A
    is-prop-is-subterminal H x y =
      is-contr-is-equiv
        ( Id star star)
        ( ap terminal-map)
        ( H x y)
        ( is-prop-is-contr is-contr-unit star star)

  abstract
    eq-is-subterminal : is-subterminal A → all-elements-equal A
    eq-is-subterminal = eq-is-prop' ∘ is-prop-is-subterminal

  abstract
    is-proof-irrelevant-is-subterminal :
      is-subterminal A → is-proof-irrelevant A
    is-proof-irrelevant-is-subterminal H =
      is-proof-irrelevant-all-elements-equal (eq-is-subterminal H)

{- Proposition 12.1.4 -}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-is-prop :
      is-prop A → is-prop B → {f : A → B} → (B → A) → is-equiv f
    is-equiv-is-prop is-prop-A is-prop-B {f} g =
      is-equiv-has-inverse
        ( g)
        ( λ y → center (is-prop-B (f (g y)) y))
        ( λ x → center (is-prop-A (g (f x)) x))

  abstract
    equiv-prop : is-prop A → is-prop B → (A → B) → (B → A) → A ≃ B
    pr1 (equiv-prop is-prop-A is-prop-B f g) = f
    pr2 (equiv-prop is-prop-A is-prop-B f g) =
      is-equiv-is-prop is-prop-A is-prop-B g

--------------------------------------------------------------------------------

-- Section 12.2 Subtypes

{- Definition 12.2.1 -}

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-subtype : UU (l1 ⊔ l2)
  is-subtype = (x : A) → is-prop (B x)

  is-property : UU (l1 ⊔ l2)
  is-property = is-subtype

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-map : (A → B) → UU (l1 ⊔ l2)
  is-prop-map f = (b : B) → is-prop (fib f b)

module _
  {l1 l2 : Level} {A : UU l1}
  where

  total-subtype : (A → UU-Prop l2) → UU (l1 ⊔ l2)
  total-subtype P = Σ A (λ x → pr1 (P x))

{- Lemma 12.2.2 -}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-is-equiv : {f : A → B} → is-equiv f → is-prop B → is-prop A
    is-prop-is-equiv {f} E H x y =
      is-contr-is-equiv _ (ap f {x} {y}) (is-emb-is-equiv E x y) (H (f x) (f y))

  abstract
    is-prop-equiv : A ≃ B → is-prop B → is-prop A
    is-prop-equiv (pair f is-equiv-f) = is-prop-is-equiv is-equiv-f

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-is-equiv' : {f : A → B} → is-equiv f → is-prop A → is-prop B
    is-prop-is-equiv' E H =
      is-prop-is-equiv (is-equiv-map-inv-is-equiv E) H

  abstract
    is-prop-equiv' : A ≃ B → is-prop A → is-prop B
    is-prop-equiv' (pair f is-equiv-f) = is-prop-is-equiv' is-equiv-f

{- Theorem 12.2.3 -}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-emb-is-prop-map : is-prop-map f → is-emb f
    is-emb-is-prop-map is-prop-map-f x =
      fundamental-theorem-id x refl
        ( is-contr-equiv
          ( fib f (f x))
          ( equiv-tot (λ y → equiv-inv (f x) (f y)))
          ( is-proof-irrelevant-is-prop (is-prop-map-f (f x)) (pair x refl)))
        ( λ y → ap f)

  abstract
    is-prop-map-is-emb : is-emb f → is-prop-map f
    is-prop-map-is-emb is-emb-f y =
      is-prop-is-proof-irrelevant α
      where
      α : (t : fib f y) → is-contr (fib f y)
      α (pair x refl) =
        fundamental-theorem-id' x refl
          ( λ y → inv ∘ ap f)
          ( λ y →
            is-equiv-comp' inv (ap f)
              ( is-emb-f x y)
              ( is-equiv-inv (f x) (f y)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-map-emb : (f : B ↪ A) → is-prop-map (map-emb f)
    is-prop-map-emb f = is-prop-map-is-emb (is-emb-map-emb f)

  fib-emb-Prop : A ↪ B → B → UU-Prop (l1 ⊔ l2)
  pr1 (fib-emb-Prop f y) = fib (map-emb f) y
  pr2 (fib-emb-Prop f y) = is-prop-map-is-emb (is-emb-map-emb f) y

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-emb-pr1 : is-subtype B → is-emb (pr1 {B = B})
    is-emb-pr1 H =
      is-emb-is-prop-map (λ x → is-prop-equiv (equiv-fib-pr1 B x) (H x))

  emb-pr1 : is-subtype B → Σ A B ↪ A
  pr1 (emb-pr1 H) = pr1
  pr2 (emb-pr1 H) = is-emb-pr1 H

  equiv-ap-pr1 : is-subtype B → {s t : Σ A B} → Id s t ≃ Id (pr1 s) (pr1 t)
  pr1 (equiv-ap-pr1 is-subtype-B {s} {t}) = ap pr1
  pr2 (equiv-ap-pr1 is-subtype-B {s} {t}) = is-emb-pr1 is-subtype-B s t

  abstract
    is-subtype-is-emb-pr1 : is-emb (pr1 {B = B}) → is-subtype B
    is-subtype-is-emb-pr1 H x =
      is-prop-equiv' (equiv-fib-pr1 B x) (is-prop-map-is-emb H x)

{- Remark 12.2.5 -}

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

{- The following is a general construction that will help us show that
   the identity type of a subtype agrees with the identity type of the 
   original type. We already know that the first projection of a family of
   propositions is an embedding, but the following lemma still has its uses. -}

  abstract
    is-contr-total-Eq-substructure :
      {l3 : Level} {P : A → UU l3} →
      is-contr (Σ A B) → (is-subtype P) → (a : A) (b : B a) (p : P a) →
      is-contr (Σ (Σ A P) (λ t → B (pr1 t)))
    is-contr-total-Eq-substructure {l3} {P}
      is-contr-AB is-subtype-P a b p =
      is-contr-equiv
        ( Σ (Σ A B) (λ t → P (pr1 t)))
        ( equiv-right-swap-Σ)
        ( is-contr-equiv
          ( P a)
          ( left-unit-law-Σ-is-contr
            ( is-contr-AB)
            ( pair a b))
          ( is-proof-irrelevant-is-prop (is-subtype-P a) p))

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (H : is-subtype B)
  where

  Eq-total-subtype : (Σ A B) → (Σ A B) → UU l1
  Eq-total-subtype p p' = Id (pr1 p) (pr1 p') 

  refl-Eq-total-subtype : (p : Σ A B) → Eq-total-subtype p p
  refl-Eq-total-subtype (pair x y) = refl

  Eq-eq-total-subtype : (p p' : Σ A B) → Id p p' → Eq-total-subtype p p'
  Eq-eq-total-subtype p .p refl = refl-Eq-total-subtype p

  abstract
    is-contr-total-Eq-total-subtype :
      (p : Σ A B) → is-contr (Σ (Σ A B) (Eq-total-subtype p))
    is-contr-total-Eq-total-subtype (pair x y) =
      is-contr-total-Eq-substructure (is-contr-total-path x) H x refl y

  abstract
    is-equiv-Eq-eq-total-subtype :
      (p p' : Σ A B) → is-equiv (Eq-eq-total-subtype p p')
    is-equiv-Eq-eq-total-subtype p =
      fundamental-theorem-id p
        ( refl-Eq-total-subtype p)
        ( is-contr-total-Eq-total-subtype p)
        ( Eq-eq-total-subtype p)

  equiv-Eq-eq-total-subtype :
    (p p' : Σ A B) → (Id p p') ≃ (Eq-total-subtype p p')
  pr1 (equiv-Eq-eq-total-subtype p p') = Eq-eq-total-subtype p p'
  pr2 (equiv-Eq-eq-total-subtype p p') = is-equiv-Eq-eq-total-subtype p p'

  eq-subtype :
    {p p' : Σ A B} → Eq-total-subtype p p' → Id p p'
  eq-subtype {p} {p'} =
    map-inv-is-equiv (is-equiv-Eq-eq-total-subtype p p')

--------------------------------------------------------------------------------

-- Section 12.3 Sets

is-set :
  {i : Level} → UU i → UU i
is-set A = (x y : A) → is-prop (Id x y)

UU-Set :
  (i : Level) → UU (lsuc i)
UU-Set i = Σ (UU i) is-set

module _
  {l : Level} (X : UU-Set l)
  where

  type-Set : UU l
  type-Set = pr1 X

  abstract
    is-set-type-Set : is-set type-Set
    is-set-type-Set = pr2 X

  Id-Prop : (x y : type-Set) → UU-Prop l
  pr1 (Id-Prop x y) = Id x y
  pr2 (Id-Prop x y) = is-set-type-Set x y

axiom-K :
  {i : Level} → UU i → UU i
axiom-K A = (x : A) (p : Id x x) → Id refl p

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-set-axiom-K' : axiom-K A → (x y : A) → all-elements-equal (Id x y)
    is-set-axiom-K' K x .x refl q with K x q
    ... | refl = refl

  abstract
    is-set-axiom-K : axiom-K A → is-set A
    is-set-axiom-K H x y = is-prop-all-elements-equal (is-set-axiom-K' H x y) 

  abstract
    axiom-K-is-set : is-set A → axiom-K A
    axiom-K-is-set H x p =
      ( inv (contraction (is-proof-irrelevant-is-prop (H x x) refl) refl)) ∙ 
      ( contraction (is-proof-irrelevant-is-prop (H x x) refl) p)

module _
  {l1 l2 : Level} {A : UU l1} (R : A → A → UU l2)
  (p : (x y : A) → is-prop (R x y)) (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → Id x y)
  where

  abstract
    is-equiv-prop-in-id : (x y : A) → is-equiv (i x y)
    is-equiv-prop-in-id x =
      fundamental-theorem-id-retr x (i x)
        ( λ y →
          pair
            ( ind-Id x (λ z p → R x z) (ρ x) y)
            ( λ r → eq-is-prop (p x y)))

  abstract
    is-set-prop-in-id : is-set A
    is-set-prop-in-id x y = is-prop-is-equiv' (is-equiv-prop-in-id x y) (p x y)

abstract
  is-prop-Eq-ℕ :
    (n m : ℕ) → is-prop (Eq-ℕ n m)
  is-prop-Eq-ℕ zero-ℕ zero-ℕ = is-prop-unit
  is-prop-Eq-ℕ zero-ℕ (succ-ℕ m) = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) zero-ℕ = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) (succ-ℕ m) = is-prop-Eq-ℕ n m

abstract
  is-set-ℕ : is-set ℕ
  is-set-ℕ =
    is-set-prop-in-id
      Eq-ℕ
      is-prop-Eq-ℕ
      refl-Eq-ℕ
      eq-Eq-ℕ

ℕ-Set : UU-Set lzero
pr1 ℕ-Set = ℕ
pr2 ℕ-Set = is-set-ℕ

module _
  {l : Level} {A : UU l}
  where

  {- Next, we show that types with decidable equality are sets. To see this, we 
     will construct a fiberwise equivalence with the binary relation R that is
     defined by R x y := unit if (x = y), and empty otherwise. In order to
     define this relation, we first define a type family over
     ((x = y) + ¬(x = y)) that returns unit on the left and empty on the right.   -}
   
  Eq-has-decidable-equality' :
    (x y : A) → is-decidable (Id x y) → UU lzero
  Eq-has-decidable-equality' x y (inl p) = unit
  Eq-has-decidable-equality' x y (inr f) = empty

  Eq-has-decidable-equality :
    (d : has-decidable-equality A) → A → A → UU lzero
  Eq-has-decidable-equality d x y = Eq-has-decidable-equality' x y (d x y)

  abstract
    is-prop-Eq-has-decidable-equality' :
      (x y : A) (t : is-decidable (Id x y)) →
      is-prop (Eq-has-decidable-equality' x y t)
    is-prop-Eq-has-decidable-equality' x y (inl p) = is-prop-unit
    is-prop-Eq-has-decidable-equality' x y (inr f) = is-prop-empty

  abstract
    is-prop-Eq-has-decidable-equality :
      (d : has-decidable-equality A)
      {x y : A} → is-prop (Eq-has-decidable-equality d x y)
    is-prop-Eq-has-decidable-equality d {x} {y} =
      is-prop-Eq-has-decidable-equality' x y (d x y)

  abstract
    refl-Eq-has-decidable-equality :
      (d : has-decidable-equality A) (x : A) →
      Eq-has-decidable-equality d x x 
    refl-Eq-has-decidable-equality d x with d x x
    ... | inl α = star
    ... | inr f = f refl

  abstract
    Eq-has-decidable-equality-eq :
      (d : has-decidable-equality A) {x y : A} →
      Id x y → Eq-has-decidable-equality d x y
    Eq-has-decidable-equality-eq d {x} {.x} refl =
      refl-Eq-has-decidable-equality d x

  abstract
    eq-Eq-has-decidable-equality' :
      (x y : A) (t : is-decidable (Id x y)) →
      Eq-has-decidable-equality' x y t → Id x y
    eq-Eq-has-decidable-equality' x y (inl p) t = p
    eq-Eq-has-decidable-equality' x y (inr f) t = ex-falso t

  abstract
    eq-Eq-has-decidable-equality :
      (d : has-decidable-equality A) {x y : A} →
      Eq-has-decidable-equality d x y → Id x y
    eq-Eq-has-decidable-equality d {x} {y} =
      eq-Eq-has-decidable-equality' x y (d x y)

  abstract
    is-set-has-decidable-equality : has-decidable-equality A → is-set A
    is-set-has-decidable-equality d =
      is-set-prop-in-id
        ( λ x y → Eq-has-decidable-equality d x y)
        ( λ x y → is-prop-Eq-has-decidable-equality d)
        ( λ x → refl-Eq-has-decidable-equality d x)
        ( λ x y → eq-Eq-has-decidable-equality d)

--------------------------------------------------------------------------------

-- Section 12.3 General truncation levels

data 𝕋 : UU lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋

neg-one-𝕋 : 𝕋
neg-one-𝕋 = succ-𝕋 (neg-two-𝕋)

zero-𝕋 : 𝕋
zero-𝕋 = succ-𝕋 (neg-one-𝕋)

one-𝕋 : 𝕋
one-𝕋 = succ-𝕋 (zero-𝕋)

truncation-level-ℕ : ℕ → 𝕋
truncation-level-ℕ zero-ℕ = zero-𝕋
truncation-level-ℕ (succ-ℕ k) = succ-𝕋 (truncation-level-ℕ k)

truncation-level-minus-one-ℕ : ℕ → 𝕋
truncation-level-minus-one-ℕ zero-ℕ = neg-one-𝕋
truncation-level-minus-one-ℕ (succ-ℕ k) =
  succ-𝕋 (truncation-level-minus-one-ℕ k)

truncation-level-minus-two-ℕ : ℕ → 𝕋
truncation-level-minus-two-ℕ zero-ℕ = neg-two-𝕋
truncation-level-minus-two-ℕ (succ-ℕ k) =
  succ-𝕋 (truncation-level-minus-two-ℕ k)

-- Probably it is better to define this where we first need it.
add-𝕋 : 𝕋 → 𝕋 → 𝕋
add-𝕋 neg-two-𝕋 neg-two-𝕋 = neg-two-𝕋
add-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = neg-two-𝕋
add-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 y)) = y
add-𝕋 (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = neg-two-𝕋
add-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 y) = y
add-𝕋 (succ-𝕋 (succ-𝕋 neg-two-𝕋)) y = y
add-𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 x))) y = succ-𝕋 (add-𝕋 (succ-𝕋 (succ-𝕋 x)) y)

-- Definition 12.4.1

-- Truncated types

is-trunc : {i : Level} (k : 𝕋) → UU i → UU i
is-trunc neg-two-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (Id x y)

-- Truncated maps

module _
  {l1 l2 : Level} (k : 𝕋)
  where

  is-trunc-map : {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
  is-trunc-map f = (y : _) → is-trunc k (fib f y)
  
  trunc-map : (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
  trunc-map A B = Σ (A → B) is-trunc-map

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  map-trunc-map : trunc-map k A B → A → B
  map-trunc-map = pr1

  abstract
    is-trunc-map-map-trunc-map :
      (f : trunc-map k A B) → is-trunc-map k (map-trunc-map f)
    is-trunc-map-map-trunc-map = pr2

module _
  {l1 l2 : Level}
  where

  is-0-map : {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
  is-0-map {A} {B} f = (y : B) → is-set (fib f y)

  0-map : (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
  0-map A B = Σ (A → B) is-0-map

  map-0-map : {A : UU l1} {B : UU l2} → 0-map A B → A → B
  map-0-map = pr1

  is-0-map-map-0-map :
    {A : UU l1} {B : UU l2} (f : 0-map A B) → is-0-map (map-0-map f)
  is-0-map-map-0-map = pr2

-- We introduce some notation for the special case of 1-types --

is-1-type : {l : Level} → UU l → UU l
is-1-type = is-trunc one-𝕋

UU-1-Type : (l : Level) → UU (lsuc l)
UU-1-Type l = Σ (UU l) is-1-type

type-1-Type : {l : Level} → UU-1-Type l → UU l
type-1-Type = pr1

abstract
  is-1-type-type-1-Type :
    {l : Level} (A : UU-1-Type l) → is-1-type (type-1-Type A)
  is-1-type-type-1-Type = pr2

Id-Set : {l : Level} (X : UU-1-Type l) (x y : type-1-Type X) → UU-Set l
pr1 (Id-Set X x y) = Id x y
pr2 (Id-Set X x y) = is-1-type-type-1-Type X x y

-- We introduce some notation for the special case of 2-types --

is-2-type : {l : Level} → UU l → UU l
is-2-type = is-trunc (succ-𝕋 one-𝕋)

UU-2-Type : (l : Level) → UU (lsuc l)
UU-2-Type l = Σ (UU l) is-2-type

type-2-Type :
  {l : Level} → UU-2-Type l → UU l
type-2-Type = pr1

abstract
  is-2-type-type-2-Type :
    {l : Level} (A : UU-2-Type l) → is-2-type (type-2-Type A)
  is-2-type-type-2-Type = pr2

-- We introduce some notation for the universe of k-truncated types --

UU-Truncated-Type : 𝕋 → (l : Level) → UU (lsuc l)
UU-Truncated-Type k l = Σ (UU l) (is-trunc k)

module _
  {k : 𝕋} {l : Level}
  where
  
  type-Truncated-Type : UU-Truncated-Type k l → UU l
  type-Truncated-Type = pr1

  abstract
    is-trunc-type-Truncated-Type :
      (A : UU-Truncated-Type k l) → is-trunc k (type-Truncated-Type A)
    is-trunc-type-Truncated-Type = pr2

{- Remark 12.4.2

We can't formalise this remark in Agda, because universes are handled 
differently. -}

-- Proposition 12.4.3

-- We show that if a type is k-truncated, then it is (k+1)-truncated. --

abstract
  is-trunc-succ-is-trunc :
    (k : 𝕋) {i : Level} {A : UU i} →
    is-trunc k A → is-trunc (succ-𝕋 k) A
  is-trunc-succ-is-trunc neg-two-𝕋 H =
    is-prop-is-contr H
  is-trunc-succ-is-trunc (succ-𝕋 k) H x y =
    is-trunc-succ-is-trunc k (H x y)

abstract
  is-trunc-map-succ-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    (f : A → B) → is-trunc-map k f → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-succ-is-trunc-map k f is-trunc-f b =
    is-trunc-succ-is-trunc k (is-trunc-f b)

truncated-type-succ-Truncated-Type :
  (k : 𝕋) {l : Level} → UU-Truncated-Type k l → UU-Truncated-Type (succ-𝕋 k) l
pr1 (truncated-type-succ-Truncated-Type k A) = type-Truncated-Type A
pr2 (truncated-type-succ-Truncated-Type k A) =
  is-trunc-succ-is-trunc k (is-trunc-type-Truncated-Type A)

abstract
  is-set-is-prop :
    {l : Level} {P : UU l} → is-prop P → is-set P
  is-set-is-prop = is-trunc-succ-is-trunc neg-one-𝕋

set-Prop :
  {l : Level} → UU-Prop l → UU-Set l
set-Prop P = truncated-type-succ-Truncated-Type neg-one-𝕋 P

1-type-Set :
  {l : Level} → UU-Set l → UU-1-Type l
1-type-Set A = truncated-type-succ-Truncated-Type zero-𝕋 A

-- We conclude that a contractible type is k-truncated for any k

abstract
  is-trunc-is-contr :
    {l : Level} (k : 𝕋) {A : UU l} → is-contr A → is-trunc k A
  is-trunc-is-contr neg-two-𝕋 is-contr-A = is-contr-A
  is-trunc-is-contr (succ-𝕋 k) is-contr-A =
    is-trunc-succ-is-trunc k (is-trunc-is-contr k is-contr-A)

abstract
  is-set-is-contr :
    {l : Level} {A : UU l} → is-contr A → is-set A
  is-set-is-contr = is-trunc-is-contr zero-𝕋

-- We also conclude that a proposition is (k+1)-truncated for any k

abstract
  is-trunc-is-prop :
    { l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
  is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)

abstract
  is-trunc-empty : (k : 𝕋) → is-trunc (succ-𝕋 k) empty
  is-trunc-empty k = ind-empty

abstract
  is-trunc-is-empty :
    {l : Level} (k : 𝕋) {A : UU l} → is-empty A → is-trunc (succ-𝕋 k) A
  is-trunc-is-empty k f = is-trunc-is-prop k (λ x → ex-falso (f x))

-- Corollary 12.4.4

abstract
  is-trunc-Id : {l : Level} (k : 𝕋) {A : UU l} →
    is-trunc k A → (x y : A) → is-trunc k (Id x y)
  is-trunc-Id neg-two-𝕋 is-trunc-A = is-prop-is-contr is-trunc-A
  is-trunc-Id (succ-𝕋 k) is-trunc-A x y =
    is-trunc-succ-is-trunc k {A = Id x y} (is-trunc-A x y)

-- Proposition 12.4.5

-- We show that k-truncated types are closed under equivalences --

abstract
  is-trunc-is-equiv :
    {i j : Level} (k : 𝕋) {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
    is-trunc k B → is-trunc k A
  is-trunc-is-equiv neg-two-𝕋 B f is-equiv-f H =
    is-contr-is-equiv B f is-equiv-f H
  is-trunc-is-equiv (succ-𝕋 k) B f is-equiv-f H x y =
    is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y})
      ( is-emb-is-equiv is-equiv-f x y) (H (f x) (f y))

abstract
  is-set-is-equiv :
    {i j : Level} {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
    is-set B → is-set A
  is-set-is-equiv = is-trunc-is-equiv zero-𝕋

abstract
  is-trunc-equiv :
    {i j : Level} (k : 𝕋) {A : UU i} (B : UU  j) (e : A ≃ B) →
    is-trunc k B → is-trunc k A
  is-trunc-equiv k B (pair f is-equiv-f) =
    is-trunc-is-equiv k B f is-equiv-f

abstract
  is-set-equiv :
    {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) →
    is-set B → is-set A
  is-set-equiv = is-trunc-equiv zero-𝕋

abstract
  is-trunc-is-equiv' :
    {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (f : A → B) →
    is-equiv f → is-trunc k A → is-trunc k B
  is-trunc-is-equiv' k A  f is-equiv-f is-trunc-A =
    is-trunc-is-equiv k A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-trunc-A)

abstract
  is-set-is-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (f : A → B) → is-equiv f →
    is-set A → is-set B
  is-set-is-equiv' = is-trunc-is-equiv' zero-𝕋

abstract
  is-trunc-equiv' :
    {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (e : A ≃ B) →
    is-trunc k A → is-trunc k B
  is-trunc-equiv' k A (pair f is-equiv-f) =
    is-trunc-is-equiv' k A f is-equiv-f

abstract
  is-set-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) →
    is-set A → is-set B
  is-set-equiv' = is-trunc-equiv' zero-𝕋

-- Corollary 12.4.6

-- We show that if A embeds into a (k+1)-type B, then A is a (k+1)-type. --

abstract
  is-trunc-is-emb :
    {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} (f : A → B) →
    is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-is-emb k f Ef H x y =
    is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y}) (Ef x y) (H (f x) (f y))

abstract
  is-trunc-emb :
    {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} (f : A ↪ B) →
    is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-emb k f = is-trunc-is-emb k (map-emb f) (is-emb-map-emb f)

-- Proposition 12.4.7

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  abstract
    is-trunc-map-is-trunc-map-ap :
      ((x y : A) → is-trunc-map k (ap f {x} {y})) → is-trunc-map (succ-𝕋 k) f
    is-trunc-map-is-trunc-map-ap is-trunc-map-ap-f b (pair x p) (pair x' p') =
      is-trunc-is-equiv k
        ( fib (ap f) (p ∙ (inv p')))
        ( fib-ap-eq-fib f (pair x p) (pair x' p'))
        ( is-equiv-fib-ap-eq-fib f (pair x p) (pair x' p'))
        ( is-trunc-map-ap-f x x' (p ∙ (inv p')))      

  abstract
    is-trunc-map-ap-is-trunc-map :
      is-trunc-map (succ-𝕋 k) f → (x y : A) → is-trunc-map k (ap f {x} {y})
    is-trunc-map-ap-is-trunc-map is-trunc-map-f x y p =
      is-trunc-is-equiv' k
        ( Id (pair x p) (pair y refl))
        ( eq-fib-fib-ap f x y p)
        ( is-equiv-eq-fib-fib-ap f x y p)
        ( is-trunc-map-f (f y) (pair x p) (pair y refl))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-0-map-is-faithful : is-faithful f → is-0-map f
  is-0-map-is-faithful H =
    is-trunc-map-is-trunc-map-ap neg-one-𝕋 f
      ( λ x y → is-prop-map-is-emb (H x y))

  is-faithful-is-0-map : is-0-map f → is-faithful f
  is-faithful-is-0-map H x y =
    is-emb-is-prop-map (is-trunc-map-ap-is-trunc-map neg-one-𝕋 f H x y)

--

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1}
  where

  abstract
    is-trunc-map-pr1 :
      {B : A → UU l2} → ((x : A) → is-trunc k (B x)) →
      is-trunc-map k (pr1 {l1} {l2} {A} {B})
    is-trunc-map-pr1 {B} H x =
      is-trunc-equiv k (B x) (equiv-fib-pr1 B x) (H x)

  pr1-trunc-map :
    (B : A → UU-Truncated-Type k l2) → trunc-map k (Σ A (λ x → pr1 (B x))) A
  pr1 (pr1-trunc-map B) = pr1
  pr2 (pr1-trunc-map B) = is-trunc-map-pr1 (λ x → pr2 (B x))

  abstract
    is-trunc-is-trunc-map-pr1 :
      (B : A → UU l2) → is-trunc-map k (pr1 {l1} {l2} {A} {B}) →
      ((x : A) → is-trunc k (B x))
    is-trunc-is-trunc-map-pr1 B is-trunc-map-pr1 x =
      is-trunc-equiv k (fib pr1 x) (inv-equiv-fib-pr1 B x) (is-trunc-map-pr1 x)
    
  abstract
    is-trunc-is-subtype :
      {P : A → UU l2} → is-subtype P → is-trunc (succ-𝕋 k) A →
      is-trunc (succ-𝕋 k) (Σ A P)
    is-trunc-is-subtype H is-trunc-A =
      is-trunc-is-emb k pr1 (is-emb-pr1 H) is-trunc-A

module _
  {l1 l2 : Level} {A : UU l1}
  where
  
  abstract
    is-0-map-pr1 :
      {B : A → UU l2} → ((x : A) → is-set (B x)) → is-0-map (pr1 {B = B})
    is-0-map-pr1 {B} H x =
      is-set-equiv (B x) (equiv-fib-pr1 B x) (H x)
                                                  
  pr1-0-map :
    (B : A → UU-Set l2) → 0-map (Σ A (λ x → type-Set (B x))) A
  pr1 (pr1-0-map B) = pr1
  pr2 (pr1-0-map B) = is-0-map-pr1 (λ x → is-set-type-Set (B x))

  abstract
    is-faithful-pr1 :
      {B : A → UU l2} → ((x : A) → is-set (B x)) → is-faithful (pr1 {B = B})
    is-faithful-pr1 H = is-faithful-is-0-map (is-0-map-pr1 H)

  pr1-faithful-map :
    (B : A → UU-Set l2) → faithful-map (Σ A (λ x → type-Set (B x))) A
  pr1 (pr1-faithful-map B) = pr1
  pr2 (pr1-faithful-map B) = is-faithful-pr1 (λ x → is-set-type-Set (B x))

module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2}
  where
  
  abstract
    is-prop-is-subtype : is-subtype P → is-prop A → is-prop (Σ A P)
    is-prop-is-subtype = is-trunc-is-subtype neg-two-𝕋

  abstract
    is-set-is-subtype : is-subtype P → is-set A → is-set (Σ A P)
    is-set-is-subtype = is-trunc-is-subtype neg-one-𝕋

  abstract
    is-1-type-is-subtype : is-subtype P → is-1-type A → is-1-type (Σ A P)
    is-1-type-is-subtype = is-trunc-is-subtype zero-𝕋

subprop-Prop :
  {l1 l2 : Level} (A : UU-Prop l1) (P : (x : type-Prop A) → UU-Prop l2) →
  UU-Prop (l1 ⊔ l2)
pr1 (subprop-Prop A P) = Σ (type-Prop A) (λ x → type-Prop (P x))
pr2 (subprop-Prop A P) =
  is-prop-is-subtype (λ x → is-prop-type-Prop (P x)) (is-prop-type-Prop A)

subset-Set :
  {l1 l2 : Level} (A : UU-Set l1) (P : (x : type-Set A) → UU-Prop l2) →
  UU-Set (l1 ⊔ l2)
pr1 (subset-Set A P) = Σ (type-Set A) (λ x → type-Prop (P x))
pr2 (subset-Set A P) =
  is-set-is-subtype (λ x → is-prop-type-Prop (P x)) (is-set-type-Set A)

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 12.1

abstract
  is-prop-Eq-bool : (x y : bool) → is-prop (Eq-bool x y)
  is-prop-Eq-bool true true = is-prop-unit
  is-prop-Eq-bool true false = is-prop-empty
  is-prop-Eq-bool false true = is-prop-empty
  is-prop-Eq-bool false false = is-prop-unit

abstract
  is-set-bool : is-set bool
  is-set-bool =
    is-set-prop-in-id
      ( Eq-bool)
      ( is-prop-Eq-bool)
      ( refl-Eq-bool)
      ( λ x y → eq-Eq-bool)

bool-Set : UU-Set lzero
pr1 bool-Set = bool
pr2 bool-Set = is-set-bool

-- Exercise 12.2

-- Exercise 12.2 (a)

abstract
  is-emb-is-injective' : {l1 l2 : Level} {A : UU l1} (is-set-A : is-set A)
    {B : UU l2} (is-set-B : is-set B) (f : A → B) →
    is-injective f → is-emb f
  is-emb-is-injective' is-set-A is-set-B f is-injective-f x y =
    is-equiv-is-prop
      ( is-set-A x y)
      ( is-set-B (f x) (f y))
      ( is-injective-f)

  is-set-is-injective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-set B → is-injective f → is-set A
  is-set-is-injective {f = f} H I =
    is-set-prop-in-id
      ( λ x y → Id (f x) (f y))
      ( λ x y → H (f x) (f y))
      ( λ x → refl)
      ( λ x y → I)

  is-emb-is-injective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-set B → is-injective f → is-emb f
  is-emb-is-injective {f = f} H I =
    is-emb-is-injective' (is-set-is-injective H I) H f I

  is-prop-map-is-injective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-set B → is-injective f → is-prop-map f
  is-prop-map-is-injective {f = f} H I =
    is-prop-map-is-emb (is-emb-is-injective H I)

-- Exercise 12.2 (b)

is-emb-add-ℕ : (x : ℕ) → is-emb (add-ℕ x)
is-emb-add-ℕ x = is-emb-is-injective is-set-ℕ (is-injective-add-ℕ x)

is-emb-add-ℕ' : (x : ℕ) → is-emb (add-ℕ' x)
is-emb-add-ℕ' x = is-emb-is-injective is-set-ℕ (is-injective-add-ℕ' x)

-- Exercise 12.2 (c)

is-emb-mul-ℕ : (x : ℕ) → is-nonzero-ℕ x → is-emb (mul-ℕ x)
is-emb-mul-ℕ x H = is-emb-is-injective is-set-ℕ (is-injective-mul-ℕ x H)

is-emb-mul-ℕ' : (x : ℕ) → is-nonzero-ℕ x → is-emb (mul-ℕ' x)
is-emb-mul-ℕ' x H = is-emb-is-injective is-set-ℕ (is-injective-mul-ℕ' x H)

-- We conclude that some maps, that were known to be injective, are embeddings
                                                                    
is-emb-nat-Fin : {k : ℕ} → is-emb (nat-Fin {k})
is-emb-nat-Fin {k} = is-emb-is-injective is-set-ℕ is-injective-nat-Fin

emb-nat-Fin : (k : ℕ) → Fin k ↪ ℕ
pr1 (emb-nat-Fin k) = nat-Fin
pr2 (emb-nat-Fin k) = is-emb-nat-Fin

-- Exercise 12.3

-- Exercise 12.3 (a)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-not-contractible-coprod-is-contr :
      is-contr A → is-contr B → ¬ (is-contr (coprod A B))
    is-not-contractible-coprod-is-contr HA HB HAB =
      is-empty-eq-coprod-inl-inr (center HA) (center HB) (eq-is-contr HAB)

-- Exercise 12.3 (b)

module _
  {l1 l2 : Level} {P : UU l1} {Q : UU l2}
  where

  abstract
    all-elements-equal-coprod :
      (P → ¬ Q) → all-elements-equal P → all-elements-equal Q →
      all-elements-equal (coprod P Q)
    all-elements-equal-coprod f is-prop-P is-prop-Q (inl p) (inl p') =
      ap inl (is-prop-P p p')
    all-elements-equal-coprod f is-prop-P is-prop-Q (inl p) (inr q') =
      ex-falso (f p q')
    all-elements-equal-coprod f is-prop-P is-prop-Q (inr q) (inl p') =
      ex-falso (f p' q)
    all-elements-equal-coprod f is-prop-P is-prop-Q (inr q) (inr q') =
      ap inr (is-prop-Q q q')
  
  abstract
    is-prop-coprod : (P → ¬ Q) → is-prop P → is-prop Q → is-prop (coprod P Q)
    is-prop-coprod f is-prop-P is-prop-Q =
      is-prop-all-elements-equal
        ( all-elements-equal-coprod f
          ( eq-is-prop' is-prop-P)
          ( eq-is-prop' is-prop-Q))

-- Exercise 12.3 (c)

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  abstract
    is-trunc-coprod :
      is-trunc (succ-𝕋 (succ-𝕋 k)) A → is-trunc (succ-𝕋 (succ-𝕋 k)) B →
      is-trunc (succ-𝕋 (succ-𝕋 k)) (coprod A B)
    is-trunc-coprod is-trunc-A is-trunc-B (inl x) (inl y) =
      is-trunc-equiv (succ-𝕋 k)
        ( Id x y)
        ( compute-eq-coprod-inl-inl x y)
        ( is-trunc-A x y)
    is-trunc-coprod is-trunc-A is-trunc-B (inl x) (inr y) =
      is-trunc-is-empty k (is-empty-eq-coprod-inl-inr x y)
    is-trunc-coprod is-trunc-A is-trunc-B (inr x) (inl y) =
      is-trunc-is-empty k (is-empty-eq-coprod-inr-inl x y)
    is-trunc-coprod is-trunc-A is-trunc-B (inr x) (inr y) =
      is-trunc-equiv (succ-𝕋 k)
        ( Id x y)
        ( compute-eq-coprod-inr-inr x y)
        ( is-trunc-B x y)

abstract
  is-set-coprod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (coprod A B)
  is-set-coprod = is-trunc-coprod neg-two-𝕋

coprod-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU-Set (l1 ⊔ l2)
pr1 (coprod-Set (pair A is-set-A) (pair B is-set-B)) = coprod A B
pr2 (coprod-Set (pair A is-set-A) (pair B is-set-B)) =
  is-set-coprod is-set-A is-set-B

abstract
  is-set-unit : is-set unit
  is-set-unit = is-trunc-succ-is-trunc neg-one-𝕋 is-prop-unit

unit-Set : UU-Set lzero
pr1 unit-Set = unit
pr2 unit-Set = is-set-unit

abstract
  is-set-ℤ : is-set ℤ
  is-set-ℤ = is-set-coprod is-set-ℕ (is-set-coprod is-set-unit is-set-ℕ)

ℤ-Set : UU-Set lzero
pr1 ℤ-Set = ℤ
pr2 ℤ-Set = is-set-ℤ

is-set-empty : is-set empty
is-set-empty ()

empty-Set : UU-Set lzero
pr1 empty-Set = empty
pr2 empty-Set = is-set-empty

abstract
  is-set-Fin : (n : ℕ) → is-set (Fin n)
  is-set-Fin zero-ℕ = is-set-empty
  is-set-Fin (succ-ℕ n) =
    is-set-coprod (is-set-Fin n) is-set-unit

Fin-Set : (n : ℕ) → UU-Set lzero
pr1 (Fin-Set n) = Fin n
pr2 (Fin-Set n) = is-set-Fin n

abstract
  is-set-ℤ-Mod : (k : ℕ) → is-set (ℤ-Mod k)
  is-set-ℤ-Mod zero-ℕ = is-set-ℤ
  is-set-ℤ-Mod (succ-ℕ k) = is-set-Fin (succ-ℕ k)

ℤ-Mod-Set : (k : ℕ) → UU-Set lzero
pr1 (ℤ-Mod-Set k) = ℤ-Mod k
pr2 (ℤ-Mod-Set k) = is-set-ℤ-Mod k    

-- Exercise 12.4

module _
  {l : Level} (A : UU l)
  where

  diagonal : A → A × A
  pr1 (diagonal x) = x
  pr2 (diagonal x) = x

  -- Exercise 12.4 (a)
  
  abstract
    is-prop-is-equiv-diagonal : is-equiv diagonal → is-prop A
    is-prop-is-equiv-diagonal is-equiv-d =
      is-prop-all-elements-equal ( λ x y →
        let α = issec-map-inv-is-equiv is-equiv-d (pair x y) in
        ( inv (ap pr1 α)) ∙ (ap pr2 α))
  
  eq-fib-diagonal : (t : A × A) → fib diagonal t → Id (pr1 t) (pr2 t)
  eq-fib-diagonal (pair x y) (pair z α) = (inv (ap pr1 α)) ∙ (ap pr2 α)
  
  fib-diagonal-eq : (t : A × A) → Id (pr1 t) (pr2 t) → fib diagonal t
  pr1 (fib-diagonal-eq (pair x y) β) = x
  pr2 (fib-diagonal-eq (pair x y) β) = eq-pair refl β
  
  issec-fib-diagonal-eq :
    (t : A × A) → ((eq-fib-diagonal t) ∘ (fib-diagonal-eq t)) ~ id
  issec-fib-diagonal-eq (pair x .x) refl = refl
  
  isretr-fib-diagonal-eq :
    (t : A × A) → ((fib-diagonal-eq t) ∘ (eq-fib-diagonal t)) ~ id
  isretr-fib-diagonal-eq .(pair z z) (pair z refl) = refl
  
  abstract
    is-equiv-eq-fib-diagonal : (t : A × A) → is-equiv (eq-fib-diagonal t)
    is-equiv-eq-fib-diagonal t =
      is-equiv-has-inverse
        ( fib-diagonal-eq t)
        ( issec-fib-diagonal-eq t)
        ( isretr-fib-diagonal-eq t)

-- Exercise 12.4 (c)

module _
  {l : Level} {A : UU l}
  where
  
  abstract
    is-trunc-is-trunc-map-diagonal :
      (k : 𝕋) → is-trunc-map k (diagonal A) → is-trunc (succ-𝕋 k) A
    is-trunc-is-trunc-map-diagonal k is-trunc-d x y =
      is-trunc-is-equiv' k
        ( fib (diagonal A) (pair x y))
        ( eq-fib-diagonal A (pair x y))
        ( is-equiv-eq-fib-diagonal A (pair x y))
        ( is-trunc-d (pair x y))

  abstract
    is-prop-is-contr-map-diagonal : is-contr-map (diagonal A) → is-prop A
    is-prop-is-contr-map-diagonal = is-trunc-is-trunc-map-diagonal neg-two-𝕋

  abstract
    is-set-is-prop-map-diagonal : is-prop-map (diagonal A) → is-set A
    is-set-is-prop-map-diagonal = is-trunc-is-trunc-map-diagonal neg-one-𝕋

  abstract
    is-set-is-emb-diagonal : is-emb (diagonal A) → is-set A
    is-set-is-emb-diagonal H =
      is-set-is-prop-map-diagonal (is-prop-map-is-emb H)

  abstract
    is-1-type-is-0-map-diagonal : is-0-map (diagonal A) → is-1-type A
    is-1-type-is-0-map-diagonal = is-trunc-is-trunc-map-diagonal zero-𝕋

  abstract
    is-1-type-is-faithful-diagonal : is-faithful (diagonal A) → is-1-type A
    is-1-type-is-faithful-diagonal H =
      is-1-type-is-0-map-diagonal (is-0-map-is-faithful H)
  
  abstract
    is-trunc-map-diagonal-is-trunc : 
      (k : 𝕋) → is-trunc (succ-𝕋 k) A → is-trunc-map k (diagonal A)
    is-trunc-map-diagonal-is-trunc k is-trunc-A t =
      is-trunc-is-equiv k
        ( Id (pr1 t) (pr2 t))
        ( eq-fib-diagonal A t)
        ( is-equiv-eq-fib-diagonal A t)
          ( is-trunc-A (pr1 t) (pr2 t))

  abstract
    is-contr-map-diagonal-is-prop : is-prop A → is-contr-map (diagonal A)
    is-contr-map-diagonal-is-prop = is-trunc-map-diagonal-is-trunc neg-two-𝕋

  abstract
    is-prop-map-diagonal-is-set : is-set A → is-prop-map (diagonal A)
    is-prop-map-diagonal-is-set = is-trunc-map-diagonal-is-trunc neg-one-𝕋

  abstract
    is-emb-diagonal-is-set : is-set A → is-emb (diagonal A)
    is-emb-diagonal-is-set H =
      is-emb-is-prop-map (is-prop-map-diagonal-is-set H)

  abstract
    is-0-map-diagonal-is-1-type : is-1-type A → is-0-map (diagonal A)
    is-0-map-diagonal-is-1-type = is-trunc-map-diagonal-is-trunc zero-𝕋

  abstract
    is-faithful-diagonal-is-1-type : is-1-type A → is-faithful (diagonal A)
    is-faithful-diagonal-is-1-type H =
      is-faithful-is-0-map (is-0-map-diagonal-is-1-type H)

diagonal-emb :
  {l : Level} (A : UU-Set l) → (type-Set A) ↪ ((type-Set A) × (type-Set A))
pr1 (diagonal-emb A) = diagonal (type-Set A)
pr2 (diagonal-emb A) = is-emb-diagonal-is-set (is-set-type-Set A)

diagonal-faithful-map :
  {l : Level} (A : UU-1-Type l) →
  faithful-map (type-1-Type A) (type-1-Type A × type-1-Type A)
pr1 (diagonal-faithful-map A) = diagonal (type-1-Type A)
pr2 (diagonal-faithful-map A) =
  is-faithful-diagonal-is-1-type (is-1-type-type-1-Type A)

-- Exercise 12.5

-- Exercise 12.5 (a)

abstract
  is-trunc-Σ : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    is-trunc k A → ((x : A) → is-trunc k (B x)) → is-trunc k (Σ A B)
  is-trunc-Σ neg-two-𝕋 is-trunc-A is-trunc-B =
    is-contr-Σ' is-trunc-A is-trunc-B
  is-trunc-Σ (succ-𝕋 k) {B = B} is-trunc-A is-trunc-B s t =
    is-trunc-is-equiv k
      ( Σ (Id (pr1 s) (pr1 t)) (λ p → Id (tr B p (pr2 s)) (pr2 t)))
      ( pair-eq-Σ)
      ( is-equiv-pair-eq-Σ s t)
      ( is-trunc-Σ k
        ( is-trunc-A (pr1 s) (pr1 t))
        ( λ p → is-trunc-B (pr1 t) (tr B p (pr2 s)) (pr2 t)))

-- Exercise 12.5 (b)

-- Bureaucracy

abstract
  is-prop-Σ : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-prop A → is-subtype B → is-prop (Σ A B)
  is-prop-Σ = is-trunc-Σ neg-one-𝕋

Σ-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : type-Prop P → UU-Prop l2) →
  UU-Prop (l1 ⊔ l2)
pr1 (Σ-Prop P Q) = Σ (type-Prop P) (λ p → type-Prop (Q p))
pr2 (Σ-Prop P Q) =
  is-prop-Σ
    ( is-prop-type-Prop P)
    ( λ p → is-prop-type-Prop (Q p))

abstract
  is-set-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → ((x : A) → is-set (B x)) → is-set (Σ A B)
  is-set-Σ = is-trunc-Σ zero-𝕋

Σ-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : pr1 A → UU-Set l2) → UU-Set (l1 ⊔ l2)
pr1 (Σ-Set A B) = Σ (type-Set A) (λ x → (type-Set (B x)))
pr2 (Σ-Set A B) = is-set-Σ (is-set-type-Set A) (λ x → is-set-type-Set (B x))

prod-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU-Set (l1 ⊔ l2)
prod-Set A B = Σ-Set A (λ x → B)

-- Exercise 12.5 (b)

abstract
  is-trunc-map-is-trunc-domain-codomain :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1}
    {B : UU l2} {f : A → B} → is-trunc k A → is-trunc k B → is-trunc-map k f
  is-trunc-map-is-trunc-domain-codomain k {f = f} is-trunc-A is-trunc-B b =
    is-trunc-Σ k is-trunc-A (λ x → is-trunc-Id k is-trunc-B (f x) b)

-- Bureaucracy

abstract
  is-trunc-fam-is-trunc-Σ :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    is-trunc k A → is-trunc k (Σ A B) → (x : A) → is-trunc k (B x)
  is-trunc-fam-is-trunc-Σ k {B = B} is-trunc-A is-trunc-ΣAB x =
    is-trunc-equiv' k
      ( fib pr1 x)
      ( equiv-fib-pr1 B x)
      ( is-trunc-map-is-trunc-domain-codomain k is-trunc-ΣAB is-trunc-A x)

-- Exercise 12.6

abstract
  is-trunc-prod :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k A → is-trunc k B → is-trunc k (A × B)
  is-trunc-prod k is-trunc-A is-trunc-B =
    is-trunc-Σ k is-trunc-A (λ x → is-trunc-B)

is-trunc-prod' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (B → is-trunc (succ-𝕋 k) A) → (A → is-trunc (succ-𝕋 k) B) →
  is-trunc (succ-𝕋 k) (A × B)
is-trunc-prod' k f g (pair a b) (pair a' b') =
  is-trunc-equiv k
    ( Eq-prod (pair a b) (pair a' b'))
    ( equiv-pair-eq (pair a b) (pair a' b'))
    ( is-trunc-prod k (f b a a') (g a b b'))

is-trunc-left-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → B → is-trunc k A
is-trunc-left-factor-prod neg-two-𝕋 {A} {B} H b =
  is-contr-left-factor-prod A B H
is-trunc-left-factor-prod (succ-𝕋 k) H b a a' =
  is-trunc-left-factor-prod k {A = Id a a'} {B = Id b b}
    ( is-trunc-equiv' k
      ( Id (pair a b) (pair a' b))
      ( equiv-pair-eq (pair a b) (pair a' b))
      ( H (pair a b) (pair a' b)))
    ( refl)

is-trunc-right-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → A → is-trunc k B
is-trunc-right-factor-prod neg-two-𝕋 {A} {B} H a =
  is-contr-right-factor-prod A B H
is-trunc-right-factor-prod (succ-𝕋 k) {A} {B} H a b b' =
  is-trunc-right-factor-prod k {A = Id a a} {B = Id b b'}
    ( is-trunc-equiv' k
      ( Id (pair a b) (pair a b'))
      ( equiv-pair-eq (pair a b) (pair a b'))
      ( H (pair a b) (pair a b')))
    ( refl)

-- Bureaucracy

abstract
  is-prop-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop A → is-prop B → is-prop (A × B)
  is-prop-prod = is-trunc-prod neg-one-𝕋

prod-Prop : {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
pr1 (prod-Prop P Q) = type-Prop P × type-Prop Q
pr2 (prod-Prop P Q) = is-prop-prod (is-prop-type-Prop P) (is-prop-type-Prop Q)

abstract
  is-set-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A × B)
  is-set-prod = is-trunc-prod zero-𝕋

-- Exercise 12.7

-- Exercise 12.7 (a)

{- In this exercise we show that if A is a retract of B, then so are its 
   identity types. -}

ap-retraction :
  {i j : Level} {A : UU i} {B : UU j}
  (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
  (x y : A) → Id (i x) (i y) → Id x y
ap-retraction i r H x y p =
    ( inv (H x)) ∙ ((ap r p) ∙ (H y))

isretr-ap-retraction :
  {i j : Level} {A : UU i} {B : UU j}
  (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
  (x y : A) → ((ap-retraction i r H x y) ∘ (ap i {x} {y})) ~ id
isretr-ap-retraction i r H x .x refl = left-inv (H x)

retr-ap :
  {i j : Level} {A : UU i} {B : UU j} (i : A → B) →
  retr i → (x y : A) → retr (ap i {x} {y})
pr1 (retr-ap i (pair r H) x y) = ap-retraction i r H x y
pr2 (retr-ap i (pair r H) x y) = isretr-ap-retraction i r H x y

retract-eq :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : A retract-of B) →
  (x y : A) → (Id x y) retract-of (Id (pr1 R x) (pr1 R y))
pr1 (retract-eq (pair i (pair r H)) x y) = ap i
pr2 (retract-eq (pair i (pair r H)) x y) = retr-ap i (pair r H) x y

-- Exercise 12.7 (b)

abstract
  is-trunc-retract-of : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    A retract-of B → is-trunc k B → is-trunc k A
  is-trunc-retract-of neg-two-𝕋 (pair i (pair r H)) is-trunc-B =
    is-contr-retract-of _ (pair i (pair r H)) is-trunc-B
  is-trunc-retract-of (succ-𝕋 k) (pair i retr-i) is-trunc-B x y =
    is-trunc-retract-of k
      ( retract-eq (pair i retr-i) x y)
      ( is-trunc-B (i x) (i y))

-- Exercise 12.8

module _
  {l : Level} {A : UU l}
  where

  fib-const : (x y : A) → fib (const unit A x) y ≃ (Id x y)
  fib-const x y = left-unit-law-prod

  abstract
    is-trunc-map-const-is-trunc :
      (k : 𝕋) → is-trunc (succ-𝕋 k) A →
      (x : A) → is-trunc-map k (const unit A x)
    is-trunc-map-const-is-trunc k is-trunc-A x y =
      is-trunc-equiv k
        ( Id x y)
        ( fib-const x y)
        ( is-trunc-A x y)

  abstract
    is-contr-map-const-is-prop :
      is-prop A → (x : A) → is-contr-map (const unit A x)
    is-contr-map-const-is-prop = is-trunc-map-const-is-trunc neg-two-𝕋

  abstract
    is-equiv-const-is-prop :
      is-prop A → (x : A) → is-equiv (const unit A x)
    is-equiv-const-is-prop H x =
      is-equiv-is-contr-map (is-contr-map-const-is-prop H x)

  abstract
    is-prop-map-const-is-set :
      is-set A → (x : A) → is-prop-map (const unit A x)
    is-prop-map-const-is-set = is-trunc-map-const-is-trunc neg-one-𝕋

  abstract
    is-emb-const-is-set : is-set A → (x : A) → is-emb (const unit A x)
    is-emb-const-is-set H x = is-emb-is-prop-map (is-prop-map-const-is-set H x)

  abstract
    is-0-map-const-is-1-type : is-1-type A → (x : A) → is-0-map (const unit A x)
    is-0-map-const-is-1-type = is-trunc-map-const-is-trunc zero-𝕋

  abstract
    is-faithful-const-is-1-type :
      is-1-type A → (x : A) → is-faithful (const unit A x)
    is-faithful-const-is-1-type H x =
      is-faithful-is-0-map (is-0-map-const-is-1-type H x)

  abstract
    is-trunc-is-trunc-map-const :
      (k : 𝕋) → ((x : A) → is-trunc-map k (const unit A x)) →
      is-trunc (succ-𝕋 k) A
    is-trunc-is-trunc-map-const k is-trunc-const x y =
      is-trunc-equiv' k
        ( Σ unit (λ t → Id x y))
        ( left-unit-law-Σ (λ t → Id x y))
        ( is-trunc-const x y)

  abstract
    is-prop-is-contr-map-const :
      ((x : A) → is-contr-map (const unit A x)) → is-prop A
    is-prop-is-contr-map-const = is-trunc-is-trunc-map-const neg-two-𝕋

  abstract
    is-prop-is-equiv-const :
      ((x : A) → is-equiv (const unit A x)) → is-prop A
    is-prop-is-equiv-const H =
      is-prop-is-contr-map-const (λ x → is-contr-map-is-equiv (H x))

  abstract
    is-set-is-prop-map-const :
      ((x : A) → is-prop-map (const unit A x)) → is-set A
    is-set-is-prop-map-const = is-trunc-is-trunc-map-const neg-one-𝕋

  abstract
    is-set-is-emb-const :
      ((x : A) → is-emb (const unit A x)) → is-set A
    is-set-is-emb-const H =
      is-set-is-prop-map-const (λ x → is-prop-map-is-emb (H x))

  abstract
    is-1-type-is-0-map-const :
      ((x : A) → is-0-map (const unit A x)) → is-1-type A
    is-1-type-is-0-map-const = is-trunc-is-trunc-map-const zero-𝕋

  abstract
    is-1-type-is-faithful-const :
      ((x : A) → is-faithful (const unit A x)) → is-1-type A
    is-1-type-is-faithful-const H =
      is-1-type-is-0-map-const (λ x → is-0-map-is-faithful (H x))

const-equiv :
  {l : Level} (A : UU-Prop l) (x : type-Prop A) → unit ≃ type-Prop A
pr1 (const-equiv A x) = const unit (type-Prop A) x
pr2 (const-equiv A x) = is-equiv-const-is-prop (is-prop-type-Prop A) x

const-emb :
  {l : Level} (A : UU-Set l) (x : type-Set A) → unit ↪ type-Set A
pr1 (const-emb A x) = const unit (type-Set A) x
pr2 (const-emb A x) = is-emb-const-is-set (is-set-type-Set A) x

const-faithful-map :
  {l : Level} (A : UU-1-Type l) (x : type-1-Type A) →
  faithful-map unit (type-1-Type A)
pr1 (const-faithful-map A x) = const unit (type-1-Type A) x
pr2 (const-faithful-map A x) =
  is-faithful-const-is-1-type (is-1-type-type-1-Type A) x

-- Exercise 12.9

map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) → fib (g ∘ h) x → Σ (fib g x) (λ t → fib h (pr1 t))
pr1 (pr1 (map-fib-comp g h x (pair a p))) = h a
pr2 (pr1 (map-fib-comp g h x (pair a p))) = p
pr1 (pr2 (map-fib-comp g h x (pair a p))) = a
pr2 (pr2 (map-fib-comp g h x (pair a p))) = refl

inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) → Σ (fib g x) (λ t → fib h (pr1 t)) → fib (g ∘ h) x
pr1 (inv-map-fib-comp g h c t) = pr1 (pr2 t)
pr2 (inv-map-fib-comp g h c t) = (ap g (pr2 (pr2 t))) ∙ (pr2 (pr1 t))

issec-inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) →
  ((map-fib-comp g h x) ∘ (inv-map-fib-comp g h x)) ~ id
issec-inv-map-fib-comp g h x
  (pair (pair .(h a) refl) (pair a refl)) = refl

isretr-inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) (x : X) →
  ((inv-map-fib-comp g h x) ∘ (map-fib-comp g h x)) ~ id
isretr-inv-map-fib-comp g h .(g (h a)) (pair a refl) = refl

abstract
  is-equiv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) (x : X) →
    is-equiv (map-fib-comp g h x)
  is-equiv-map-fib-comp g h x =
    is-equiv-has-inverse
      ( inv-map-fib-comp g h x)
      ( issec-inv-map-fib-comp g h x)
      ( isretr-inv-map-fib-comp g h x)

abstract
  is-equiv-inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) (x : X) →
    is-equiv (inv-map-fib-comp g h x)
  is-equiv-inv-map-fib-comp g h x =
    is-equiv-has-inverse
      ( map-fib-comp g h x)
      ( isretr-inv-map-fib-comp g h x)
      ( issec-inv-map-fib-comp g h x)

abstract
  is-trunc-map-htpy :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {f g : A → B} → f ~ g → is-trunc-map k g → is-trunc-map k f
  is-trunc-map-htpy k {A} {B} {f} {g} H is-trunc-g b =
    is-trunc-is-equiv k
      ( Σ A (λ z → Id (g z) b))
      ( fib-triangle f g id H b)
      ( is-fiberwise-equiv-is-equiv-triangle f g id H is-equiv-id b)
      ( is-trunc-g b)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  where
  
  abstract
    is-contr-map-htpy : is-contr-map g → is-contr-map f
    is-contr-map-htpy = is-trunc-map-htpy neg-two-𝕋 H

  abstract
    is-prop-map-htpy : is-prop-map g → is-prop-map f
    is-prop-map-htpy = is-trunc-map-htpy neg-one-𝕋 H

  abstract
    is-0-map-htpy : is-0-map g → is-0-map f
    is-0-map-htpy = is-trunc-map-htpy zero-𝕋 H

  abstract
    is-faithful-htpy : is-faithful g → is-faithful f
    is-faithful-htpy K =
      is-faithful-is-0-map (is-0-map-htpy (is-0-map-is-faithful K))

abstract
  is-trunc-map-comp : {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k h → is-trunc-map k f
  is-trunc-map-comp k f g h H is-trunc-g is-trunc-h =
    is-trunc-map-htpy k H
      ( λ x → is-trunc-is-equiv k
        ( Σ (fib g x) (λ t → fib h (pr1 t)))
        ( map-fib-comp g h x)
        ( is-equiv-map-fib-comp g h x)
        ( is-trunc-Σ k
          ( is-trunc-g x)
          ( λ t → is-trunc-h (pr1 t))))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  abstract
    is-contr-map-comp : is-contr-map g → is-contr-map h → is-contr-map f
    is-contr-map-comp = is-trunc-map-comp neg-two-𝕋 f g h H

  abstract
    is-prop-map-comp : is-prop-map g → is-prop-map h → is-prop-map f
    is-prop-map-comp = is-trunc-map-comp neg-one-𝕋 f g h H

  abstract
    is-0-map-comp : is-0-map g → is-0-map h → is-0-map f
    is-0-map-comp = is-trunc-map-comp zero-𝕋 f g h H

  abstract
    is-faithful-comp : is-faithful g → is-faithful h → is-faithful f
    is-faithful-comp K L =
      is-faithful-is-0-map
        (is-0-map-comp (is-0-map-is-faithful K) (is-0-map-is-faithful L))

abstract
  is-trunc-map-right-factor : {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k f → is-trunc-map k h
  is-trunc-map-right-factor k {A} f g h H is-trunc-g is-trunc-f b =
    is-trunc-fam-is-trunc-Σ k
      ( is-trunc-g (g b))
      ( is-trunc-is-equiv' k
        ( Σ A (λ z → Id (g (h z)) (g b)))
        ( map-fib-comp g h (g b))
        ( is-equiv-map-fib-comp g h (g b))
        ( is-trunc-map-htpy k (inv-htpy H) is-trunc-f (g b)))
      ( pair b refl)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  is-contr-map-right-factor : is-contr-map g → is-contr-map f → is-contr-map h
  is-contr-map-right-factor = is-trunc-map-right-factor neg-two-𝕋 f g h H

  is-prop-map-right-factor : is-prop-map g → is-prop-map f → is-prop-map h
  is-prop-map-right-factor = is-trunc-map-right-factor neg-one-𝕋 f g h H

  is-0-map-right-factor : is-0-map g → is-0-map f → is-0-map h
  is-0-map-right-factor = is-trunc-map-right-factor zero-𝕋 f g h H

  is-faithful-right-factor : is-faithful g → is-faithful f → is-faithful h
  is-faithful-right-factor K L =
    is-faithful-is-0-map
      ( is-0-map-right-factor (is-0-map-is-faithful K) (is-0-map-is-faithful L))

-- Exercise 12.10

module _
  {l1 l2 l3 : Level} (k : 𝕋)  {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-trunc-map-tot : ((x : A) → is-trunc-map k (f x)) → is-trunc-map k (tot f)
    is-trunc-map-tot H y =
      is-trunc-equiv k
        ( fib (f (pr1 y)) (pr2 y))
        ( compute-fib-tot f y)
        ( H (pr1 y) (pr2 y))

  abstract
    is-trunc-map-is-trunc-map-tot : 
      is-trunc-map k (tot f) → ((x : A) → is-trunc-map k (f x))
    is-trunc-map-is-trunc-map-tot is-trunc-tot-f x z =
      is-trunc-equiv k
        ( fib (tot f) (pair x z))
        ( inv-compute-fib-tot f (pair x z))
        ( is-trunc-tot-f (pair x z))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-contr-map-tot :
      ((x : A) → is-contr-map (f x)) → is-contr-map (tot f)
    is-contr-map-tot =
      is-trunc-map-tot neg-two-𝕋

  abstract
    is-prop-map-tot : ((x : A) → is-prop-map (f x)) → is-prop-map (tot f)
    is-prop-map-tot = is-trunc-map-tot neg-one-𝕋

  is-emb-tot : ((x : A) → is-emb (f x)) → is-emb (tot f)
  is-emb-tot H =
    is-emb-is-prop-map (is-prop-map-tot (λ x → is-prop-map-is-emb (H x)))

  abstract
    is-0-map-tot : ((x : A) → is-0-map (f x)) → is-0-map (tot f)
    is-0-map-tot = is-trunc-map-tot zero-𝕋

  is-faithful-tot : ((x : A) → is-faithful (f x)) → is-faithful (tot f)
  is-faithful-tot H =
    is-faithful-is-0-map (is-0-map-tot (λ x → is-0-map-is-faithful (H x)))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  tot-emb : ((x : A) → B x ↪ C x) → Σ A B ↪ Σ A C
  pr1 (tot-emb f) = tot (λ x → map-emb (f x))
  pr2 (tot-emb f) = is-emb-tot (λ x → is-emb-map-emb (f x))

  tot-faithful-map :
    ((x : A) → faithful-map (B x) (C x)) → faithful-map (Σ A B) (Σ A C)
  pr1 (tot-faithful-map f) = tot (λ x → map-faithful-map (f x))
  pr2 (tot-faithful-map f) =
    is-faithful-tot (λ x → is-faithful-map-faithful-map (f x))

-- Exercise 12.11

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where
  
  fiber-inclusion : (x : A) → B x → Σ A B
  pr1 (fiber-inclusion x y) = x
  pr2 (fiber-inclusion x y) = y

  fib-fiber-inclusion :
    (a : A) (t : Σ A B) → fib (fiber-inclusion a) t ≃ Id a (pr1 t)
  fib-fiber-inclusion a t =
    ( ( right-unit-law-Σ-is-contr
        ( λ p → is-contr-map-is-equiv (is-equiv-tr B p) (pr2 t))) ∘e
      ( equiv-left-swap-Σ)) ∘e
    ( equiv-tot (λ b → equiv-pair-eq-Σ (pair a b) t))

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1}
  where
  
  is-trunc-is-trunc-map-fiber-inclusion :
    ((B : A → UU l2) (a : A) → is-trunc-map k (fiber-inclusion B a)) →
    is-trunc (succ-𝕋 k) A
  is-trunc-is-trunc-map-fiber-inclusion H x y =
    is-trunc-equiv' k
      ( fib (fiber-inclusion B x) (pair y raise-star))
      ( fib-fiber-inclusion B x (pair y raise-star))
      ( H B x (pair y raise-star))
    where
    B : A → UU l2
    B a = raise-unit l2

  is-trunc-map-fiber-inclusion-is-trunc :
    (B : A → UU l2) (a : A) →
    is-trunc (succ-𝕋 k) A → is-trunc-map k (fiber-inclusion B a)
  is-trunc-map-fiber-inclusion-is-trunc B a H t =
    is-trunc-equiv k
      ( Id a (pr1 t))
      ( fib-fiber-inclusion B a t)
      ( H a (pr1 t))

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-contr-map-fiber-inclusion :
    (x : A) → is-prop A → is-contr-map (fiber-inclusion B x)
  is-contr-map-fiber-inclusion =
    is-trunc-map-fiber-inclusion-is-trunc neg-two-𝕋 B

  is-prop-map-fiber-inclusion :
    (x : A) → is-set A → is-prop-map (fiber-inclusion B x)
  is-prop-map-fiber-inclusion =
    is-trunc-map-fiber-inclusion-is-trunc neg-one-𝕋 B

  is-0-map-fiber-inclusion :
    (x : A) → is-1-type A → is-0-map (fiber-inclusion B x)
  is-0-map-fiber-inclusion =
    is-trunc-map-fiber-inclusion-is-trunc zero-𝕋 B

  is-emb-fiber-inclusion : is-set A → (x : A) → is-emb (fiber-inclusion B x)
  is-emb-fiber-inclusion H x =
    is-emb-is-prop-map (is-prop-map-fiber-inclusion x H)

  is-faithful-fiber-inclusion :
    is-1-type A → (x : A) → is-faithful (fiber-inclusion B x)
  is-faithful-fiber-inclusion H x =
    is-faithful-is-0-map (is-0-map-fiber-inclusion x H)

fiber-inclusion-emb :
  {l1 l2 : Level} (A : UU-Set l1) (B : type-Set A → UU l2) →
  (x : type-Set A) → B x ↪ Σ (type-Set A) B
pr1 (fiber-inclusion-emb A B x) = fiber-inclusion B x
pr2 (fiber-inclusion-emb A B x) = is-emb-fiber-inclusion B (is-set-type-Set A) x

fiber-inclusion-faithful-map :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU l2) →
  (x : type-1-Type A) → faithful-map (B x) (Σ (type-1-Type A) B)
pr1 (fiber-inclusion-faithful-map A B x) = fiber-inclusion B x
pr2 (fiber-inclusion-faithful-map A B x) =
  is-faithful-fiber-inclusion B (is-1-type-type-1-Type A) x

-- Exercise 12.12

is-isolated :
  {l1 : Level} {X : UU l1} (x : X) → UU l1
is-isolated {l1} {X} x = (y : X) → is-decidable (Id x y)

isolated-point :
  {l1 : Level} (X : UU l1) → UU l1
isolated-point X = Σ X is-isolated

-- We will use a few facts about decidability in this exercise

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-map : (A → B) → UU (l1 ⊔ l2)
  is-decidable-map f = (y : B) → is-decidable (fib f y)

  is-decidable-retract-of :
    A retract-of B → is-decidable B → is-decidable A
  is-decidable-retract-of (pair i (pair r H)) (inl b) = inl (r b)
  is-decidable-retract-of (pair i (pair r H)) (inr f) = inr (f ∘ i)

  is-decidable-is-equiv :
    {f : A → B} → is-equiv f → is-decidable B → is-decidable A
  is-decidable-is-equiv {f} (pair (pair g G) (pair h H)) =
    is-decidable-retract-of (pair f (pair h H))

  is-decidable-equiv :
    (e : A ≃ B) → is-decidable B → is-decidable A
  is-decidable-equiv e = is-decidable-iff (map-inv-equiv e) (map-equiv e)

is-decidable-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-decidable A → is-decidable B
is-decidable-equiv' e = is-decidable-equiv (inv-equiv e)

module _
  {l1 : Level} {A : UU l1} (a : A)
  where
  
  -- Exercise 12.12 (a)
  
  is-decidable-map-const-is-isolated :
    is-isolated a → is-decidable-map (const unit A a)
  is-decidable-map-const-is-isolated d x =
    is-decidable-equiv (fib-const a x) (d x)

  is-isolated-is-decidable-map-const :
    is-decidable-map (const unit A a) → is-isolated a
  is-isolated-is-decidable-map-const d x =
    is-decidable-equiv' (fib-const a x) (d x)

  -- Exercise 12.12 (b)
  
  cases-Eq-isolated-point :
    is-isolated a → (x : A) → is-decidable (Id a x) → UU lzero
  cases-Eq-isolated-point H x (inl p) = unit
  cases-Eq-isolated-point H x (inr f) = empty

  abstract
    is-prop-cases-Eq-isolated-point :
      (d : is-isolated a) (x : A) (dx : is-decidable (Id a x)) →
      is-prop (cases-Eq-isolated-point d x dx)
    is-prop-cases-Eq-isolated-point d x (inl p) = is-prop-unit
    is-prop-cases-Eq-isolated-point d x (inr f) = is-prop-empty

  Eq-isolated-point : is-isolated a → A → UU lzero
  Eq-isolated-point d x = cases-Eq-isolated-point d x (d x)

  abstract
    is-prop-Eq-isolated-point :
      (d : is-isolated a) (x : A) → is-prop (Eq-isolated-point d x)
    is-prop-Eq-isolated-point d x =
      is-prop-cases-Eq-isolated-point d x (d x)

  decide-reflexivity :
    (d : is-decidable (Id a a)) → Σ (Id a a) (λ p → Id (inl p) d)
  pr1 (decide-reflexivity (inl p)) = p
  pr2 (decide-reflexivity (inl p)) = refl
  decide-reflexivity (inr f) = ex-falso (f refl)

  abstract
    refl-Eq-isolated-point : (d : is-isolated a) → Eq-isolated-point d a
    refl-Eq-isolated-point d =
      tr ( cases-Eq-isolated-point d a)
        ( pr2 (decide-reflexivity (d a)))
        ( star)

  abstract
    Eq-eq-isolated-point :
      (d : is-isolated a) {x : A} → Id a x → Eq-isolated-point d x
    Eq-eq-isolated-point d refl = refl-Eq-isolated-point d

  abstract
    center-total-Eq-isolated-point :
      (d : is-isolated a) → Σ A (Eq-isolated-point d)
    pr1 (center-total-Eq-isolated-point d) = a
    pr2 (center-total-Eq-isolated-point d) = refl-Eq-isolated-point d
  
    cases-contraction-total-Eq-isolated-point :
      (d : is-isolated a) (x : A) (dx : is-decidable (Id a x))
      (e : cases-Eq-isolated-point d x dx) → Id a x
    cases-contraction-total-Eq-isolated-point d x (inl p) e = p
  
    contraction-total-Eq-isolated-point :
      (d : is-isolated a) (t : Σ A (Eq-isolated-point d)) →
      Id (center-total-Eq-isolated-point d) t
    contraction-total-Eq-isolated-point d (pair x e) =
      eq-subtype
        ( is-prop-Eq-isolated-point d)
        ( cases-contraction-total-Eq-isolated-point d x (d x) e)

    is-contr-total-Eq-isolated-point :
      (d : is-isolated a) → is-contr (Σ A (Eq-isolated-point d))
    pr1 (is-contr-total-Eq-isolated-point d) = center-total-Eq-isolated-point d
    pr2 (is-contr-total-Eq-isolated-point d) =
      contraction-total-Eq-isolated-point d

  abstract
    is-equiv-Eq-eq-isolated-point :
      (d : is-isolated a) (x : A) → is-equiv (Eq-eq-isolated-point d {x})
    is-equiv-Eq-eq-isolated-point d =
      fundamental-theorem-id a
        ( refl-Eq-isolated-point d)
        ( is-contr-total-Eq-isolated-point d)
        ( λ x → Eq-eq-isolated-point d {x})

  abstract
    equiv-Eq-eq-isolated-point :
      (d : is-isolated a) (x : A) → Id a x ≃ Eq-isolated-point d x
    pr1 (equiv-Eq-eq-isolated-point d x) = Eq-eq-isolated-point d
    pr2 (equiv-Eq-eq-isolated-point d x) = is-equiv-Eq-eq-isolated-point d x

  abstract
    is-prop-eq-isolated-point : (d : is-isolated a) (x : A) → is-prop (Id a x)
    is-prop-eq-isolated-point d x =
      is-prop-equiv
        ( equiv-Eq-eq-isolated-point d x)
        ( is-prop-Eq-isolated-point d x)

  abstract
    is-emb-const-is-isolated : is-isolated a → is-emb (const unit A a)
    is-emb-const-is-isolated d star =
      fundamental-theorem-id star
        refl
        ( is-contr-equiv
          ( Id a a)
          ( left-unit-law-prod)
          ( is-proof-irrelevant-is-prop
            ( is-prop-eq-isolated-point d a)
            ( refl)))
        ( λ x → ap (λ y → a))

abstract
  has-decidable-equality-retract-of :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    A retract-of B → has-decidable-equality B → has-decidable-equality A
  has-decidable-equality-retract-of (pair i (pair r H)) d x y =
    is-decidable-retract-of
      ( retract-eq (pair i (pair r H)) x y)
      ( d (i x) (i y))

--------------------------------------------------------------------------------

-- Extra stuff

abstract
  has-decidable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    has-decidable-equality A → ((x : A) → has-decidable-equality (B x)) →
    has-decidable-equality (Σ A B)
  has-decidable-equality-Σ dA dB (pair x y) (pair x' y') with dA x x'
  ... | inr np = inr (λ r → np (ap pr1 r))
  ... | inl p =
    is-decidable-iff eq-pair-Σ' pair-eq-Σ
      ( is-decidable-equiv
        ( left-unit-law-Σ-is-contr
          ( is-proof-irrelevant-is-prop
            ( is-set-has-decidable-equality dA x x') p)
          ( p))
        ( dB x' (tr _ p y) y'))

abstract
  has-decidable-equality-is-prop :
    {l1 : Level} {A : UU l1} → is-prop A → has-decidable-equality A
  has-decidable-equality-is-prop H x y = inl (eq-is-prop H)

abstract
  has-decidable-equality-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    has-decidable-equality B → has-decidable-equality A
  has-decidable-equality-equiv e dB x y =
    is-decidable-equiv (equiv-ap e x y) (dB (map-equiv e x) (map-equiv e y))
  
abstract
  has-decidable-equality-equiv' :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    has-decidable-equality A → has-decidable-equality B
  has-decidable-equality-equiv' e = has-decidable-equality-equiv (inv-equiv e)

abstract
  has-decidable-equality-fiber-has-decidable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    has-decidable-equality A → has-decidable-equality (Σ A B) →
    (x : A) → has-decidable-equality (B x)
  has-decidable-equality-fiber-has-decidable-equality-Σ {B = B} dA dΣ x =
    has-decidable-equality-equiv'
      ( equiv-fib-pr1 B x)
      ( has-decidable-equality-Σ dΣ
        ( λ t →
          has-decidable-equality-is-prop
            ( is-set-has-decidable-equality dA (pr1 t) x)))

is-injective-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-injective (map-section b)
is-injective-map-section b = ap pr1

abstract
  has-decidable-equality-base-has-decidable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    has-decidable-equality (Σ A B) → ((x : A) → has-decidable-equality (B x)) →
    has-decidable-equality A
  has-decidable-equality-base-has-decidable-equality-Σ b dΣ dB =
    has-decidable-equality-equiv'
      ( equiv-total-fib (map-section b))
      ( has-decidable-equality-Σ dΣ
        ( λ t →
          has-decidable-equality-is-prop
            ( is-prop-map-is-injective
              ( is-set-has-decidable-equality dΣ)
              ( is-injective-map-section b)
              ( t))))

abstract
  is-injective-const-true : is-injective (const unit bool true)
  is-injective-const-true {star} {star} p = refl

abstract
  is-injective-const-false : is-injective (const unit bool false)
  is-injective-const-false {star} {star} p = refl

equiv-total-subtype :
  { l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2} {Q : A → UU l3} →
  ( is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q) →
  ( f : (x : A) → P x → Q x) →
  ( g : (x : A) → Q x → P x) →
  ( Σ A P) ≃ (Σ A Q)
pr1 (equiv-total-subtype is-subtype-P is-subtype-Q f g) = tot f
pr2 (equiv-total-subtype is-subtype-P is-subtype-Q f g) =
  is-equiv-tot-is-fiberwise-equiv {f = f}
    ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q x) (g x))

{- We show that if f : A → B is an embedding, then the induced map
   Σ A (C ∘ f) → Σ A C is also an embedding. -}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  is-trunc-map-map-Σ-map-base :
    (k : 𝕋) {f : A → B} (C : B → UU l3) →
    is-trunc-map k f → is-trunc-map k (map-Σ-map-base f C)
  is-trunc-map-map-Σ-map-base k {f} C H y =
    is-trunc-equiv' k
      ( fib f (pr1 y))
      ( equiv-fib-map-Σ-map-base-fib f C y)
      ( H (pr1 y))

  module _
    {f : A → B} (C : B → UU l3)
    where

    abstract
      is-prop-map-map-Σ-map-base :
        is-prop-map f → is-prop-map (map-Σ-map-base f C)
      is-prop-map-map-Σ-map-base = is-trunc-map-map-Σ-map-base neg-one-𝕋 C

    abstract
      is-emb-map-Σ-map-base : is-emb f → is-emb (map-Σ-map-base f C)
      is-emb-map-Σ-map-base H =
        is-emb-is-prop-map (is-prop-map-map-Σ-map-base (is-prop-map-is-emb H))

    abstract
      is-0-map-map-Σ-map-base : is-0-map f → is-0-map (map-Σ-map-base f C)
      is-0-map-map-Σ-map-base = is-trunc-map-map-Σ-map-base zero-𝕋 C

    abstract
      is-faithful-map-Σ-map-base :
        is-faithful f → is-faithful (map-Σ-map-base f C)
      is-faithful-map-Σ-map-base H =
        is-faithful-is-0-map (is-0-map-map-Σ-map-base (is-0-map-is-faithful H))

  emb-Σ-emb-base :
    (f : A ↪ B) (C : B → UU l3) → Σ A (λ a → C (map-emb f a)) ↪ Σ B C
  pr1 (emb-Σ-emb-base f C) = map-Σ-map-base (map-emb f) C
  pr2 (emb-Σ-emb-base f C) =
    is-emb-map-Σ-map-base C (is-emb-map-emb f)

  faithful-map-Σ-faithful-map-base :
    (f : faithful-map A B) (C : B → UU l3) →
    faithful-map (Σ A (λ a → C (map-faithful-map f a))) (Σ B C)
  pr1 (faithful-map-Σ-faithful-map-base f C) =
    map-Σ-map-base (map-faithful-map f) C
  pr2 (faithful-map-Σ-faithful-map-base f C) =
    is-faithful-map-Σ-map-base C (is-faithful-map-faithful-map f)
    
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  where

  is-trunc-map-map-Σ :
    (k : 𝕋) (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)} →
    is-trunc-map k f → ((x : A) → is-trunc-map k (g x)) →
    is-trunc-map k (map-Σ D f g)
  is-trunc-map-map-Σ k D {f} {g} H K = 
    is-trunc-map-comp k
      ( map-Σ D f g)
      ( map-Σ-map-base f D)
      ( tot g)
      ( triangle-map-Σ D f g)
      ( is-trunc-map-map-Σ-map-base k D H)
      ( is-trunc-map-tot k K)

  module _
    (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)}
    where

    is-contr-map-map-Σ :
      is-contr-map f → ((x : A) → is-contr-map (g x)) →
      is-contr-map (map-Σ D f g)
    is-contr-map-map-Σ = is-trunc-map-map-Σ neg-two-𝕋 D

    is-prop-map-map-Σ :
      is-prop-map f → ((x : A) → is-prop-map (g x)) → is-prop-map (map-Σ D f g)
    is-prop-map-map-Σ = is-trunc-map-map-Σ neg-one-𝕋 D

    is-emb-map-Σ :
      is-emb f → ((x : A) → is-emb (g x)) → is-emb (map-Σ D f g)
    is-emb-map-Σ H K =
      is-emb-is-prop-map
        ( is-prop-map-map-Σ
          ( is-prop-map-is-emb H)
          ( λ x → is-prop-map-is-emb (K x)))

    is-0-map-map-Σ :
      is-0-map f → ((x : A) → is-0-map (g x)) → is-0-map (map-Σ D f g)
    is-0-map-map-Σ = is-trunc-map-map-Σ zero-𝕋 D

    is-faithful-map-Σ :
      is-faithful f → ((x : A) → is-faithful (g x)) → is-faithful (map-Σ D f g)
    is-faithful-map-Σ H K =
      is-faithful-is-0-map
        ( is-0-map-map-Σ
          ( is-0-map-is-faithful H)
          ( λ x → is-0-map-is-faithful (K x)))

  emb-Σ :
    (D : B → UU l4) (f : A ↪ B) (g : (x : A) → C x ↪ D (map-emb f x)) →
    Σ A C ↪ Σ B D
  pr1 (emb-Σ D f g) = map-Σ D (map-emb f) (λ x → map-emb (g x))
  pr2 (emb-Σ D f g) =
    is-emb-map-Σ D (is-emb-map-emb f) (λ x → is-emb-map-emb (g x))
