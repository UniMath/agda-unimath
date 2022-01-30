# Sets

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.sets where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using (is-contr; contraction)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id-retr)
open import foundation.identity-types using (Id; refl; inv; _∙_; ind-Id)
open import foundation.propositions using
  ( is-prop; UU-Prop; all-elements-equal; is-prop-all-elements-equal;
    is-proof-irrelevant-is-prop; eq-is-prop; is-prop-is-equiv')
open import foundation.truncated-types using
  ( is-trunc-succ-is-trunc; truncated-type-succ-Truncated-Type;
    is-trunc-is-contr; is-trunc-is-equiv; is-trunc-equiv; is-trunc-is-equiv';
    is-trunc-equiv'; is-trunc-Σ; is-trunc-prod)
open import foundation.truncation-levels using (neg-one-𝕋; zero-𝕋)
open import foundation.universe-levels using (Level; UU; lsuc; lzero; _⊔_)
```

## Idea

A type is a set if its identity types are propositions.

## Definition

```agda
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
```

## Properties

### A type is a set if and only if it satisfies Streicher's axiom K

```agda
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
```

### If a reflexive binary relation maps into the identity type of A, then A is a set

```
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
```

### Any proposition is a set

```agda
abstract
  is-set-is-prop :
    {l : Level} {P : UU l} → is-prop P → is-set P
  is-set-is-prop = is-trunc-succ-is-trunc neg-one-𝕋

set-Prop :
  {l : Level} → UU-Prop l → UU-Set l
set-Prop P = truncated-type-succ-Truncated-Type neg-one-𝕋 P
```

### Any contractible type is a set

```agda
abstract
  is-set-is-contr :
    {l : Level} {A : UU l} → is-contr A → is-set A
  is-set-is-contr = is-trunc-is-contr zero-𝕋
```

### Sets are closed under equivalences

```agda
abstract
  is-set-is-equiv :
    {i j : Level} {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
    is-set B → is-set A
  is-set-is-equiv = is-trunc-is-equiv zero-𝕋

abstract
  is-set-equiv :
    {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) →
    is-set B → is-set A
  is-set-equiv = is-trunc-equiv zero-𝕋

abstract
  is-set-is-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (f : A → B) → is-equiv f →
    is-set A → is-set B
  is-set-is-equiv' = is-trunc-is-equiv' zero-𝕋

abstract
  is-set-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) →
    is-set A → is-set B
  is-set-equiv' = is-trunc-equiv' zero-𝕋
```

### Sets are closed under dependent pair types

```agda
abstract
  is-set-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → ((x : A) → is-set (B x)) → is-set (Σ A B)
  is-set-Σ = is-trunc-Σ {k = zero-𝕋}

Σ-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : pr1 A → UU-Set l2) → UU-Set (l1 ⊔ l2)
pr1 (Σ-Set A B) = Σ (type-Set A) (λ x → (type-Set (B x)))
pr2 (Σ-Set A B) = is-set-Σ (is-set-type-Set A) (λ x → is-set-type-Set (B x))
```

### Sets are closed under cartesian product types

```agda
abstract
  is-set-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A × B)
  is-set-prod = is-trunc-prod zero-𝕋
  
prod-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU-Set (l1 ⊔ l2)
prod-Set A B = Σ-Set A (λ x → B)
```
