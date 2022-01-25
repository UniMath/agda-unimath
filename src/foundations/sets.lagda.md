---
title: Univalent Mathematics in Agda
---

# Sets

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.sets where

open import foundations.contractible-types using (is-contr; contraction)
open import foundations.coproduct-types using (inl; inr)
open import foundations.decidable-equality using (has-decidable-equality)
open import foundations.decidable-types using (is-decidable)
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.empty-type using (empty; ex-falso)
open import foundations.equivalences using (is-equiv; _≃_)
open import foundations.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id-retr)
open import foundations.identity-types using (Id; refl; inv; _∙_; ind-Id)
open import foundations.levels using (Level; UU; lsuc; lzero)
open import foundations.propositions using
  ( is-prop; UU-Prop; all-elements-equal; is-prop-all-elements-equal;
    is-proof-irrelevant-is-prop; eq-is-prop; is-prop-is-equiv'; is-prop-unit;
    is-prop-empty)
open import foundations.truncated-types using
  ( is-trunc-succ-is-trunc; truncated-type-succ-Truncated-Type;
    is-trunc-is-contr; is-trunc-is-equiv; is-trunc-equiv; is-trunc-is-equiv';
    is-trunc-equiv')
open import foundations.truncation-levels using (neg-one-𝕋; zero-𝕋)
open import foundations.unit-type using (unit; star)
```

A type is a set if its identity types are propositions

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

## Streicher's axiom K

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

## If a reflexive binary relation maps into the identity type of A, then A is a set

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

## Hedberg's theorem

```agda
module _
  {l : Level} {A : UU l}
  where

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
```

```agda
abstract
  is-set-is-prop :
    {l : Level} {P : UU l} → is-prop P → is-set P
  is-set-is-prop = is-trunc-succ-is-trunc neg-one-𝕋

set-Prop :
  {l : Level} → UU-Prop l → UU-Set l
set-Prop P = truncated-type-succ-Truncated-Type neg-one-𝕋 P
```

```agda
abstract
  is-set-is-contr :
    {l : Level} {A : UU l} → is-contr A → is-set A
  is-set-is-contr = is-trunc-is-contr zero-𝕋
```

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
