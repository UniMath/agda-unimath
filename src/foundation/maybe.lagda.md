# The maybe modality

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module foundation.maybe where

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using
  ( coprod; inl; inr; is-injective-inl)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-neg)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.empty-types using (ex-falso)
open import foundation.equality-coproduct-types using
  ( is-emb-inl; is-empty-eq-coprod-inl-inr)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; refl)
open import foundation.injective-maps using (is-injective)
open import foundation.negation using (¬)
open import foundation.type-arithmetic-empty-type using
  ( map-right-unit-law-coprod-is-empty)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU)
```

## Idea

The maybe modality is an operation on types that adds one point. This is used, for example, to define partial functions, where a partial function `f : X ⇀ Y` is a map `f : X → Maybe Y`.

```agda
-- The Maybe modality

Maybe : {l : Level} → UU l → UU l
Maybe X = coprod X unit

unit-Maybe : {l : Level} {X : UU l} → X → Maybe X
unit-Maybe = inl

abstract
  is-emb-unit-Maybe : {l : Level} {X : UU l} → is-emb (unit-Maybe {X = X})
  is-emb-unit-Maybe {l} {X} = is-emb-inl X unit

emb-unit-Maybe : {l : Level} (X : UU l) → X ↪ Maybe X
pr1 (emb-unit-Maybe X) = unit-Maybe
pr2 (emb-unit-Maybe X) = is-emb-unit-Maybe

abstract
  is-injective-unit-Maybe :
    {l : Level} {X : UU l} → is-injective (unit-Maybe {X = X})
  is-injective-unit-Maybe = is-injective-inl

-- The exception
exception-Maybe : {l : Level} {X : UU l} → Maybe X
exception-Maybe {l} {X} = inr star

-- The is-exception predicate
is-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-exception-Maybe {l} {X} x = Id x exception-Maybe

-- The is-exception predicate is decidable
is-decidable-is-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-exception-Maybe x)
is-decidable-is-exception-Maybe {l} {X} (inl x) =
  inr (λ p → ex-falso (is-empty-eq-coprod-inl-inr x star p))
is-decidable-is-exception-Maybe (inr star) = inl refl

-- The is-not-exception predicate
is-not-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-not-exception-Maybe x = ¬ (is-exception-Maybe x)

abstract
  is-not-exception-unit-Maybe :
    {l : Level} {X : UU l} (x : X) → is-not-exception-Maybe (unit-Maybe x)
  is-not-exception-unit-Maybe {l} {X} x ()

-- The is-not-exception predicate is decidable
is-decidable-is-not-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-not-exception-Maybe x)
is-decidable-is-not-exception-Maybe x =
  is-decidable-neg (is-decidable-is-exception-Maybe x)

-- The is-value predicate
is-value-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-value-Maybe {l} {X} x = Σ X (λ y → Id (inl y) x)

value-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-value-Maybe x → X
value-is-value-Maybe x = pr1

eq-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) (H : is-value-Maybe x) →
  Id (inl (value-is-value-Maybe x H)) x
eq-is-value-Maybe x H = pr2 H

-- The decision procedure whether something is a value or an exception
decide-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) →
  coprod (is-value-Maybe x) (is-exception-Maybe x)
decide-Maybe (inl x) = inl (pair x refl)
decide-Maybe (inr star) = inr refl

-- If a point is not an exception, then it is a value
is-value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) →
  is-not-exception-Maybe x → is-value-Maybe x
is-value-is-not-exception-Maybe x H =
  map-right-unit-law-coprod-is-empty (is-value-Maybe x) (is-exception-Maybe x) H (decide-Maybe x)

value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) → is-not-exception-Maybe x → X
value-is-not-exception-Maybe x H =
  value-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

eq-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) (H : is-not-exception-Maybe x) →
  Id (inl (value-is-not-exception-Maybe x H)) x
eq-is-not-exception-Maybe x H =
  eq-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

-- If a point is a value, then it is not an exception
abstract
  is-not-exception-is-value-Maybe :
    {l1 : Level} {X : UU l1} (x : Maybe X) →
    is-value-Maybe x → is-not-exception-Maybe x
  is-not-exception-is-value-Maybe {l1} {X} .(inl x) (pair x refl) =
    is-not-exception-unit-Maybe x
```
