# The maybe modality

```agda
module foundation.maybe where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
```

</details>

## Idea

The maybe modality is an operation on types that adds one point. This is used,
for example, to define partial functions, where a partial function `f : X ⇀ Y`
is a map `f : X → Maybe Y`.

## Definitions

### The Maybe modality

```agda
Maybe : {l : Level} → UU l → UU l
Maybe X = X + unit

data Maybe' {l} (X : UU l) : UU l where
  unit-Maybe' : X → Maybe' X
  exception-Maybe' : Maybe' X

{-# BUILTIN MAYBE Maybe' #-}

unit-Maybe : {l : Level} {X : UU l} → X → Maybe X
unit-Maybe = inl

exception-Maybe : {l : Level} {X : UU l} → Maybe X
exception-Maybe {l} {X} = inr star
```

### The predicate of being an exception

```agda
is-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-exception-Maybe {l} {X} x = (x ＝ exception-Maybe)

is-not-exception-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-not-exception-Maybe x = ¬ (is-exception-Maybe x)
```

### The predicate of being a value

```agda
is-value-Maybe : {l : Level} {X : UU l} → Maybe X → UU l
is-value-Maybe {l} {X} x = Σ X (λ y → inl y ＝ x)

value-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-value-Maybe x → X
value-is-value-Maybe x = pr1

eq-is-value-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) (H : is-value-Maybe x) →
  inl (value-is-value-Maybe x H) ＝ x
eq-is-value-Maybe x H = pr2 H
```

### Maybe structure on a type

```agda
maybe-structure : {l1 : Level} (X : UU l1) → UU (lsuc l1)
maybe-structure {l1} X = Σ (UU l1) (λ Y → Maybe Y ≃ X)
```

## Properties

### The unit of Maybe is an embedding

```agda
abstract
  is-emb-unit-Maybe : {l : Level} {X : UU l} → is-emb (unit-Maybe {X = X})
  is-emb-unit-Maybe = is-emb-inl

emb-unit-Maybe : {l : Level} (X : UU l) → X ↪ Maybe X
pr1 (emb-unit-Maybe X) = unit-Maybe
pr2 (emb-unit-Maybe X) = is-emb-unit-Maybe

abstract
  is-injective-unit-Maybe :
    {l : Level} {X : UU l} → is-injective (unit-Maybe {X = X})
  is-injective-unit-Maybe = is-injective-inl
```

### Being an exception is decidable

```agda
is-decidable-is-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-exception-Maybe x)
is-decidable-is-exception-Maybe {l} {X} (inl x) =
  inr (λ p → ex-falso (is-empty-eq-coproduct-inl-inr x star p))
is-decidable-is-exception-Maybe (inr star) = inl refl

is-decidable-is-not-exception-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-decidable (is-not-exception-Maybe x)
is-decidable-is-not-exception-Maybe x =
  is-decidable-neg (is-decidable-is-exception-Maybe x)
```

### The values of the unit of the Maybe modality are not exceptions

```agda
abstract
  is-not-exception-unit-Maybe :
    {l : Level} {X : UU l} (x : X) → is-not-exception-Maybe (unit-Maybe x)
  is-not-exception-unit-Maybe {l} {X} x ()
```

### For any element of type `Maybe X` we can decide whether it is a value or an exception

```agda
decide-Maybe :
  {l : Level} {X : UU l} (x : Maybe X) → is-value-Maybe x + is-exception-Maybe x
decide-Maybe (inl x) = inl (pair x refl)
decide-Maybe (inr star) = inr refl
```

### Values are not exceptions

```agda
abstract
  is-not-exception-is-value-Maybe :
    {l1 : Level} {X : UU l1} (x : Maybe X) →
    is-value-Maybe x → is-not-exception-Maybe x
  is-not-exception-is-value-Maybe {l1} {X} .(inl x) (pair x refl) =
    is-not-exception-unit-Maybe x
```

### If a point is not an exception, then it is a value

```agda
is-value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) →
  is-not-exception-Maybe x → is-value-Maybe x
is-value-is-not-exception-Maybe x H =
  map-right-unit-law-coproduct-is-empty
    ( is-value-Maybe x)
    ( is-exception-Maybe x)
    ( H)
    ( decide-Maybe x)

value-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) → is-not-exception-Maybe x → X
value-is-not-exception-Maybe x H =
  value-is-value-Maybe x (is-value-is-not-exception-Maybe x H)

eq-is-not-exception-Maybe :
  {l1 : Level} {X : UU l1} (x : Maybe X) (H : is-not-exception-Maybe x) →
  inl (value-is-not-exception-Maybe x H) ＝ x
eq-is-not-exception-Maybe x H =
  eq-is-value-Maybe x (is-value-is-not-exception-Maybe x H)
```

### The two definitions of `Maybe` are equal

```agda
equiv-Maybe-Maybe' :
  {l1 l2 : Level} {X : UU l1} → Maybe X ≃ Maybe' X
pr1 equiv-Maybe-Maybe' (inl x) = unit-Maybe' x
pr1 equiv-Maybe-Maybe' (inr star) = exception-Maybe'
pr1 (pr1 (pr2 equiv-Maybe-Maybe')) (unit-Maybe' x) = inl x
pr1 (pr1 (pr2 equiv-Maybe-Maybe')) exception-Maybe' = inr star
pr2 (pr1 (pr2 equiv-Maybe-Maybe')) (unit-Maybe' x) = refl
pr2 (pr1 (pr2 equiv-Maybe-Maybe')) exception-Maybe' = refl
pr1 (pr2 (pr2 equiv-Maybe-Maybe')) (unit-Maybe' x) = inl x
pr1 (pr2 (pr2 equiv-Maybe-Maybe')) exception-Maybe' = inr star
pr2 (pr2 (pr2 equiv-Maybe-Maybe')) (inl x) = refl
pr2 (pr2 (pr2 equiv-Maybe-Maybe')) (inr star) = refl
```
