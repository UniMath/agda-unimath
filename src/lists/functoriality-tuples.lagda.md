# Functoriality of the type of tuples

```agda
module lists.functoriality-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import lists.tuples

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Any map `f : A → B` determines a map between [tuples](lists.tuples.md)
`tuple A n → tuple B n` for every `n`.

## Definition

### Functoriality of the type of tuples

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-tuple : {n : ℕ} → (A → B) → tuple A n → tuple B n
  map-tuple _ empty-tuple = empty-tuple
  map-tuple f (x ∷ xs) = f x ∷ map-tuple f xs

  htpy-tuple :
    {n : ℕ} {f g : A → B} → (f ~ g) → map-tuple {n = n} f ~ map-tuple {n = n} g
  htpy-tuple H empty-tuple = refl
  htpy-tuple H (x ∷ v) = ap-binary _∷_ (H x) (htpy-tuple H v)
```

### Binary functoriality of the type of listed tuples

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  binary-map-tuple :
    {n : ℕ} → (A → B → C) → tuple A n → tuple B n → tuple C n
  binary-map-tuple f empty-tuple empty-tuple = empty-tuple
  binary-map-tuple f (x ∷ v) (y ∷ w) = f x y ∷ binary-map-tuple f v w
```
