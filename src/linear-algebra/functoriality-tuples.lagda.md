# Functoriality of the type of tuples

```agda
module linear-algebra.functoriality-tuples where
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

open import linear-algebra.tuples

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Any map `f : A → B` determines a map `tuple A n → tuple B n` for every `n`.

## Definition

### Functoriality of the type of listed tuples

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

### Functoriality of the type of functional tuples

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-functional-tuple :
    (n : ℕ) → (A → B) → functional-tuple A n → functional-tuple B n
  map-functional-tuple n f v = f ∘ v

  htpy-functional-tuple :
    (n : ℕ) {f g : A → B} → (f ~ g) →
    map-functional-tuple n f ~ map-functional-tuple n g
  htpy-functional-tuple n = htpy-postcomp (Fin n)
```

### Binary functoriality of the type of functional tuples

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  binary-map-functional-tuple :
    (n : ℕ) → (A → B → C) →
    functional-tuple A n → functional-tuple B n → functional-tuple C n
  binary-map-functional-tuple n f v w i = f (v i) (w i)
```

### Link between functoriality of the type of tuples and of the type of functional tuples

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B)
  where

  map-tuple-map-functional-tuple :
    (n : ℕ) (v : tuple A n) →
    listed-tuple-functional-tuple
      ( n)
      ( map-functional-tuple n f (functional-tuple-tuple n v)) ＝
    map-tuple f v
  map-tuple-map-functional-tuple zero-ℕ empty-tuple = refl
  map-tuple-map-functional-tuple (succ-ℕ n) (x ∷ v) =
    eq-Eq-tuple
      ( succ-ℕ n)
      ( listed-tuple-functional-tuple
        ( succ-ℕ n)
        ( map-functional-tuple
          ( succ-ℕ n)
          ( f)
          ( functional-tuple-tuple (succ-ℕ n) (x ∷ v))))
      ( map-tuple f (x ∷ v))
      ( refl ,
        Eq-eq-tuple
          ( n)
          ( listed-tuple-functional-tuple
            ( n)
            ( map-functional-tuple n f (functional-tuple-tuple n v)))
          ( map-tuple f v)
          ( map-tuple-map-functional-tuple n v))
```
