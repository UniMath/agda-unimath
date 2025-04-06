# Functoriality of the type of vectors

```agda
module linear-algebra.functoriality-vectors where
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

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Any map `f : A → B` determines a map `vec A n → vec B n` for every `n`.

## Definition

### Functoriality of the type of listed vectors

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-vec : {n : ℕ} → (A → B) → vec A n → vec B n
  map-vec _ empty-vec = empty-vec
  map-vec f (x ∷ xs) = f x ∷ map-vec f xs

  htpy-vec :
    {n : ℕ} {f g : A → B} → (f ~ g) → map-vec {n = n} f ~ map-vec {n = n} g
  htpy-vec H empty-vec = refl
  htpy-vec H (x ∷ v) = ap-binary _∷_ (H x) (htpy-vec H v)
```

### Binary functoriality of the type of listed vectors

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  binary-map-vec :
    {n : ℕ} → (A → B → C) → vec A n → vec B n → vec C n
  binary-map-vec f empty-vec empty-vec = empty-vec
  binary-map-vec f (x ∷ v) (y ∷ w) = f x y ∷ binary-map-vec f v w
```

### Functoriality of the type of functional vectors

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-functional-vec :
    (n : ℕ) → (A → B) → functional-vec A n → functional-vec B n
  map-functional-vec n f v = f ∘ v

  htpy-functional-vec :
    (n : ℕ) {f g : A → B} → (f ~ g) →
    map-functional-vec n f ~ map-functional-vec n g
  htpy-functional-vec n = htpy-postcomp (Fin n)
```

### Binary functoriality of the type of functional vectors

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  binary-map-functional-vec :
    (n : ℕ) → (A → B → C) →
    functional-vec A n → functional-vec B n → functional-vec C n
  binary-map-functional-vec n f v w i = f (v i) (w i)
```

### Link between functoriality of the type of vectors and of the type of functional vectors

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B)
  where

  map-vec-map-functional-vec :
    (n : ℕ) (v : vec A n) →
    listed-vec-functional-vec
      ( n)
      ( map-functional-vec n f (functional-vec-vec n v)) ＝
    map-vec f v
  map-vec-map-functional-vec zero-ℕ empty-vec = refl
  map-vec-map-functional-vec (succ-ℕ n) (x ∷ v) =
    eq-Eq-vec
      ( succ-ℕ n)
      ( listed-vec-functional-vec
        ( succ-ℕ n)
        ( map-functional-vec
          ( succ-ℕ n)
          ( f)
          ( functional-vec-vec (succ-ℕ n) (x ∷ v))))
      ( map-vec f (x ∷ v))
      ( refl ,
        Eq-eq-vec
          ( n)
          ( listed-vec-functional-vec
            ( n)
            ( map-functional-vec n f (functional-vec-vec n v)))
          ( map-vec f v)
          ( map-vec-map-functional-vec n v))
```
