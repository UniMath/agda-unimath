# Functoriality of the type of vectors

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.functoriality-vectors where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.universe-levels using (Level; UU)

open import linear-algebra.vectors using (vec; empty-vec; _∷_)
```

## Idea

Any map `f : A → B` determines a map `vec n A → vec n B` for every `n`.

## Definition

### Functoriality of vec

```agda
map-vec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {n : ℕ} → (A → B) → vec A n → vec B n
map-vec _ empty-vec = empty-vec
map-vec f (x ∷ xs) = f x ∷ map-vec f xs
```

### Binary functoriality of vec

```agda
map-binary-vec :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {n : ℕ}
  (f : A → B → C) → vec A n → vec B n → vec C n
map-binary-vec f empty-vec empty-vec = empty-vec
map-binary-vec f (x ∷ v) (y ∷ w) = f x y ∷ map-binary-vec f v w
```
