# Functoriality of the type of vectors

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.functoriality-vectors where

open import elementary-number-theory.natural-numbers

open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

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

htpy-vec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {n : ℕ} {f g : A → B} →
  (f ~ g) → map-vec {n = n} f ~ map-vec {n = n} g
htpy-vec H empty-vec = refl
htpy-vec H (x ∷ v) = ap-binary _∷_ (H x) (htpy-vec H v)
```

### Binary functoriality of vec

```agda
map-binary-vec :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {n : ℕ}
  (f : A → B → C) → vec A n → vec B n → vec C n
map-binary-vec f empty-vec empty-vec = empty-vec
map-binary-vec f (x ∷ v) (y ∷ w) = f x y ∷ map-binary-vec f v w
```
