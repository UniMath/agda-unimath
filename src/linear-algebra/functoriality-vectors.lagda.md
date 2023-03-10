# Functoriality of the type of vectors

```agda
module linear-algebra.functoriality-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.function-extensionality
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.vectors
```

</details>

## Idea

Any map `f : A → B` determines a map `vec n A → vec n B` for every `n`.

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
    (n : ℕ) {f g : A → B} → (f ~ g) → map-functional-vec n f ~ map-functional-vec n g
  htpy-functional-vec n H v = eq-htpy (H ·r v)
```

### Binary functoriality of the type of functional vectors

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

 binary-map-functional-vec :
   (n : ℕ) → (A → B → C) → functional-vec A n → functional-vec B n → functional-vec C n
 binary-map-functional-vec n f v w i = f (v i) (w i)
```
