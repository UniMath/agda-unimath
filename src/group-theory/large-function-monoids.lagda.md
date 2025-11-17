# Large function monoids

```agda
module group-theory.large-function-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.function-large-similarity-relations
open import foundation.universe-levels

open import group-theory.large-function-semigroups
open import group-theory.large-monoids
```

</details>

## Idea

Given a [large monoid](group-theory.large-monoids.md) `M` and an arbitrary type
`A`, `A → M` forms a large monoid.

## Definition

```agda
module _
  {l1 : Level}
  {α : Level → Level}
  {β : Level → Level → Level}
  (A : UU l1)
  (M : Large-Monoid α β)
  where

  function-Large-Monoid :
    Large-Monoid (λ l → l1 ⊔ α l) (λ l2 l3 → l1 ⊔ β l2 l3)
  large-semigroup-Large-Monoid function-Large-Monoid =
    function-Large-Semigroup A (large-semigroup-Large-Monoid M)
  large-similarity-relation-Large-Monoid function-Large-Monoid =
    function-Large-Similarity-Relation
      ( A)
      ( large-similarity-relation-Large-Monoid M)
  raise-Large-Monoid function-Large-Monoid l f a = raise-Large-Monoid M l (f a)
  sim-raise-Large-Monoid function-Large-Monoid l2 f a =
    sim-raise-Large-Monoid M l2 (f a)
  preserves-sim-mul-Large-Monoid function-Large-Monoid f f' f~f' g g' g~g' a =
    preserves-sim-mul-Large-Monoid M (f a) (f' a) (f~f' a) (g a) (g' a) (g~g' a)
  unit-Large-Monoid function-Large-Monoid a = unit-Large-Monoid M
  left-unit-law-mul-Large-Monoid function-Large-Monoid f =
    eq-htpy (λ a → left-unit-law-mul-Large-Monoid M (f a))
  right-unit-law-mul-Large-Monoid function-Large-Monoid f =
    eq-htpy (λ a → right-unit-law-mul-Large-Monoid M (f a))
```
