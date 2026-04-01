# Reversed tuples

```agda
module lists.reversed-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.involutions
open import foundation.universe-levels

open import lists.tuples
```

</details>

## Idea

The {{#concept "reverse" Disambiguation="of a tuple" Agda=reverse-tuple}} of a
[tuple](lists.tuples.md) `x₁, x₂, ..., xₙ` is `xₙ, xₙ₋₁, ..., x₁`.

## Definition

```agda
module _
  {l : Level}
  {A : UU l}
  where

  reverse-tuple : {n : ℕ} → tuple A n → tuple A n
  reverse-tuple empty-tuple = empty-tuple
  reverse-tuple (x ∷ v) = snoc-tuple (reverse-tuple v) x
```

## Properties

### Reversing tuples is an involution

```agda
module _
  {l : Level}
  {A : UU l}
  where

  abstract
    reverse-snoc-tuple :
      {n : ℕ} (xs : tuple A n) (x : A) →
      reverse-tuple (snoc-tuple xs x) ＝ x ∷ reverse-tuple xs
    reverse-snoc-tuple empty-tuple x = refl
    reverse-snoc-tuple (y ∷ ys) x =
      ap (λ ys' → snoc-tuple ys' y) (reverse-snoc-tuple ys x)

    is-involution-reverse-tuple :
      {n : ℕ} (xs : tuple A n) → reverse-tuple (reverse-tuple xs) ＝ xs
    is-involution-reverse-tuple empty-tuple = refl
    is-involution-reverse-tuple (x ∷ xs) =
      ( reverse-snoc-tuple (reverse-tuple xs) x) ∙
      ( ap (x ∷_) (is-involution-reverse-tuple xs))
```
