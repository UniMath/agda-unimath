# Set quotients of finite sequences

```agda
module lists.set-quotients-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.equivalence-relations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import lists.equivalence-relations-finite-sequences
open import lists.finite-sequences

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.set-quotients-dependent-products-finite-families-equivalence-relations
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

For any [equivalence relation](foundation.equivalence-relations.md) `R` on a
type `A`, the type of [finite sequences](lists.finite-sequences.md) of length
`n` in the [set quotient](foundation.set-quotients.md) `A/R` satisfies the
[universal property of the set quotient](foundation.universal-property-set-quotients.md)
for the
[induced equivalence relation](lists.equivalence-relations-finite-sequences.md)
of `R` on finite sequences of length `n` in `A`.

## Definition

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : equivalence-relation l2 A)
  (n : ℕ)
  where

  reflecting-quotient-map-fin-sequence :
    reflecting-map-equivalence-relation
      ( fin-sequence-equivalence-relation R n)
      ( fin-sequence (set-quotient R) n)
  reflecting-quotient-map-fin-sequence =
    reflecting-quotient-map-Π-finite-family-set-quotient
      ( Fin-Finite-Type n)
      ( λ _ → R)

  abstract
    is-set-quotient-fin-sequence-set-quotient :
      is-set-quotient
        ( fin-sequence-equivalence-relation R n)
        ( fin-sequence-Set (quotient-Set R) n)
        ( reflecting-quotient-map-fin-sequence)
    is-set-quotient-fin-sequence-set-quotient =
      is-set-quotient-Π-finite-family-set-quotient
        ( Fin-Finite-Type n)
        ( λ _ → R)
```
