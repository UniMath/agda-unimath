# Relationship between functoriality of tuples and finite sequences

```agda
module lists.functoriality-tuples-finite-sequences where
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

open import lists.equivalence-tuples-finite-sequences
open import lists.finite-sequences
open import lists.functoriality-finite-sequences
open import lists.functoriality-tuples
open import lists.tuples

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Mapping a function over a [tuple](lists.tuples.md) is equivalent to mapping the
same function over the
[corresponding](lists.equivalence-tuples-finite-sequences.md)
[finite sequence](lists.finite-sequences.md)

## Proof

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B)
  where

  map-tuple-map-fin-sequence :
    (n : ℕ) (v : tuple A n) →
    tuple-fin-sequence
      ( n)
      ( map-fin-sequence n f (fin-sequence-tuple n v)) ＝
    map-tuple f v
  map-tuple-map-fin-sequence zero-ℕ empty-tuple = refl
  map-tuple-map-fin-sequence (succ-ℕ n) (x ∷ v) =
    eq-Eq-tuple
      ( succ-ℕ n)
      ( tuple-fin-sequence
        ( succ-ℕ n)
        ( map-fin-sequence
          ( succ-ℕ n)
          ( f)
          ( fin-sequence-tuple (succ-ℕ n) (x ∷ v))))
      ( map-tuple f (x ∷ v))
      ( refl ,
        Eq-eq-tuple
          ( n)
          ( tuple-fin-sequence
            ( n)
            ( map-fin-sequence n f (fin-sequence-tuple n v)))
          ( map-tuple f v)
          ( map-tuple-map-fin-sequence n v))
```
