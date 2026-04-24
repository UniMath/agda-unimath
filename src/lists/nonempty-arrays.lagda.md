# Nonempty arrays

```agda
module lists.nonempty-arrays where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import lists.arrays
open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An [array](lists.arrays.md) is
{{#concept "nonempty" Disambiguation="arrays" Agda=is-nonempty-array}} if it has
at least one element.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  is-nonempty-array-Prop : array A → Prop lzero
  is-nonempty-array-Prop (zero-ℕ , t) = empty-Prop
  is-nonempty-array-Prop (succ-ℕ n , t) = unit-Prop

  is-nonempty-array : array A → UU lzero
  is-nonempty-array = type-Prop ∘ is-nonempty-array-Prop

nonempty-array : {l : Level} → UU l → UU l
nonempty-array A = type-subtype (is-nonempty-array-Prop {A = A})

module _
  {l : Level} {A : UU l}
  where

  length-nonempty-array : nonempty-array A → ℕ
  length-nonempty-array ((n , _) , _) = n

  is-nonzero-length-nonempty-array :
    (a : nonempty-array A) → is-nonzero-ℕ (length-nonempty-array a)
  is-nonzero-length-nonempty-array ((succ-ℕ n , _) , _) ()

  nonzero-length-nonempty-array : nonempty-array A → ℕ⁺
  nonzero-length-nonempty-array a =
    ( length-nonempty-array a ,
      is-nonzero-length-nonempty-array a)

  fin-sequence-nonempty-array :
    (a : nonempty-array A) → fin-sequence A (length-nonempty-array a)
  fin-sequence-nonempty-array ((_ , u) , _) = u

  head-nonempty-array : nonempty-array A → A
  head-nonempty-array ((succ-ℕ n , u) , _) = u (neg-one-Fin n)

  tail-nonempty-array : nonempty-array A → array A
  tail-nonempty-array ((succ-ℕ n , u) , _) = (n , u ∘ inl-Fin n)

  last-nonempty-array : nonempty-array A → A
  last-nonempty-array ((succ-ℕ n , u) , _) = u (zero-Fin n)

  init-nonempty-array : nonempty-array A → array A
  init-nonempty-array ((succ-ℕ n , u) , _) = (n , u ∘ skip-zero-Fin n)
```
