# The minimum of finite families of real numbers

```agda
module real-numbers.minimum-finite-families-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.function-types
open import foundation.universe-levels

open import lists.finite-sequences

open import order-theory.greatest-lower-bounds-large-posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.infima-families-real-numbers
open import real-numbers.maximum-finite-families-real-numbers
open import real-numbers.negation-real-numbers

open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Idea

The
{{#concept "minimum" Disambiguation="inhabited finite family, Dedekind real numbers" Agda=min-finite-family-ℝ WD="minimum" WDID=Q10578722}}
of a family of [Dedekind real numbers](real-numbers.dedekind-real-numbers.md)
indexed by an
[inhabited finite type](univalent-combinatorics.inhabited-finite-types.md) is
their
[greatest lower bound](order-theory.greatest-lower-bounds-large-posets.md).

## Definition

### The minimum of a nonempty finite sequence of real numbers

```agda
module _
  {l : Level} (n : ℕ) (x : fin-sequence (ℝ l) (succ-ℕ n))
  where

  opaque
    min-fin-sequence-ℝ : ℝ l
    min-fin-sequence-ℝ = neg-ℝ (max-fin-sequence-ℝ n (neg-ℝ ∘ x))
```

### The minimum of an inhabited finite family of real numbers

```agda
module _
  {l1 l2 : Level} (I : Inhabited-Finite-Type l1)
  (f : type-Inhabited-Finite-Type I → ℝ l2)
  where

  opaque
    min-finite-family-ℝ : ℝ l2
    min-finite-family-ℝ = neg-ℝ (max-finite-family-ℝ I (neg-ℝ ∘ f))
```

## Properties

### The minimum of a finite sequence is its infimum

```agda
opaque
  unfolding min-fin-sequence-ℝ

  is-infimum-min-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (x : fin-sequence (ℝ l) (succ-ℕ n)) →
    is-infimum-family-ℝ x (min-fin-sequence-ℝ n x)
  is-infimum-min-fin-sequence-ℝ n x =
    is-infimum-neg-supremum-neg-family-ℝ
      ( x)
      ( max-fin-sequence-ℝ n (neg-ℝ ∘ x))
      ( is-supremum-max-fin-sequence-ℝ n (neg-ℝ ∘ x))
```

### The minimum of a finite family is its infimum

```agda
module _
  {l1 l2 : Level} (I : Inhabited-Finite-Type l1)
  (x : type-Inhabited-Finite-Type I → ℝ l2)
  where

  opaque
    unfolding min-finite-family-ℝ

    is-infimum-min-finite-family-ℝ :
      is-infimum-family-ℝ x (min-finite-family-ℝ I x)
    is-infimum-min-finite-family-ℝ =
      is-infimum-neg-supremum-neg-family-ℝ
        ( x)
        ( max-finite-family-ℝ I (neg-ℝ ∘ x))
        ( is-supremum-max-finite-family-ℝ I (neg-ℝ ∘ x))
```

### The minimum of a finite family is its greatest lower bound

```agda
module _
  {l1 l2 : Level} (I : Inhabited-Finite-Type l1)
  (x : type-Inhabited-Finite-Type I → ℝ l2)
  where

  abstract
    is-greatest-lower-bound-min-finite-family-ℝ :
      is-greatest-lower-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( x)
        ( min-finite-family-ℝ I x)
    is-greatest-lower-bound-min-finite-family-ℝ =
      is-greatest-lower-bound-is-infimum-family-ℝ
        ( x)
        ( min-finite-family-ℝ I x)
        ( is-infimum-min-finite-family-ℝ I x)
```
