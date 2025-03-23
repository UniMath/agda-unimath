# Projective types

```agda
module foundation.projective-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.connected-maps
open import foundation.postcomposition-functions
open import foundation.surjective-maps
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.sets
open import foundation-core.truncated-types
```

</details>

## Idea

A type `X` is said to be **set-projective** if for every surjective map
`f : A → B` into a set `B` the postcomposition function

```text
  (X → A) → (X → B)
```

is surjective. This is equivalent to the condition that for every equivalence
relation `R` on a type `A` the natural map

```text
  (X → A)/~ → (X → A/R)
```

is an equivalence. The latter map is always an embedding, and it is an
equivalence for every `X`, `A`, and `R` if and only if the axiom of choice
holds.

The notion of set-projectiveness generalizes to `n`-projectiveness, for `n : ℕ`.
A type `X` is said to be `k`-projective if the postcomposition function
`(X → A) → (X → B)` is surjective for every `k-1`-connected map `f : A → B` into
a `k`-truncated type `B`.

## Definitions

### Set-projective types

```agda
is-set-projective :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
is-set-projective l2 l3 X =
  (A : UU l2) (B : Set l3) (f : A ↠ type-Set B) →
  is-surjective (postcomp X (map-surjection f))
```

### `k`-projective types

```agda
is-projective :
  {l1 : Level} (l2 l3 : Level) (k : ℕ) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
is-projective l2 l3 k X =
  ( A : UU l2) (B : Truncated-Type l3 (truncation-level-ℕ k))
  ( f :
    connected-map
      ( truncation-level-minus-one-ℕ k)
      ( A)
      ( type-Truncated-Type B)) →
  is-surjective (postcomp X (map-connected-map f))
```

## See also

- The natural map `(X → A)/~ → (X → A/R)` is studied in
  [`foundation.exponents-set-quotients`](foundation.exponents-set-quotients.md)
