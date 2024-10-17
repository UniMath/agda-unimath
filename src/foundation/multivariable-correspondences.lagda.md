# Multivariable correspondences

```agda
module foundation.multivariable-correspondences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Consider a family of types `A` indexed by `Fin n`. An `n`-ary correspondence of
tuples `(x₁, …, xₙ)` where `xᵢ : A i` is a type family over `(i : Fin n) → A i`.

## Definition

```agda
multivariable-correspondence :
  {l1 : Level} (l2 : Level) (n : ℕ) (A : Fin n → UU l1) → UU (l1 ⊔ lsuc l2)
multivariable-correspondence l2 n A = ((i : Fin n) → A i) → UU l2
```
