# Cycle decompositions of a natural numbers

```agda
module univalent-combinatorics.cycle-decomposition-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.fundamental-theorem-of-arithmetic
open import elementary-number-theory.inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels
open import foundation.iterated-cartesian-product-types

open import univalent-combinatorics.cyclic-types
open import univalent-combinatorics.finite-types

open import lists.lists
open import lists.functoriality-lists

open import structured-types.types-equipped-with-endomorphisms
open import structured-types.mere-equivalences-types-equipped-with-endomorphisms
open import structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms
```

</details>

## Idea



## Definition

```agda
standard-cycle-decomposition :
  (n : ℕ) → 1 ≤-ℕ n → Endo lzero
standard-cycle-decomposition n p =
  iterated-product-Endo-list
    ( map-list ℤ-Mod-Endo (list-fundamental-theorem-arithmetic-ℕ n p))

is-cycle-decomposition-Endo :
  {l : Level} → (n : ℕ) → 1 ≤-ℕ n → Endo l → UU l
is-cycle-decomposition-Endo n p X =
  mere-equiv-Endo
    ( standard-cycle-decomposition n p)
    ( X)

Cycle-Decomposition : (l : Level) → (n : ℕ) → 1 ≤-ℕ n → UU (lsuc l)
Cycle-Decomposition l n p = Σ (Endo l) (is-cycle-decomposition-Endo n p)
```

