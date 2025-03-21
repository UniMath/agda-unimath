# Bracelets

```agda
module univalent-combinatorics.bracelets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.polygons

open import univalent-combinatorics.standard-finite-types
```

</details>

## Definition

### Bracelets

```agda
bracelet : ℕ → ℕ → UU (lsuc lzero)
bracelet m n = Σ (Polygon m) (λ X → vertex-Polygon m X → Fin n)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
