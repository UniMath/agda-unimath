# Maps of towers of types

```agda
module foundation.maps-of-towers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.towers-of-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A **map of towers** `A → B` is a commuting diagram of the form

```text
  ⋯ ----> Aₙ₊₁ ----> Aₙ ----> ⋯ ----> A₁ ----> A₀
  |        |         |       |       |        |
  ⋯        |         |       ⋯       |        |
  v        v         v       v       v        v
  ⋯ ----> Bₙ₊₁ ----> Bₙ ----> ⋯ ----> B₁ ----> B₀.
```

## Definitions

### Maps of towers

```agda
hom-Tower : {l1 l2 : Level} (A : Tower l1) (B : Tower l2) → UU (l1 ⊔ l2)
hom-Tower A B = section-Dependent-Tower A (const-Dependent-Tower A B)
```

### Identity map on towers

```agda
id-hom-Tower :
  {l : Level} (A : Tower l) → hom-Tower A A
pr1 (id-hom-Tower A) n = id
pr2 (id-hom-Tower A) n = refl-htpy
```
