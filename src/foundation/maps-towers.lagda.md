# Maps of towers of types

```agda
module foundation.maps-towers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.towers
open import foundation.universe-levels
open import foundation.equivalences
open import foundation.identity-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.iterating-functions
open import foundation.unit-type
open import foundation.identity-types
open import foundation.contractible-types
open import foundation.structure-identity-principle
open import foundation.equality-dependent-function-types
open import foundation.univalence
open import foundation.homotopy-induction
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels
open import foundation.equivalences

open import foundation-core.function-types
open import foundation-core.homotopies
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
naturality-hom-tower :
  {l1 l2 : Level} (A : tower l1) (B : tower l2)
  (h : (n : ℕ) → type-tower A n → type-tower B n) (n : ℕ) → UU (l1 ⊔ l2)
naturality-hom-tower A B =
  naturality-section-Dependent-tower A (const-Dependent-tower A B)

hom-tower : {l1 l2 : Level} (A : tower l1) (B : tower l2) → UU (l1 ⊔ l2)
hom-tower A B = section-Dependent-tower A (const-Dependent-tower A B)
```

### Identity map on towers

```agda
id-hom-tower :
  {l : Level} (A : tower l) → hom-tower A A
pr1 (id-hom-tower A) n = id
pr2 (id-hom-tower A) n = refl-htpy

-- comp-hom-tower :
--   {l : Level} (A B C : tower l) → hom-tower B C → hom-tower A B → hom-tower A C
-- pr1 (comp-hom-tower A B C g f) = {! map  !}
-- pr2 (comp-hom-tower A B C g f) = {!   !}
```
