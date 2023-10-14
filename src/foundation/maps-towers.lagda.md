# Maps of towers of types

```agda
module foundation.maps-towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-towers
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.structure-identity-principle
open import foundation.towers
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies

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
  naturality-section-dependent-tower A (const-dependent-tower A B)

hom-tower : {l1 l2 : Level} (A : tower l1) (B : tower l2) → UU (l1 ⊔ l2)
hom-tower A B = section-dependent-tower A (const-dependent-tower A B)

module _
  {l1 l2 : Level} (A : tower l1) (B : tower l2)
  where

  map-hom-tower : hom-tower A B → (n : ℕ) → type-tower A n → type-tower B n
  map-hom-tower = map-section-dependent-tower (const-dependent-tower A B)

  naturality-map-hom-tower :
    (f : hom-tower A B) (n : ℕ) → naturality-hom-tower A B (map-hom-tower f) n
  naturality-map-hom-tower =
    naturality-map-section-dependent-tower (const-dependent-tower A B)
```

### Identity map on towers

```agda
id-hom-tower :
  {l : Level} (A : tower l) → hom-tower A A
pr1 (id-hom-tower A) n = id
pr2 (id-hom-tower A) n = refl-htpy

comp-hom-tower :
  {l : Level} (A B C : tower l) → hom-tower B C → hom-tower A B → hom-tower A C
pr1 (comp-hom-tower A B C g f) n = map-hom-tower B C g n ∘ map-hom-tower A B f n
pr2 (comp-hom-tower A B C g f) n x =
  ( ap (map-hom-tower B C g n) (naturality-map-hom-tower A B f n x)) ∙
  ( naturality-map-hom-tower B C g n (map-hom-tower A B f (succ-ℕ n) x))
```
