# Cones over towers

```agda
module foundation.cones-over-towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.towers
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A **cone** over a [tower](foundation.towers.md) `A` with domain `X` is a
[sequence](foundation.dependent-sequences.md) of functions from `X` into the
sequence of types of `A` such that the triangles

```text
     X
    / \
   /   \
  v     v
 Aₙ₊₁ -> Aₙ
```

[commute](foundation-core.commuting-triangles-of-maps.md) for all `n : ℕ`.

## Definitions

### Cones on towers

```agda
module _
  {l1 : Level} (A : Tower l1)
  where

  cone-Tower : {l2 : Level} → UU l2 → UU (l1 ⊔ l2)
  cone-Tower X =
    Σ ( (n : ℕ) → X → type-Tower A n)
      ( λ f →
        (n : ℕ) → coherence-triangle-maps (f n) (map-Tower A n) (f (succ-ℕ n)))

  map-cone-Tower :
    {l2 : Level} {X : UU l2} → cone-Tower X → (n : ℕ) → X → type-Tower A n
  map-cone-Tower = pr1

  coherence-cone-Tower :
    {l2 : Level} {X : UU l2} (c : cone-Tower X) (n : ℕ) →
    coherence-triangle-maps
      ( map-cone-Tower c n)
      ( map-Tower A n)
      ( map-cone-Tower c (succ-ℕ n))
  coherence-cone-Tower = pr2
```

### Identifications of cones over towers of types

```agda
module _
  {l1 l2 : Level} (A : Tower l1) {X : UU l2}
  where

  coherence-htpy-cone-Tower :
    (c c' : cone-Tower A X) →
    ((n : ℕ) → map-cone-Tower A c n ~ map-cone-Tower A c' n) → UU (l1 ⊔ l2)
  coherence-htpy-cone-Tower c c' H =
    (n : ℕ) →
    ( coherence-cone-Tower A c n ∙h (map-Tower A n ·l H (succ-ℕ n))) ~
    ( H n ∙h coherence-cone-Tower A c' n)

  htpy-cone-Tower : cone-Tower A X → cone-Tower A X → UU (l1 ⊔ l2)
  htpy-cone-Tower c c' =
    Σ ( (n : ℕ) → map-cone-Tower A c n ~ map-cone-Tower A c' n)
      ( coherence-htpy-cone-Tower c c')

  refl-htpy-cone-Tower : (c : cone-Tower A X) → htpy-cone-Tower c c
  pr1 (refl-htpy-cone-Tower c) n = refl-htpy
  pr2 (refl-htpy-cone-Tower c) n = right-unit-htpy

  htpy-eq-cone-Tower : (c c' : cone-Tower A X) → c ＝ c' → htpy-cone-Tower c c'
  htpy-eq-cone-Tower c .c refl = refl-htpy-cone-Tower c

  is-contr-total-htpy-cone-Tower :
    (c : cone-Tower A X) → is-contr (Σ (cone-Tower A X) (htpy-cone-Tower c))
  is-contr-total-htpy-cone-Tower c =
    is-contr-total-Eq-structure
      ( λ x z → coherence-htpy-cone-Tower c (x , z))
      ( is-contr-total-binary-htpy (map-cone-Tower A c))
      ( map-cone-Tower A c , (λ n → refl-htpy))
      ( is-contr-total-Eq-Π
        ( λ n → (coherence-cone-Tower A c n ∙h refl-htpy) ~_)
        ( λ n → is-contr-total-htpy (coherence-cone-Tower A c n ∙h refl-htpy)))

  is-equiv-htpy-eq-cone-Tower :
    (c c' : cone-Tower A X) → is-equiv (htpy-eq-cone-Tower c c')
  is-equiv-htpy-eq-cone-Tower c =
    fundamental-theorem-id
      ( is-contr-total-htpy-cone-Tower c)
      ( htpy-eq-cone-Tower c)

  extensionality-cone-Tower :
    (c c' : cone-Tower A X) → (c ＝ c') ≃ htpy-cone-Tower c c'
  pr1 (extensionality-cone-Tower c c') = htpy-eq-cone-Tower c c'
  pr2 (extensionality-cone-Tower c c') = is-equiv-htpy-eq-cone-Tower c c'

  eq-htpy-cone-Tower : (c c' : cone-Tower A X) → htpy-cone-Tower c c' → c ＝ c'
  eq-htpy-cone-Tower c c' = map-inv-equiv (extensionality-cone-Tower c c')
```

### Precomposition cones on towers

```agda
module _
  {l1 l2 l3 : Level} (A : Tower l1) {X : UU l2} {Y : UU l3}
  where

  cone-map-Tower : cone-Tower A X → (Y → X) → cone-Tower A Y
  pr1 (cone-map-Tower c f) n x = map-cone-Tower A c n (f x)
  pr2 (cone-map-Tower c f) n x = coherence-cone-Tower A c n (f x)
```
