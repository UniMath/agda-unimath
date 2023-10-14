# Limits of towers of types

```agda
module foundation.limits-towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.commuting-squares-of-homotopies
open import foundation.cones-over-towers
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-fibers-of-maps
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.maps-of-towers
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.towers-of-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-limits-of-towers
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
```

</details>

## Definitions

### The standard limit of a tower

```agda
module _
  {l : Level} (A : Tower l)
  where

  standard-limit-Tower : UU l
  standard-limit-Tower =
    Σ ( (n : ℕ) → type-Tower A n)
      ( λ a → (n : ℕ) → a n ＝ map-Tower A n (a (succ-ℕ n)))

module _
  {l : Level} (A : Tower l)
  where

  sequence-standard-limit-Tower :
    standard-limit-Tower A → (n : ℕ) → type-Tower A n
  sequence-standard-limit-Tower = pr1

  coherence-standard-limit-Tower :
    (x : standard-limit-Tower A) (n : ℕ) →
    sequence-standard-limit-Tower x n ＝
    map-Tower A n (sequence-standard-limit-Tower x (succ-ℕ n))
  coherence-standard-limit-Tower = pr2
```

### The cone at the standard limit of a tower

```agda
module _
  {l : Level} (A : Tower l)
  where

  cone-standard-limit-Tower : cone-Tower A (standard-limit-Tower A)
  pr1 cone-standard-limit-Tower n x = sequence-standard-limit-Tower A x n
  pr2 cone-standard-limit-Tower n x = coherence-standard-limit-Tower A x n
```

### The gap map into the standard limit of a tower

The **gap map** of a [cone over a tower](foundation.cones-over-towers.md) is the
map from the domain of the cone into the standard limit of the tower.

```agda
module _
  {l1 l2 : Level} (A : Tower l1) {X : UU l2}
  where

  gap-Tower : cone-Tower A X → X → standard-limit-Tower A
  pr1 (gap-Tower c x) n = map-cone-Tower A c n x
  pr2 (gap-Tower c x) n = coherence-cone-Tower A c n x
```

### The `is-limit-Tower` property

The [proposition](foundation-core.propositions.md) `is-limit-Tower` is the
assertion that the gap map is an [equivalence](foundation-core.equivalences.md).
Note that this proposition is [small](foundation-core.small-types.md), whereas
[the universal property](foundation-core.universal-property-limits-of-towers.md)
is a large proposition.

```agda
module _
  {l1 l2 : Level} (A : Tower l1) {X : UU l2}
  where

  is-limit-Tower : cone-Tower A X → UU (l1 ⊔ l2)
  is-limit-Tower c = is-equiv (gap-Tower A c)

  is-property-is-limit-Tower : (c : cone-Tower A X) → is-prop (is-limit-Tower c)
  is-property-is-limit-Tower c = is-property-is-equiv (gap-Tower A c)

  is-limit-prop-Tower : (c : cone-Tower A X) → Prop (l1 ⊔ l2)
  pr1 (is-limit-prop-Tower c) = is-limit-Tower c
  pr2 (is-limit-prop-Tower c) = is-property-is-limit-Tower c
```

### Functoriality of standard limits of towers

```agda
module _
  {l1 l2 : Level} {A : Tower l1} {A' : Tower l2}
  where

  map-hom-standard-limit-Tower :
    hom-Tower A' A → standard-limit-Tower A' → standard-limit-Tower A
  pr1 (map-hom-standard-limit-Tower (f , F) (x , H)) n = f n (x n)
  pr2 (map-hom-standard-limit-Tower (f , F) (x , H)) n =
    ap (f n) (H n) ∙ F n (x (succ-ℕ n))

  map-hom-is-limit-Tower :
    {l4 l4' : Level} {C : UU l4} {C' : UU l4'} →
    (c : cone-Tower A C) (c' : cone-Tower A' C') →
    is-limit-Tower A c → is-limit-Tower A' c' →
    hom-Tower A' A → C' → C
  map-hom-is-limit-Tower c c' is-lim-c is-lim-c' h x =
    map-inv-is-equiv
      ( is-lim-c)
      ( map-hom-standard-limit-Tower h (gap-Tower A' c' x))
```

## Properties

### Characterization of the identity type of the standard limit of a tower

```agda
module _
  {l : Level} (A : Tower l)
  where

  Eq-standard-limit-Tower : (s t : standard-limit-Tower A) → UU l
  Eq-standard-limit-Tower s t =
    Σ ( sequence-standard-limit-Tower A s ~ sequence-standard-limit-Tower A t)
      ( λ H →
        coherence-square-homotopies
          ( coherence-standard-limit-Tower A s)
          ( λ n → ap (map-Tower A n) (H (succ-ℕ n)))
          ( H)
          ( coherence-standard-limit-Tower A t))

  refl-Eq-standard-limit-Tower :
    (s : standard-limit-Tower A) → Eq-standard-limit-Tower s s
  pr1 (refl-Eq-standard-limit-Tower s) = refl-htpy
  pr2 (refl-Eq-standard-limit-Tower s) = right-unit-htpy

  Eq-eq-standard-limit-Tower :
    (s t : standard-limit-Tower A) → s ＝ t → Eq-standard-limit-Tower s t
  Eq-eq-standard-limit-Tower s .s refl = refl-Eq-standard-limit-Tower s

  is-contr-total-Eq-standard-limit-Tower :
    (s : standard-limit-Tower A) →
    is-contr (Σ (standard-limit-Tower A) (Eq-standard-limit-Tower s))
  is-contr-total-Eq-standard-limit-Tower s =
    is-contr-total-Eq-structure _
      ( is-contr-total-htpy (pr1 s))
      ( pr1 s , refl-htpy)
      ( is-contr-total-Eq-Π _ (λ n → is-contr-total-path (pr2 s n ∙ refl)))

  is-equiv-Eq-eq-standard-limit-Tower :
    (s t : standard-limit-Tower A) → is-equiv (Eq-eq-standard-limit-Tower s t)
  is-equiv-Eq-eq-standard-limit-Tower s =
    fundamental-theorem-id
      ( is-contr-total-Eq-standard-limit-Tower s)
      ( Eq-eq-standard-limit-Tower s)

  extensionality-standard-limit-Tower :
    (s t : standard-limit-Tower A) → (s ＝ t) ≃ Eq-standard-limit-Tower s t
  pr1 (extensionality-standard-limit-Tower s t) =
    Eq-eq-standard-limit-Tower s t
  pr2 (extensionality-standard-limit-Tower s t) =
    is-equiv-Eq-eq-standard-limit-Tower s t

  eq-Eq-standard-limit-Tower :
    (s t : standard-limit-Tower A) → Eq-standard-limit-Tower s t → s ＝ t
  eq-Eq-standard-limit-Tower s t =
    map-inv-equiv (extensionality-standard-limit-Tower s t)
```

### The standard limit of a tower satisfies the universal property of a limit of a tower

```agda
module _
  {l1 : Level} (A : Tower l1)
  where

  cone-map-standard-limit-Tower :
    {l : Level} {Y : UU l} → (Y → standard-limit-Tower A) → cone-Tower A Y
  cone-map-standard-limit-Tower {Y = Y} =
    cone-map-Tower A {Y = Y} (cone-standard-limit-Tower A)

  is-retraction-gap-Tower :
    {l : Level} {Y : UU l} →
    gap-Tower A ∘ cone-map-standard-limit-Tower {Y = Y} ~ id
  is-retraction-gap-Tower x = refl

  is-section-gap-Tower :
    {l : Level} {Y : UU l} →
    cone-map-standard-limit-Tower {Y = Y} ∘ gap-Tower A ~ id
  is-section-gap-Tower x = refl

  universal-property-standard-limit-Tower :
    {l : Level} →
    universal-property-limit-Tower l A (cone-standard-limit-Tower A)
  pr1 (pr1 (universal-property-standard-limit-Tower X)) = gap-Tower A
  pr2 (pr1 (universal-property-standard-limit-Tower X)) = is-section-gap-Tower
  pr1 (pr2 (universal-property-standard-limit-Tower X)) = gap-Tower A
  pr2 (pr2 (universal-property-standard-limit-Tower X)) =
    is-retraction-gap-Tower
```

### A cone is equal to the value of cone-map at its own gap map

```agda
module _
  {l1 l2 : Level} (A : Tower l1) {X : UU l2}
  where

  htpy-cone-up-pullback-standard-limit-Tower :
    (c : cone-Tower A X) →
    htpy-cone-Tower A
      ( cone-map-Tower A (cone-standard-limit-Tower A) (gap-Tower A c))
      ( c)
  pr1 (htpy-cone-up-pullback-standard-limit-Tower c) n = refl-htpy
  pr2 (htpy-cone-up-pullback-standard-limit-Tower c) n = right-unit-htpy
```

### A cone satisfies the universal property of the limit if and only if the gap map is an equivalence

```agda
module _
  {l1 l2 : Level} (A : Tower l1) {X : UU l2}
  where

  is-limit-universal-property-limit-Tower :
    (c : cone-Tower A X) →
    ({l : Level} → universal-property-limit-Tower l A c) → is-limit-Tower A c
  is-limit-universal-property-limit-Tower c =
    is-equiv-up-limit-up-limit-Tower
      ( cone-standard-limit-Tower A)
      ( c)
      ( gap-Tower A c)
      ( htpy-cone-up-pullback-standard-limit-Tower A c)
      ( universal-property-standard-limit-Tower A)

  universal-property-is-limit-Tower :
    (c : cone-Tower A X) → is-limit-Tower A c →
    {l : Level} → universal-property-limit-Tower l A c
  universal-property-is-limit-Tower c is-lim-c =
    up-limit-up-limit-is-equiv-Tower
      ( cone-standard-limit-Tower A)
      ( c)
      ( gap-Tower A c)
      ( htpy-cone-up-pullback-standard-limit-Tower A c)
      ( is-lim-c)
      ( universal-property-standard-limit-Tower A)
```
