# Sequential limits

```agda
module foundation.sequential-limits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.cones-over-towers
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.maps-towers
open import foundation.structure-identity-principle
open import foundation.towers
open import foundation.universal-property-sequential-limits
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Definitions

### The standard sequential limit

```agda
module _
  {l : Level} (A : tower l)
  where

  standard-sequential-limit : UU l
  standard-sequential-limit =
    Σ ( (n : ℕ) → type-tower A n)
      ( λ a → (n : ℕ) → a n ＝ map-tower A n (a (succ-ℕ n)))

module _
  {l : Level} (A : tower l)
  where

  sequence-standard-sequential-limit :
    standard-sequential-limit A → (n : ℕ) → type-tower A n
  sequence-standard-sequential-limit = pr1

  coherence-standard-sequential-limit :
    (x : standard-sequential-limit A) (n : ℕ) →
    sequence-standard-sequential-limit x n ＝
    map-tower A n (sequence-standard-sequential-limit x (succ-ℕ n))
  coherence-standard-sequential-limit = pr2
```

### The cone at the standard sequential limit

```agda
module _
  {l : Level} (A : tower l)
  where

  cone-standard-sequential-limit : cone-tower A (standard-sequential-limit A)
  pr1 cone-standard-sequential-limit n x =
    sequence-standard-sequential-limit A x n
  pr2 cone-standard-sequential-limit n x =
    coherence-standard-sequential-limit A x n
```

### The gap map into the standard sequential limit

The **gap map** of a [cone over a tower](foundation.cones-over-towers.md) is the
map from the domain of the cone into the standard limit of the tower.

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  gap-tower : cone-tower A X → X → standard-sequential-limit A
  pr1 (gap-tower c x) n = map-cone-tower A c n x
  pr2 (gap-tower c x) n = coherence-cone-tower A c n x
```

### The `is-sequential-limit` property

The [proposition](foundation-core.propositions.md) `is-sequential-limit` is the
assertion that the gap map is an [equivalence](foundation-core.equivalences.md).
Note that this proposition is [small](foundation-core.small-types.md), whereas
[the universal property](foundation.universal-property-sequential-limits.md) is
a large proposition.

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  is-sequential-limit : cone-tower A X → UU (l1 ⊔ l2)
  is-sequential-limit c = is-equiv (gap-tower A c)

  is-property-is-sequential-limit :
    (c : cone-tower A X) → is-prop (is-sequential-limit c)
  is-property-is-sequential-limit c = is-property-is-equiv (gap-tower A c)

  is-sequential-limit-Prop : (c : cone-tower A X) → Prop (l1 ⊔ l2)
  pr1 (is-sequential-limit-Prop c) = is-sequential-limit c
  pr2 (is-sequential-limit-Prop c) = is-property-is-sequential-limit c
```

### Functoriality of standard limits of towers

```agda
module _
  {l1 l2 : Level} {A : tower l1} {A' : tower l2}
  where

  map-hom-standard-sequential-limit :
    hom-tower A' A → standard-sequential-limit A' → standard-sequential-limit A
  pr1 (map-hom-standard-sequential-limit (f , F) (x , H)) n = f n (x n)
  pr2 (map-hom-standard-sequential-limit (f , F) (x , H)) n =
    ap (f n) (H n) ∙ F n (x (succ-ℕ n))

  map-hom-is-sequential-limit :
    {l4 l4' : Level} {C : UU l4} {C' : UU l4'} →
    (c : cone-tower A C) (c' : cone-tower A' C') →
    is-sequential-limit A c → is-sequential-limit A' c' →
    hom-tower A' A → C' → C
  map-hom-is-sequential-limit c c' is-lim-c is-lim-c' h x =
    map-inv-is-equiv
      ( is-lim-c)
      ( map-hom-standard-sequential-limit h (gap-tower A' c' x))
```

## Properties

### Characterization of the identity type of the standard sequential limit

```agda
module _
  {l : Level} (A : tower l)
  where

  Eq-standard-sequential-limit : (s t : standard-sequential-limit A) → UU l
  Eq-standard-sequential-limit s t =
    Σ ( sequence-standard-sequential-limit A s ~ sequence-standard-sequential-limit A t)
      ( λ H →
        coherence-square-homotopies
          ( coherence-standard-sequential-limit A s)
          ( λ n → ap (map-tower A n) (H (succ-ℕ n)))
          ( H)
          ( coherence-standard-sequential-limit A t))

  refl-Eq-standard-sequential-limit :
    (s : standard-sequential-limit A) → Eq-standard-sequential-limit s s
  pr1 (refl-Eq-standard-sequential-limit s) = refl-htpy
  pr2 (refl-Eq-standard-sequential-limit s) = right-unit-htpy

  Eq-eq-standard-sequential-limit :
    (s t : standard-sequential-limit A) → s ＝ t → Eq-standard-sequential-limit s t
  Eq-eq-standard-sequential-limit s .s refl =
    refl-Eq-standard-sequential-limit s

  is-contr-total-Eq-standard-sequential-limit :
    (s : standard-sequential-limit A) →
    is-contr (Σ (standard-sequential-limit A) (Eq-standard-sequential-limit s))
  is-contr-total-Eq-standard-sequential-limit s =
    is-contr-total-Eq-structure _
      ( is-contr-total-htpy (pr1 s))
      ( pr1 s , refl-htpy)
      ( is-contr-total-Eq-Π _ (λ n → is-contr-total-path (pr2 s n ∙ refl)))

  is-equiv-Eq-eq-standard-sequential-limit :
    (s t : standard-sequential-limit A) → is-equiv (Eq-eq-standard-sequential-limit s t)
  is-equiv-Eq-eq-standard-sequential-limit s =
    fundamental-theorem-id
      ( is-contr-total-Eq-standard-sequential-limit s)
      ( Eq-eq-standard-sequential-limit s)

  extensionality-standard-sequential-limit :
    (s t : standard-sequential-limit A) → (s ＝ t) ≃ Eq-standard-sequential-limit s t
  pr1 (extensionality-standard-sequential-limit s t) =
    Eq-eq-standard-sequential-limit s t
  pr2 (extensionality-standard-sequential-limit s t) =
    is-equiv-Eq-eq-standard-sequential-limit s t

  eq-Eq-standard-sequential-limit :
    (s t : standard-sequential-limit A) → Eq-standard-sequential-limit s t → s ＝ t
  eq-Eq-standard-sequential-limit s t =
    map-inv-equiv (extensionality-standard-sequential-limit s t)
```

### The standard sequential limit satisfies the universal property of a sequential limit

```agda
module _
  {l1 : Level} (A : tower l1)
  where

  cone-map-standard-sequential-limit :
    {l : Level} {Y : UU l} → (Y → standard-sequential-limit A) → cone-tower A Y
  cone-map-standard-sequential-limit {Y = Y} =
    cone-map-tower A {Y = Y} (cone-standard-sequential-limit A)

  is-retraction-gap-tower :
    {l : Level} {Y : UU l} →
    gap-tower A ∘ cone-map-standard-sequential-limit {Y = Y} ~ id
  is-retraction-gap-tower x = refl

  is-section-gap-tower :
    {l : Level} {Y : UU l} →
    cone-map-standard-sequential-limit {Y = Y} ∘ gap-tower A ~ id
  is-section-gap-tower x = refl

  universal-property-standard-sequential-limit :
    {l : Level} →
    universal-property-sequential-limit l A (cone-standard-sequential-limit A)
  pr1 (pr1 (universal-property-standard-sequential-limit X)) = gap-tower A
  pr2 (pr1 (universal-property-standard-sequential-limit X)) =
    is-section-gap-tower
  pr1 (pr2 (universal-property-standard-sequential-limit X)) = gap-tower A
  pr2 (pr2 (universal-property-standard-sequential-limit X)) =
    is-retraction-gap-tower
```

### A cone is equal to the value of cone-map at its own gap map

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  htpy-cone-up-pullback-standard-sequential-limit :
    (c : cone-tower A X) →
    htpy-cone-tower A
      ( cone-map-tower A (cone-standard-sequential-limit A) (gap-tower A c))
      ( c)
  pr1 (htpy-cone-up-pullback-standard-sequential-limit c) n = refl-htpy
  pr2 (htpy-cone-up-pullback-standard-sequential-limit c) n = right-unit-htpy
```

### A cone satisfies the universal property of the limit if and only if the gap map is an equivalence

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  is-sequential-limit-universal-property-sequential-limit :
    (c : cone-tower A X) →
    ({l : Level} → universal-property-sequential-limit l A c) → is-sequential-limit A c
  is-sequential-limit-universal-property-sequential-limit c =
    is-equiv-universal-property-sequential-limit-universal-property-sequential-limit
      ( cone-standard-sequential-limit A)
      ( c)
      ( gap-tower A c)
      ( htpy-cone-up-pullback-standard-sequential-limit A c)
      ( universal-property-standard-sequential-limit A)

  universal-property-is-sequential-limit :
    (c : cone-tower A X) → is-sequential-limit A c →
    {l : Level} → universal-property-sequential-limit l A c
  universal-property-is-sequential-limit c is-lim-c =
    universal-property-sequential-limit-universal-property-sequential-limit-is-equiv
      ( cone-standard-sequential-limit A)
      ( c)
      ( gap-tower A c)
      ( htpy-cone-up-pullback-standard-sequential-limit A c)
      ( is-lim-c)
      ( universal-property-standard-sequential-limit A)
```
