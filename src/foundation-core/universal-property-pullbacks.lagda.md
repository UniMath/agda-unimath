# The universal property of pullbacks

```agda
module foundation-core.universal-property-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Definition

### The universal property of pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} (l : Level) {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4}
  where

  universal-property-pullback :
    (c : cone f g C) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  universal-property-pullback c =
    (C' : UU l) → is-equiv (cone-map f g {C' = C'} c)
```

## Properties

### 3-for-2 property of pullbacks

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4} {C' : UU l5}
  {f : A → X} {g : B → X} (c : cone f g C) (c' : cone f g C')
  (h : C' → C) (KLM : htpy-cone f g (cone-map f g c h) c')
  where

  triangle-cone-cone :
    {l6 : Level} (D : UU l6) →
    (cone-map f g {C' = D} c') ~ ((cone-map f g c) ∘ (λ (k : D → C') → h ∘ k))
  triangle-cone-cone D k =
    inv
      ( ap
        ( λ t → cone-map f g {C' = D} t k)
        { x = (cone-map f g c h)}
        { y = c'}
        ( eq-htpy-cone f g (cone-map f g c h) c' KLM))

  abstract
    is-equiv-up-pullback-up-pullback :
      ({l : Level} → universal-property-pullback l f g c) →
      ({l : Level} → universal-property-pullback l f g c') →
      is-equiv h
    is-equiv-up-pullback-up-pullback up up' =
      is-equiv-is-equiv-postcomp h
        ( λ D → is-equiv-right-factor-htpy
          ( cone-map f g {C' = D} c')
          ( cone-map f g c)
          ( λ (k : D → C') → h ∘ k)
          ( triangle-cone-cone D)
          ( up D)
          ( up' D))

  abstract
    up-pullback-up-pullback-is-equiv :
      is-equiv h →
      ({l : Level} → universal-property-pullback l f g c) →
      ({l : Level} → universal-property-pullback l f g c')
    up-pullback-up-pullback-is-equiv is-equiv-h up D =
      is-equiv-comp-htpy
        ( cone-map f g c')
        ( cone-map f g c)
        ( λ k → h ∘ k)
        ( triangle-cone-cone D)
        ( is-equiv-postcomp-is-equiv h is-equiv-h D)
        ( up D)

  abstract
    up-pullback-is-equiv-up-pullback :
      ({l : Level} → universal-property-pullback l f g c') →
      is-equiv h →
      ({l : Level} → universal-property-pullback l f g c)
    up-pullback-is-equiv-up-pullback up' is-equiv-h D =
      is-equiv-left-factor-htpy
        ( cone-map f g c')
        ( cone-map f g c)
        ( λ k → h ∘ k)
        ( triangle-cone-cone D)
        ( up' D)
        ( is-equiv-postcomp-is-equiv h is-equiv-h D)
```

### Uniqueness of maps obtained via the universal property of pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C)
  where

  abstract
    uniqueness-universal-property-pullback :
      ({l : Level} → universal-property-pullback l f g c) →
      {l5 : Level} (C' : UU l5) (c' : cone f g C') →
      is-contr (Σ (C' → C) (λ h → htpy-cone f g (cone-map f g c h) c'))
    uniqueness-universal-property-pullback up C' c' =
      is-contr-equiv'
        ( Σ (C' → C) (λ h → cone-map f g c h ＝ c'))
        ( equiv-tot
          ( λ h → extensionality-cone f g (cone-map f g c h) c'))
        ( is-contr-map-is-equiv (up C') c')
```
