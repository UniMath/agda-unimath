# Retractions

```agda
module foundation.retractions where

open import foundation-core.retractions public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.morphisms-coslice
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retracts-of-types
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### Characterizing the identity type of `retraction f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  coherence-htpy-retraction :
    (g h : retraction f) → map-retraction f g ~ map-retraction f h → UU l1
  coherence-htpy-retraction = coherence-htpy-hom-coslice

  htpy-retraction : retraction f → retraction f → UU (l1 ⊔ l2)
  htpy-retraction = htpy-hom-coslice

  extensionality-retraction :
    (g h : retraction f) → (g ＝ h) ≃ htpy-retraction g h
  extensionality-retraction = extensionality-hom-coslice

  eq-htpy-retraction :
    ( g h : retraction f)
    ( H : map-retraction f g ~ map-retraction f h)
    ( K :
      ( is-retraction-map-retraction f g) ~
      ( (H ·r f) ∙h is-retraction-map-retraction f h)) →
    g ＝ h
  eq-htpy-retraction = eq-htpy-hom-coslice
```

### If the left factor of a composite has a retraction, then the type of retractions of the right factor is a retract of the type of retractions of the composite

```agda
is-retraction-retraction-left-map-triangle :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B)
  (H : f ~ (g ∘ h)) (rg : retraction g) →
  ( ( retraction-top-map-triangle f g h H) ∘
    ( retraction-left-map-triangle f g h H rg)) ~ id
is-retraction-retraction-left-map-triangle f g h H (l , L) (k , K) =
  eq-htpy-retraction
    ( ( retraction-top-map-triangle f g h H
        ( retraction-left-map-triangle f g h H (l , L) (k , K))))
    ( k , K)
    ( k ·l L)
    ( homotopy-reasoning
      (((k ∘ l) ·l inv-htpy H) ∙h ((k ∘ l) ·l H ∙h (k ·l (L ·r h) ∙h K)))
      ~ (inv-htpy ((k ∘ l) ·l H) ∙h ((k ∘ l) ·l H ∙h (k ·l (L ·r h) ∙h K)))
      by
        ap-concat-htpy'
          ( (k ∘ l) ·l H ∙h (k ·l (L ·r h) ∙h K))
          ( left-whisker-inv-htpy (k ∘ l) H)
      ~ ((inv-htpy ((k ∘ l) ·l H) ∙h (k ∘ l) ·l H) ∙h (k ·l (L ·r h) ∙h K))
      by
      ( inv-htpy-assoc-htpy
        ( inv-htpy ((k ∘ l) ·l H))
        ( (k ∘ l) ·l H)
        ( (k ·l (L ·r h)) ∙h K))
      ~ (k ·l L ·r h ∙h is-retraction-map-retraction h (k , K))
      by
        ap-concat-htpy' ((k ·l (L ·r h)) ∙h K) (left-inv-htpy ((k ∘ l) ·l H)))

retraction-right-factor-retract-of-retraction-left-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h) →
  retraction g → (retraction h) retract-of (retraction f)
pr1 (retraction-right-factor-retract-of-retraction-left-factor f g h H rg) =
  retraction-left-map-triangle f g h H rg
pr1
  ( pr2
    ( retraction-right-factor-retract-of-retraction-left-factor f g h H rg)) =
  retraction-top-map-triangle f g h H
pr2
  ( pr2
    ( retraction-right-factor-retract-of-retraction-left-factor f g h H rg)) =
  is-retraction-retraction-left-map-triangle f g h H rg
```

### The type of retractions is `k`-truncated if the domain is `k`-truncated

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-trunc-retraction : is-trunc k A → is-trunc k (retraction f)
  is-trunc-retraction is-trunc-A =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-A)
      ( λ r →
        is-trunc-Π k (λ x → is-trunc-succ-is-trunc k is-trunc-A (r (f x)) x))
```

### When the domain is contractible, the type of retractions is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-contr-retraction : is-contr A → is-contr (retraction f)
  is-contr-retraction = is-trunc-retraction
```

### When the domain is a proposition, the type of retractions is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-prop-retraction : is-prop A → is-prop (retraction f)
  is-prop-retraction = is-trunc-retraction
```
