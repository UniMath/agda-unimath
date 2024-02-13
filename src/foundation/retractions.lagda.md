# Retractions

```agda
module foundation.retractions where

open import foundation-core.retractions public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coslice
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.multivariable-homotopies
open import foundation.retracts-of-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
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
    ( ( inv-htpy-assoc-htpy
        ( inv-htpy ((k ∘ l) ·l H))
        ( (k ∘ l) ·l H)
        ( (k ·l (L ·r h)) ∙h K)) ∙h
      ( ap-concat-htpy' ((k ·l (L ·r h)) ∙h K) (left-inv-htpy ((k ∘ l) ·l H))))

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

### If `f` has a retraction, then `f` is injective

```agda
abstract
  is-injective-retraction :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    retraction f → is-injective f
  is-injective-retraction f (h , H) {x} {y} p = inv (H x) ∙ (ap h p ∙ H y)
```

### Transposing identifications along retractions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  transpose-eq-is-retraction :
    g ∘ f ~ id → {x : B} {y : A} → x ＝ f y → g x ＝ y
  transpose-eq-is-retraction H {x} {y} p = ap g p ∙ H y

  transpose-eq-is-retraction' :
    g ∘ f ~ id → {x : A} {y : B} → f x ＝ y → x ＝ g y
  transpose-eq-is-retraction' H {x} refl = inv (H x)

  is-retraction-transpose-eq :
    ({x : B} {y : A} → x ＝ f y → g x ＝ y) → g ∘ f ~ id
  is-retraction-transpose-eq H x = H refl

  is-retraction-transpose-eq' :
    ({x : A} {y : B} → f x ＝ y → x ＝ g y) → g ∘ f ~ id
  is-retraction-transpose-eq' H x = inv (H refl)

  is-retraction-is-retraction-transpose-eq :
    is-retraction-transpose-eq ∘ transpose-eq-is-retraction ~ id
  is-retraction-is-retraction-transpose-eq H = refl

  abstract
    is-section-is-retraction-transpose-eq :
      transpose-eq-is-retraction ∘ is-retraction-transpose-eq ~ id
    is-section-is-retraction-transpose-eq H =
      eq-multivariable-htpy-implicit 2 (λ x y → eq-htpy (λ where refl → refl))

  is-equiv-transpose-eq-is-retraction :
    is-equiv transpose-eq-is-retraction
  is-equiv-transpose-eq-is-retraction =
    is-equiv-is-invertible
      ( is-retraction-transpose-eq)
      ( is-section-is-retraction-transpose-eq)
      ( is-retraction-is-retraction-transpose-eq)

  equiv-transpose-eq-is-retraction :
    (g ∘ f ~ id) ≃ ({x : B} {y : A} → x ＝ f y → g x ＝ y)
  equiv-transpose-eq-is-retraction =
    (transpose-eq-is-retraction , is-equiv-transpose-eq-is-retraction)
```
