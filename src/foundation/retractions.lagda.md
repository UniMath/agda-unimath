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
open import foundation.universe-levels

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

  htpy-retraction : retraction f → retraction f → UU (l1 ⊔ l2)
  htpy-retraction = htpy-hom-coslice

  extensionality-retraction :
    (g h : retraction f) → Id g h ≃ htpy-retraction g h
  extensionality-retraction g h = extensionality-hom-coslice g h

  eq-htpy-retraction :
    ( g h : retraction f) (H : pr1 g ~ pr1 h)
    ( K : (pr2 g) ~ ((H ·r f) ∙h pr2 h)) →
    g ＝ h
  eq-htpy-retraction g h = eq-htpy-hom-coslice g h
```

### If the left factor of a composite has a retraction, then the type of retractions of the right factor is a retract of the type of retractions of the composite

```agda
is-retraction-retraction-comp-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B)
  (H : f ~ (g ∘ h)) (rg : retraction g) →
  ( ( retraction-right-factor-htpy f g h H) ∘
    ( retraction-comp-htpy f g h H rg)) ~ id
is-retraction-retraction-comp-htpy f g h H (l , L) (k , K) =
  eq-htpy-retraction
    ( ( retraction-right-factor-htpy f g h H
        ( retraction-comp-htpy f g h H (l , L) (k , K)
          )))
    ( k , K)
    ( k ·l L)
    ( ( inv-htpy-assoc-htpy
        ( inv-htpy ((k ∘ l) ·l H))
        ( (k ∘ l) ·l H)
        ( (k ·l (L ·r h)) ∙h K)) ∙h
      ( ap-concat-htpy'
        ( (inv-htpy ((k ∘ l) ·l H)) ∙h ((k ∘ l) ·l H))
        ( refl-htpy)
        ( (k ·l (L ·r h)) ∙h K)
        ( left-inv-htpy ((k ∘ l) ·l H))))

retraction-right-factor-retract-of-retraction-left-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retraction g → (retraction h) retract-of (retraction f)
pr1 (retraction-right-factor-retract-of-retraction-left-factor f g h H rg) =
  retraction-comp-htpy f g h H rg
pr1
  ( pr2
    ( retraction-right-factor-retract-of-retraction-left-factor f g h H rg)) =
  retraction-right-factor-htpy f g h H
pr2
  ( pr2
    ( retraction-right-factor-retract-of-retraction-left-factor f g h H rg)) =
  is-retraction-retraction-comp-htpy f g h H rg
```

### If `f` has a retraction, then `f` is injective

```agda
abstract
  is-injective-retraction :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → retraction f →
    is-injective f
  is-injective-retraction f (h , H) {x} {y} p = (inv (H x)) ∙ (ap h p ∙ H y)
```

### Transposing identifications along retractions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  transpose-eq-retraction :
    (g : B → A) (H : (g ∘ f) ~ id) {x : B} {y : A} →
    x ＝ f y → g x ＝ y
  transpose-eq-retraction g H refl = H _

  transpose-eq-retraction' :
    (g : B → A) (H : (g ∘ f) ~ id) {x : A} {y : B} →
    f x ＝ y → x ＝ g y
  transpose-eq-retraction' g H refl = inv (H _)
```
