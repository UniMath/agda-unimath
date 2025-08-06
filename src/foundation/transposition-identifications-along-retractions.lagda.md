# Transposing identifications along retractions

```agda
module foundation.transposition-identifications-along-retractions where
```

<details><summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
```

</details>

## Idea

Consider a map `f : A → B` and a map `g : B → A` in the converse direction. Then
there is an [equivalence](foundation-core.equivalences.md)

```text
  is-retraction f g ≃ ((x : A) (y : B) → (f x ＝ y) → (x ＝ g y))
```

In other words, any [retracting homotopy](foundation-core.retractions.md)
`g ∘ f ~ id` induces a unique family of
{{#concept "transposition" Disambiguation="identifications along retractions" Agda=eq-transpose-is-retraction}}
maps

```text
  f x ＝ y → x ＝ g y
```

indexed by `x : A` and `y : B`.

## Definitions

### Transposing identifications along retractions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  eq-transpose-is-retraction :
    is-retraction f g → {x : B} {y : A} → x ＝ f y → g x ＝ y
  eq-transpose-is-retraction H {x} {y} p = ap g p ∙ H y

  eq-transpose-is-retraction' :
    is-retraction f g → {x : A} {y : B} → f x ＝ y → x ＝ g y
  eq-transpose-is-retraction' H {x} p = inv (H x) ∙ ap g p
```

## Properties

### The map that assigns to each retracting homotopy a family of transposition functions of identifications is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-retraction-eq-transpose :
    ({x : B} {y : A} → x ＝ f y → g x ＝ y) → is-retraction f g
  is-retraction-eq-transpose H x = H refl

  is-retraction-eq-transpose' :
    ({x : A} {y : B} → f x ＝ y → x ＝ g y) → is-retraction f g
  is-retraction-eq-transpose' H x = inv (H refl)

  is-retraction-is-retraction-eq-transpose :
    is-retraction-eq-transpose ∘ eq-transpose-is-retraction f g ~ id
  is-retraction-is-retraction-eq-transpose H = refl

  htpy-is-section-is-retraction-eq-transpose :
    (H : {x : B} {y : A} → x ＝ f y → g x ＝ y)
    (x : B) (y : A) →
    eq-transpose-is-retraction f g (is-retraction-eq-transpose H) {x} {y} ~
    H {x} {y}
  htpy-is-section-is-retraction-eq-transpose H x y refl = refl

  abstract
    is-section-is-retraction-eq-transpose :
      eq-transpose-is-retraction f g ∘ is-retraction-eq-transpose ~ id
    is-section-is-retraction-eq-transpose H =
      eq-htpy-implicit
        ( λ x →
          eq-htpy-implicit
            ( λ y → eq-htpy (htpy-is-section-is-retraction-eq-transpose H x y)))

  is-equiv-eq-transpose-is-retraction :
    is-equiv (eq-transpose-is-retraction f g)
  is-equiv-eq-transpose-is-retraction =
    is-equiv-is-invertible
      ( is-retraction-eq-transpose)
      ( is-section-is-retraction-eq-transpose)
      ( is-retraction-is-retraction-eq-transpose)

  equiv-eq-transpose-is-retraction :
    is-retraction f g ≃ ({x : B} {y : A} → x ＝ f y → g x ＝ y)
  equiv-eq-transpose-is-retraction =
    ( eq-transpose-is-retraction f g , is-equiv-eq-transpose-is-retraction)
```
