# Transposing identifications along sections

```agda
module foundation.transposition-identifications-along-sections where
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
open import foundation-core.sections
```

</details>

## Idea

Consider a map `f : A → B` and a map `g : B → A` in the converse direction. Then
there is an [equivalence](foundation-core.equivalences.md)

```text
  is-section f g ≃ ((x : A) (y : B) → (x ＝ g y) → (f x ＝ y))
```

In other words, any [section homotopy](foundation-core.sections.md) `f ∘ g ~ id`
induces a unique family of
{{#concept "transposition" Disambiguation="identifications along sections" Agda=eq-transpose-is-section}}
maps

```text
  x ＝ g y → f x ＝ y
```

indexed by `x : A` and `y : B`.

### Transposing identifications along sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  eq-transpose-is-section :
    f ∘ g ~ id → {x : A} {y : B} → x ＝ g y → f x ＝ y
  eq-transpose-is-section H {x} {y} p = ap f p ∙ H y

  eq-transpose-is-section' :
    f ∘ g ~ id → {x : B} {y : A} → g x ＝ y → x ＝ f y
  eq-transpose-is-section' H {x} p = inv (H x) ∙ ap f p
```

## Properties

### The map that assigns to each section homotopy a family of transposition functions of identifications is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-section-eq-transpose :
    ({x : A} {y : B} → x ＝ g y → f x ＝ y) → f ∘ g ~ id
  is-section-eq-transpose H x = H refl

  is-section-eq-transpose' :
    ({x : B} {y : A} → g x ＝ y → x ＝ f y) → f ∘ g ~ id
  is-section-eq-transpose' H x = inv (H refl)

  is-retraction-is-section-eq-transpose :
    is-section-eq-transpose ∘ eq-transpose-is-section f g ~ id
  is-retraction-is-section-eq-transpose H = refl

  htpy-is-section-is-section-eq-transpose :
    (H : {x : A} {y : B} → x ＝ g y → f x ＝ y) →
    (x : A) (y : B) →
    eq-transpose-is-section f g (is-section-eq-transpose H) {x} {y} ~ H {x} {y}
  htpy-is-section-is-section-eq-transpose H x y refl = refl

  abstract
    is-section-is-section-eq-transpose :
      eq-transpose-is-section f g ∘ is-section-eq-transpose ~ id
    is-section-is-section-eq-transpose H =
      eq-htpy-implicit
        ( λ x →
          eq-htpy-implicit
          ( λ y →
            eq-htpy (htpy-is-section-is-section-eq-transpose H x y)))

  is-equiv-eq-transpose-is-section :
    is-equiv (eq-transpose-is-section f g)
  is-equiv-eq-transpose-is-section =
    is-equiv-is-invertible
      ( is-section-eq-transpose)
      ( is-section-is-section-eq-transpose)
      ( is-retraction-is-section-eq-transpose)

  equiv-eq-transpose-is-section :
    (f ∘ g ~ id) ≃ ({x : A} {y : B} → x ＝ g y → f x ＝ y)
  equiv-eq-transpose-is-section =
    (eq-transpose-is-section f g , is-equiv-eq-transpose-is-section)
```
