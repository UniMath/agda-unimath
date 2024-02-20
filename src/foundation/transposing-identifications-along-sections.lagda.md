# Transposing identifications along sections

```agda
module foundation.transposing-identifications-along-sections where
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

Consider a map `f : A → B` and a map `g : B → A` in the converse direction. Then there is an [equivalence](foundation-core.equivalences.md)

```text
  is-section f g ≃ ((x : A) (y : B) → (x ＝ g y) ≃ (f x ＝ y))
```

In other words, any [section homotopy](foundation-core.sections.md) `f ∘ g ~ id` induces a unique family of {{#concept "transposition" Disambiguation="identifications along sections" Agda=transpose-eq-is-section}} maps

```text
  x ＝ g y → f x ＝ y
```

indexed by `x : A` and `y : B`. 

### Transposing identifications along sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  transpose-eq-is-section :
    f ∘ g ~ id → {x : A} {y : B} → x ＝ g y → f x ＝ y
  transpose-eq-is-section H {x} {y} p = ap f p ∙ H y

  transpose-eq-is-section' :
    f ∘ g ~ id → {x : B} {y : A} → g x ＝ y → x ＝ f y
  transpose-eq-is-section' H {x} refl = inv (H x)
```

## Properties

### The map that assings to each section homotopy a family of transposition functions of identifications is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-section-transpose-eq :
    ({x : A} {y : B} → x ＝ g y → f x ＝ y) → f ∘ g ~ id
  is-section-transpose-eq H x = H refl

  is-section-transpose-eq' :
    ({x : B} {y : A} → g x ＝ y → x ＝ f y) → f ∘ g ~ id
  is-section-transpose-eq' H x = inv (H refl)

  is-retraction-is-section-transpose-eq :
    is-section-transpose-eq ∘ transpose-eq-is-section f g ~ id
  is-retraction-is-section-transpose-eq H = refl

  htpy-is-section-is-section-transpose-eq :
    (H : {x : A} {y : B} → x ＝ g y → f x ＝ y) →
    (x : A) (y : B) →
    transpose-eq-is-section f g (is-section-transpose-eq H) {x} {y} ~ H {x} {y}
  htpy-is-section-is-section-transpose-eq H x y refl = refl

  abstract
    is-section-is-section-transpose-eq :
      transpose-eq-is-section f g ∘ is-section-transpose-eq ~ id
    is-section-is-section-transpose-eq H =
      eq-htpy-implicit
        ( λ x →
          eq-htpy-implicit
          ( λ y →
            eq-htpy (htpy-is-section-is-section-transpose-eq H x y)))

  is-equiv-transpose-eq-is-section :
    is-equiv (transpose-eq-is-section f g)
  is-equiv-transpose-eq-is-section =
    is-equiv-is-invertible
      ( is-section-transpose-eq)
      ( is-section-is-section-transpose-eq)
      ( is-retraction-is-section-transpose-eq)

  equiv-transpose-eq-is-section :
    (f ∘ g ~ id) ≃ ({x : A} {y : B} → x ＝ g y → f x ＝ y)
  equiv-transpose-eq-is-section =
    (transpose-eq-is-section f g , is-equiv-transpose-eq-is-section)
```
