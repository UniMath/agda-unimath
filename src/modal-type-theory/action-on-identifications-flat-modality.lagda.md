# The action on identifications of the flat modality

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.action-on-identifications-flat-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import modal-type-theory.action-on-identifications-crisp-functions
open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
```

</details>

## Idea

Given a crisp [identification](foundation-core.identity-types.md) `x ＝ y` in
`A`, then there is an identification `intro-flat x ＝ intro-flat y` in `♭ A`.

## Definitions

### The action on identifications of the flat modality

```agda
module _
  {@♭ l1 : Level} {@♭ A : UU l1} {@♭ x y : A}
  where

  ap-flat : @♭ x ＝ y → intro-flat x ＝ intro-flat y
  ap-flat = crisp-ap intro-flat
```

## Properties

### Computing the flat modality's action on reflexivity

```agda
module _
  {@♭ l : Level} {@♭ A : UU l} {@♭ x : A}
  where

  compute-refl-ap-flat : ap-flat (refl {x = x}) ＝ refl
  compute-refl-ap-flat = refl
```

### The action on identifications of the flat modality is a crisp section of the action on identifications of its counit

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  is-crisp-section-ap-flat :
    {@♭ x y : A} (@♭ p : x ＝ y) → ap (counit-flat) (ap-flat p) ＝ p
  is-crisp-section-ap-flat =
    crisp-based-ind-Id
      ( λ y p → ap (counit-flat) (ap-flat p) ＝ p)
      ( refl)
```

### The action on identifications of the flat modality from {{#cite Shu18}}

**Note.** While we record the constructions from Corollary 6.3 {{#cite Shu18}}
here, the construction of `ap-flat` is preferred elsewhere.

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  ap-flat' :
    {@♭ x y : A} → @♭ (x ＝ y) → intro-flat x ＝ intro-flat y
  ap-flat' {x} {y} p =
    eq-Eq-flat (intro-flat x) (intro-flat y) (intro-flat p)

  compute-refl-ap-flat' :
    {@♭ x : A} → ap-flat' (refl {x = x}) ＝ refl
  compute-refl-ap-flat' = refl

  is-crisp-section-ap-flat' :
    {@♭ x y : A} (@♭ p : x ＝ y) → ap (counit-flat) (ap-flat' p) ＝ p
  is-crisp-section-ap-flat' =
    crisp-based-ind-Id
      ( λ y p → ap (counit-flat) (ap-flat' p) ＝ p)
      ( refl)

  compute-ap-flat' :
    {@♭ x y : A} (@♭ p : x ＝ y) → ap-flat p ＝ ap-flat' p
  compute-ap-flat' =
    crisp-based-ind-Id (λ y p → ap-flat p ＝ ap-flat' p) refl
```
