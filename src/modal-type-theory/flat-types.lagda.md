# Flat types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.unit-type
open import foundation.universe-levels

open import modal-type-theory.flat-modality
```

</details>

## Idea

A crisp type is said to be **flat** if it is
[flat modal](modal-type-theory.flat-modality.md), i.e. if the flat counit at
that type is an [equivalence](foundation-core.equivalences.md).

## Definition

```agda
is-flat : {@♭ l : Level} (@♭ A : UU l) → UU l
is-flat {l} A = is-equiv (counit-♭ {l} {A})
```

## Properties

### Being flat is a property

```agda
is-property-is-flat : {@♭ l : Level} (@♭ A : UU l) → is-prop (is-flat A)
is-property-is-flat {l} A = is-property-is-equiv (counit-♭ {l} {A})

is-flat-Prop : {@♭ l : Level} (@♭ A : UU l) → Prop l
is-flat-Prop {l} A = is-equiv-Prop (counit-♭ {l} {A})
```

### The empty type is flat

```agda
map-is-flat-empty : empty → ♭ empty
map-is-flat-empty ()

is-section-map-is-flat-empty : (counit-♭ ∘ map-is-flat-empty) ~ id
is-section-map-is-flat-empty ()

is-retraction-map-is-flat-empty : (map-is-flat-empty ∘ counit-♭) ~ id
is-retraction-map-is-flat-empty (con-♭ ())

is-flat-empty : is-flat empty
is-flat-empty =
  is-equiv-has-inverse
    ( map-is-flat-empty)
    ( is-section-map-is-flat-empty)
    ( is-retraction-map-is-flat-empty)
```

### The unit type is flat

```agda
map-is-flat-unit : unit → ♭ unit
map-is-flat-unit star = con-♭ star

is-section-map-is-flat-unit : (counit-♭ ∘ map-is-flat-unit) ~ id
is-section-map-is-flat-unit _ = refl

is-retraction-map-is-flat-unit : (map-is-flat-unit ∘ counit-♭) ~ id
is-retraction-map-is-flat-unit (con-♭ _) = refl

is-flat-unit : is-flat unit
is-flat-unit =
  is-equiv-has-inverse
    ( map-is-flat-unit)
    ( is-section-map-is-flat-unit)
    ( is-retraction-map-is-flat-unit)
```

### The type of natural numbers is flat

```agda
-- map-is-flat-ℕ : ℕ → ♭ ℕ
-- map-is-flat-ℕ zero-ℕ = con-♭ zero-ℕ
-- map-is-flat-ℕ (succ-ℕ n) = ap-♭ succ-ℕ (map-is-flat-ℕ n)

-- is-section-map-is-flat : (counit-♭ ∘ map-is-flat-ℕ) ~ id
-- is-section-map-is-flat zero-ℕ = refl
-- is-section-map-is-flat (succ-ℕ x) = {!  !}
```

### Flat types are closed under taking dependent sums

```agda
module _
  {@♭ l1 l2 : Level}
  (@♭ A : UU l1) (@♭ B : A → UU l2)
  (is-flat-A : is-flat A) (is-flat-B : (@♭ a : A) → is-flat (B a))
  where

  -- map-is-flat-Σ : Σ A B → ♭ (Σ A B)
  -- map-is-flat-Σ (x , y) =
  --   map-inv-distributive-♭-Σ
  --     ( map-inv-is-equiv is-flat-A x , map-inv-is-equiv {! is-flat-B x !} y)

  -- is-flat-Σ :  is-flat (Σ A B)
  -- is-flat-Σ = {!  !}
```
