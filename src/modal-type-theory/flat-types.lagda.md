# Flat types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
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
is-flat {l} A = is-equiv (counit-flat {l} {A})
```

## Properties

### Being flat is a property

```agda
is-property-is-flat : {@♭ l : Level} (@♭ A : UU l) → is-prop (is-flat A)
is-property-is-flat {l} A = is-property-is-equiv (counit-flat {l} {A})

is-flat-Prop : {@♭ l : Level} (@♭ A : UU l) → Prop l
is-flat-Prop {l} A = is-equiv-Prop (counit-flat {l} {A})
```

### The empty type is flat

```agda
map-is-flat-empty : empty → ♭ empty
map-is-flat-empty ()

is-section-map-is-flat-empty : (counit-flat ∘ map-is-flat-empty) ~ id
is-section-map-is-flat-empty ()

is-retraction-map-is-flat-empty : (map-is-flat-empty ∘ counit-flat) ~ id
is-retraction-map-is-flat-empty (cons-flat ())

is-flat-empty : is-flat empty
is-flat-empty =
  is-equiv-is-invertible
    ( map-is-flat-empty)
    ( is-section-map-is-flat-empty)
    ( is-retraction-map-is-flat-empty)
```

### The unit type is flat

```agda
map-is-flat-unit : unit → ♭ unit
map-is-flat-unit star = cons-flat star

is-section-map-is-flat-unit : (counit-flat ∘ map-is-flat-unit) ~ id
is-section-map-is-flat-unit _ = refl

is-retraction-map-is-flat-unit : (map-is-flat-unit ∘ counit-flat) ~ id
is-retraction-map-is-flat-unit (cons-flat _) = refl

is-flat-unit : is-flat unit
is-flat-unit =
  is-equiv-is-invertible
    ( map-is-flat-unit)
    ( is-section-map-is-flat-unit)
    ( is-retraction-map-is-flat-unit)
```

## See also

- [Codiscrete types](modal-type-theory.codiscrete-types.md) for the dual notion.
