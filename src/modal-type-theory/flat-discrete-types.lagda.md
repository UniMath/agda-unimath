# Flat discrete types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-discrete-types where
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

A crisp type is said to be **(flat) discrete** if it is
[flat](modal-type-theory.flat-modality.md) modal, i.e. if the flat counit at
that type is an [equivalence](foundation-core.equivalences.md).

## Definition

```agda
is-flat-discrete : {@♭ l : Level} (@♭ A : UU l) → UU l
is-flat-discrete {l} A = is-equiv (counit-flat {l} {A})
```

## Properties

### Being flat is a property

```agda
is-property-is-flat-discrete :
  {@♭ l : Level} (@♭ A : UU l) → is-prop (is-flat-discrete A)
is-property-is-flat-discrete {l} A = is-property-is-equiv (counit-flat {l} {A})

is-flat-discrete-Prop : {@♭ l : Level} (@♭ A : UU l) → Prop l
is-flat-discrete-Prop {l} A = is-equiv-Prop (counit-flat {l} {A})
```

### The empty type is flat

```agda
map-is-flat-discrete-empty : empty → ♭ empty
map-is-flat-discrete-empty ()

is-section-map-is-flat-discrete-empty :
  (counit-flat ∘ map-is-flat-discrete-empty) ~ id
is-section-map-is-flat-discrete-empty ()

is-retraction-map-is-flat-discrete-empty :
  (map-is-flat-discrete-empty ∘ counit-flat) ~ id
is-retraction-map-is-flat-discrete-empty (cons-flat ())

is-flat-discrete-empty : is-flat-discrete empty
is-flat-discrete-empty =
  is-equiv-is-invertible
    ( map-is-flat-discrete-empty)
    ( is-section-map-is-flat-discrete-empty)
    ( is-retraction-map-is-flat-discrete-empty)
```

### The unit type is flat

```agda
map-is-flat-discrete-unit : unit → ♭ unit
map-is-flat-discrete-unit star = cons-flat star

is-section-map-is-flat-discrete-unit :
  counit-flat ∘ map-is-flat-discrete-unit ~ id
is-section-map-is-flat-discrete-unit _ = refl

is-retraction-map-is-flat-discrete-unit :
  map-is-flat-discrete-unit ∘ counit-flat ~ id
is-retraction-map-is-flat-discrete-unit (cons-flat _) = refl

is-flat-discrete-unit : is-flat-discrete unit
is-flat-discrete-unit =
  is-equiv-is-invertible
    ( map-is-flat-discrete-unit)
    ( is-section-map-is-flat-discrete-unit)
    ( is-retraction-map-is-flat-discrete-unit)
```

## See also

- [Sharp codiscrete types](modal-type-theory.sharp-codiscrete-types.md) for the
  dual notion.
