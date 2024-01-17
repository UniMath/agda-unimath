# Flat discrete types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-discrete-crisp-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.coproduct-types
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

open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
```

</details>

## Idea

A crisp type is said to be
{{$concept "flat discrete" Disambiguation="crisp type" Agda=is-flat-discrete-crisp}},
or simply {{#concept "flat" Disambiguation="crisp type"}}, if it is
[flat](modal-type-theory.flat-modality.md) modal. I.e. if the flat counit is an
[equivalence](foundation-core.equivalences.md) at that type.

## Definition

### Flat discrete crisp types

```agda
module _
  {@♭ l : Level} (@♭ A : UU l)
  where

  is-flat-discrete-crisp : UU l
  is-flat-discrete-crisp = is-equiv (counit-flat {l} {A})

  is-property-is-flat-discrete-crisp : is-prop is-flat-discrete-crisp
  is-property-is-flat-discrete-crisp =
    is-property-is-equiv (counit-flat {l} {A})

  is-flat-discrete-crisp-Prop : Prop l
  is-flat-discrete-crisp-Prop = is-equiv-Prop (counit-flat {l} {A})
```

### Flat discrete crisp families

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  where

  is-flat-discrete-crisp-family : (@♭ B : @♭ A → UU l2) → UU (l1 ⊔ l2)
  is-flat-discrete-crisp-family B = (@♭ x : A) → is-flat-discrete-crisp (B x)
```

## Properties

### The empty type is flat discrete

```agda
map-is-flat-discrete-crisp-empty : empty → ♭ empty
map-is-flat-discrete-crisp-empty ()

is-section-map-is-flat-discrete-crisp-empty :
  is-section counit-flat map-is-flat-discrete-crisp-empty
is-section-map-is-flat-discrete-crisp-empty ()

is-retraction-map-is-flat-discrete-crisp-empty :
  is-retraction counit-flat map-is-flat-discrete-crisp-empty
is-retraction-map-is-flat-discrete-crisp-empty (cons-flat ())

is-flat-discrete-crisp-empty : is-flat-discrete-crisp empty
is-flat-discrete-crisp-empty =
  is-equiv-is-invertible
    ( map-is-flat-discrete-crisp-empty)
    ( is-section-map-is-flat-discrete-crisp-empty)
    ( is-retraction-map-is-flat-discrete-crisp-empty)
```

### The unit type is flat discrete

```agda
map-is-flat-discrete-crisp-unit : unit → ♭ unit
map-is-flat-discrete-crisp-unit star = cons-flat star

is-section-map-is-flat-discrete-crisp-unit :
  is-section counit-flat map-is-flat-discrete-crisp-unit
is-section-map-is-flat-discrete-crisp-unit _ = refl

is-retraction-map-is-flat-discrete-crisp-unit :
  is-retraction counit-flat map-is-flat-discrete-crisp-unit
is-retraction-map-is-flat-discrete-crisp-unit (cons-flat _) = refl

is-flat-discrete-crisp-unit : is-flat-discrete-crisp unit
is-flat-discrete-crisp-unit =
  is-equiv-is-invertible
    ( map-is-flat-discrete-crisp-unit)
    ( is-section-map-is-flat-discrete-crisp-unit)
    ( is-retraction-map-is-flat-discrete-crisp-unit)
```

### The type of booleans is flat discrete

```agda
map-is-flat-discrete-crisp-bool : bool → ♭ bool
map-is-flat-discrete-crisp-bool true = cons-flat true
map-is-flat-discrete-crisp-bool false = cons-flat false

is-section-map-is-flat-discrete-crisp-bool :
  is-section counit-flat map-is-flat-discrete-crisp-bool
is-section-map-is-flat-discrete-crisp-bool true = refl
is-section-map-is-flat-discrete-crisp-bool false = refl

is-retraction-map-is-flat-discrete-crisp-bool :
  is-retraction counit-flat map-is-flat-discrete-crisp-bool
is-retraction-map-is-flat-discrete-crisp-bool (cons-flat true) = refl
is-retraction-map-is-flat-discrete-crisp-bool (cons-flat false) = refl

is-flat-discrete-crisp-bool : is-flat-discrete-crisp bool
is-flat-discrete-crisp-bool =
  is-equiv-is-invertible
    ( map-is-flat-discrete-crisp-bool)
    ( is-section-map-is-flat-discrete-crisp-bool)
    ( is-retraction-map-is-flat-discrete-crisp-bool)
```

### The type of natural numbers is flat discrete

```agda
map-is-flat-discrete-crisp-ℕ : ℕ → ♭ ℕ
map-is-flat-discrete-crisp-ℕ zero-ℕ = cons-flat zero-ℕ
map-is-flat-discrete-crisp-ℕ (succ-ℕ x) =
  ap-map-flat succ-ℕ (map-is-flat-discrete-crisp-ℕ x)

compute-map-is-flat-discrete-crisp-ℕ :
  (@♭ x : ℕ) → map-is-flat-discrete-crisp-ℕ x ＝ cons-flat x
compute-map-is-flat-discrete-crisp-ℕ zero-ℕ =
  refl
compute-map-is-flat-discrete-crisp-ℕ (succ-ℕ x) =
  ap (ap-map-flat succ-ℕ) (compute-map-is-flat-discrete-crisp-ℕ x)

is-section-map-is-flat-discrete-crisp-ℕ :
  is-section counit-flat map-is-flat-discrete-crisp-ℕ
is-section-map-is-flat-discrete-crisp-ℕ zero-ℕ =
  refl
is-section-map-is-flat-discrete-crisp-ℕ (succ-ℕ x) =
  ( naturality-counit-flat succ-ℕ (map-is-flat-discrete-crisp-ℕ x)) ∙
  ( ap succ-ℕ (is-section-map-is-flat-discrete-crisp-ℕ x))

is-retraction-map-is-flat-discrete-crisp-ℕ :
  is-retraction counit-flat map-is-flat-discrete-crisp-ℕ
is-retraction-map-is-flat-discrete-crisp-ℕ (cons-flat x) =
  compute-map-is-flat-discrete-crisp-ℕ x

is-flat-discrete-crisp-ℕ : is-flat-discrete-crisp ℕ
is-flat-discrete-crisp-ℕ =
  is-equiv-is-invertible
    ( map-is-flat-discrete-crisp-ℕ)
    ( is-section-map-is-flat-discrete-crisp-ℕ)
    ( is-retraction-map-is-flat-discrete-crisp-ℕ)
```

## See also

- [Sharp codiscrete types](modal-type-theory.sharp-codiscrete-types.md) for the
  dual notion.
