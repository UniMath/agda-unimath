# Disjunction of types

```agda
module foundation.disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

The
{{#concept "disjunction" Disambiguation="of types" Agda=disjunction-prop-Type}}
of two types `A` and `B` is the
[propositional truncation](foundation.propositional-truncations.md) of their
[coproduct](foundation-core.coproduct-types.md).

```text
  A ∨ B := ║ A + B ║₋₁
```

The universal property of the disjunction states that, for every
[proposition](foundation-core.propositions.md) `R`, the evaluation map

```text
  ev : ((A ∨ B) → R) → ((A → R) ∧ (B → R))
```

is an [equivalence](foundation.logical-equivalence.md).

## Definitions

### Disjunction of types

```agda
disjunction-prop-Type : {l1 l2 : Level} → UU l1 → UU l2 → Prop (l1 ⊔ l2)
disjunction-prop-Type A B = trunc-Prop (A + B)

disjunction-Type : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
disjunction-Type A B = type-Prop (disjunction-prop-Type A B)

_∨_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
_∨_ = disjunction-Type
```

## Properties

### The introduction rules for disjunction

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  inl-disjunction : A → A ∨ B
  inl-disjunction = unit-trunc-Prop ∘ inl

  inr-disjunction : B → A ∨ B
  inr-disjunction = unit-trunc-Prop ∘ inr
```

### The universal property of disjunctions

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (R : Prop l3)
  where

  ev-disjunction :
    ((A ∨ B) → type-Prop R) → (A → type-Prop R) × (B → type-Prop R)
  pr1 (ev-disjunction h) = h ∘ (inl-disjunction A B)
  pr2 (ev-disjunction h) = h ∘ (inr-disjunction A B)

  elim-disjunction :
    (A → type-Prop R) × (B → type-Prop R) → A ∨ B → type-Prop R
  elim-disjunction (f , g) =
    map-universal-property-trunc-Prop R (rec-coproduct f g)

  abstract
    is-equiv-ev-disjunction :
      is-equiv ev-disjunction
    is-equiv-ev-disjunction =
      is-equiv-is-prop
        ( is-prop-function-type (is-prop-type-Prop R))
        ( is-prop-product
          ( is-prop-function-type (is-prop-type-Prop R))
          ( is-prop-function-type (is-prop-type-Prop R)))
        ( elim-disjunction)
```

### The recursion principle of disjunctions

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (R : Prop l3)
  where

  rec-disjunction :
    (A → type-Prop R) → (B → type-Prop R) → A ∨ B → type-Prop R
  rec-disjunction f g = elim-disjunction A B R (f , g)
```

### The unit laws for disjunction

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  map-left-unit-law-disjunction-is-empty :
    is-empty A → A ∨ B → is-inhabited B
  map-left-unit-law-disjunction-is-empty f =
    rec-disjunction A B (is-inhabited-Prop B) (ex-falso ∘ f) unit-trunc-Prop

  map-right-unit-law-disjunction-is-empty :
    is-empty B → A ∨ B → is-inhabited A
  map-right-unit-law-disjunction-is-empty f =
    rec-disjunction A B (is-inhabited-Prop A) unit-trunc-Prop (ex-falso ∘ f)
```

## See also

- [Disjunction of propositions](foundation.disjunction-propositions.md)
