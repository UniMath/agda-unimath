# Irrefutable propositions

```agda
module foundation.irrefutable-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.function-types
open import foundation.negation
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

The [subuniverse](foundation.subuniverses.md) of
{{#concept "irrefutable propositions" Agda=Irrefutable-Prop}} consists of
[propositions](foundation-core.propositions.md) `P` for which the
[double negation](foundation.double-negation.md) `¬¬P` is true.

## Definitions

### The predicate on a proposition of being irrefutable

```agda
is-irrefutable : {l : Level} → Prop l → UU l
is-irrefutable P = ¬¬ (type-Prop P)

is-prop-is-irrefutable : {l : Level} (P : Prop l) → is-prop (is-irrefutable P)
is-prop-is-irrefutable P = is-prop-double-negation

is-irrefutable-Prop : {l : Level} → Prop l → Prop l
is-irrefutable-Prop = double-negation-Prop
```

### The subuniverse of irrefutable propositions

```agda
subuniverse-Irrefutable-Prop : (l : Level) → subuniverse l l
subuniverse-Irrefutable-Prop l A =
  product-Prop (is-prop-Prop A) (double-negation-type-Prop A)

Irrefutable-Prop : (l : Level) → UU (lsuc l)
Irrefutable-Prop l =
  type-subuniverse (subuniverse-Irrefutable-Prop l)

make-Irrefutable-Prop :
  {l : Level} (P : Prop l) → is-irrefutable P → Irrefutable-Prop l
make-Irrefutable-Prop P is-irrefutable-P =
  ( type-Prop P , is-prop-type-Prop P , is-irrefutable-P)

module _
  {l : Level} (P : Irrefutable-Prop l)
  where

  type-Irrefutable-Prop : UU l
  type-Irrefutable-Prop = pr1 P

  is-prop-type-Irrefutable-Prop : is-prop type-Irrefutable-Prop
  is-prop-type-Irrefutable-Prop = pr1 (pr2 P)

  prop-Irrefutable-Prop : Prop l
  prop-Irrefutable-Prop = type-Irrefutable-Prop , is-prop-type-Irrefutable-Prop

  is-irrefutable-Irrefutable-Prop : is-irrefutable prop-Irrefutable-Prop
  is-irrefutable-Irrefutable-Prop = pr2 (pr2 P)
```

## Properties

### Provable propositions are irrefutable

```agda
module _
  {l : Level} (P : Prop l)
  where

  is-irrefutable-is-inhabited : type-Prop P → is-irrefutable P
  is-irrefutable-is-inhabited = intro-double-negation

is-irrefutable-unit : is-irrefutable unit-Prop
is-irrefutable-unit = is-irrefutable-is-inhabited unit-Prop star
```

### If it is irrefutable that a proposition is irrefutable, then the proposition is irrefutable

```agda
module _
  {l : Level} (P : Prop l)
  where

  is-irrefutable-is-irrefutable-is-irrefutable :
    is-irrefutable (is-irrefutable-Prop P) → is-irrefutable P
  is-irrefutable-is-irrefutable-is-irrefutable =
    double-negation-elim-neg (¬ (type-Prop P))
```

### The decidability of a proposition is irrefutable

```agda
is-irrefutable-is-decidable : {l : Level} {A : UU l} → ¬¬ (is-decidable A)
is-irrefutable-is-decidable H = H (inr (H ∘ inl))

module _
  {l : Level} (P : Prop l)
  where

  is-irrefutable-is-decidable-Prop : is-irrefutable (is-decidable-Prop P)
  is-irrefutable-is-decidable-Prop = is-irrefutable-is-decidable

  is-decidable-prop-Irrefutable-Prop : Irrefutable-Prop l
  is-decidable-prop-Irrefutable-Prop =
    make-Irrefutable-Prop (is-decidable-Prop P) is-irrefutable-is-decidable-Prop
```
