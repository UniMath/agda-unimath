# Irrefutable propositions

```agda
module foundation.irrefutable-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.function-types
open import foundation.propositions
open import foundation.subuniverses
open import foundation.universe-levels

open import logic.irrefutable-types
```

</details>

## Idea

The [subuniverse](foundation.subuniverses.md) of
{{#concept "irrefutable propositions" Agda=Irrefutable-Prop}}, or
{{#concept "double
negation dense propositions" Agda=Irrefutable-Prop}}, consists of [propositions](foundation-core.propositions.md)
`P` for which the [double negation](foundation.double-negation.md) `¬¬P` is true.

**Terminology.** The term _dense_ used here is in the sense of dense with
respect to a
[reflective subuniverse](orthogonal-factorization-systems.reflective-global-subuniverses.md)/[modality](orthogonal-factorization-systems.higher-modalities.md),
or connected. Here, it means that the double negation of `P` is contractible.
Since negations are propositions, it thus suffices that the double negation is
true.

## Definitions

### The predicate on a proposition of being irrefutable

```agda
module _
  {l : Level} (P : Prop l)
  where

  is-irrefutable-Prop : Prop l
  is-irrefutable-Prop = is-irrefutable-prop-Type (type-Prop P)

  is-irrefutable-type-Prop : UU l
  is-irrefutable-type-Prop = is-irrefutable (type-Prop P)
```

### The predicate on a type of being an irrefutable proposition

```agda
module _
  {l : Level} (P : UU l)
  where

  is-irrefutable-prop : UU l
  is-irrefutable-prop = is-prop P × (¬¬ P)

  is-prop-is-irrefutable-prop : is-prop is-irrefutable-prop
  is-prop-is-irrefutable-prop =
    is-prop-product (is-prop-is-prop P) is-prop-double-negation

  is-irrefutable-prop-Prop : Prop l
  is-irrefutable-prop-Prop = is-irrefutable-prop , is-prop-is-irrefutable-prop

module _
  {l : Level} {P : UU l} (H : is-irrefutable-prop P)
  where

  is-prop-type-is-irrefutable-prop : is-prop P
  is-prop-type-is-irrefutable-prop = pr1 H

  prop-is-irrefutable-prop : Prop l
  prop-is-irrefutable-prop = P , is-prop-type-is-irrefutable-prop

  is-irrefutable-is-irrefutable-prop :
    is-irrefutable P
  is-irrefutable-is-irrefutable-prop = pr2 H
```

### The subuniverse of irrefutable propositions

```agda
Irrefutable-Prop : (l : Level) → UU (lsuc l)
Irrefutable-Prop l = type-subuniverse is-irrefutable-prop-Prop

make-Irrefutable-Prop :
  {l : Level} (P : Prop l) → is-irrefutable-type-Prop P → Irrefutable-Prop l
make-Irrefutable-Prop P is-irrefutable-P =
  ( type-Prop P , is-prop-type-Prop P , is-irrefutable-P)

module _
  {l : Level} (P : Irrefutable-Prop l)
  where

  type-Irrefutable-Prop : UU l
  type-Irrefutable-Prop = pr1 P

  is-irrefutable-prop-type-Irrefutable-Prop :
    is-irrefutable-prop type-Irrefutable-Prop
  is-irrefutable-prop-type-Irrefutable-Prop = pr2 P

  is-prop-type-Irrefutable-Prop : is-prop type-Irrefutable-Prop
  is-prop-type-Irrefutable-Prop =
    is-prop-type-is-irrefutable-prop is-irrefutable-prop-type-Irrefutable-Prop

  prop-Irrefutable-Prop : Prop l
  prop-Irrefutable-Prop = type-Irrefutable-Prop , is-prop-type-Irrefutable-Prop

  is-irrefutable-Irrefutable-Prop : is-irrefutable type-Irrefutable-Prop
  is-irrefutable-Irrefutable-Prop =
    is-irrefutable-is-irrefutable-prop is-irrefutable-prop-type-Irrefutable-Prop
```

## Properties

### Contractible types are irrefutable propositions

```agda
is-irrefutable-prop-is-contr :
  {l : Level} {P : UU l} → is-contr P → is-irrefutable-prop P
is-irrefutable-prop-is-contr H =
  ( is-prop-is-contr H , is-irrefutable-is-contr H)
```

### Decidability is irrefutable

```agda
module _
  {l : Level} (P : Prop l)
  where

  is-irrefutable-is-decidable-Prop :
    is-irrefutable-type-Prop (is-decidable-Prop P)
  is-irrefutable-is-decidable-Prop = is-irrefutable-is-decidable

  is-decidable-prop-Irrefutable-Prop : Irrefutable-Prop l
  is-decidable-prop-Irrefutable-Prop =
    make-Irrefutable-Prop (is-decidable-Prop P) is-irrefutable-is-decidable-Prop
```

### Dependent sums of irrefutable propositions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-irrefutable-prop-Σ :
    is-irrefutable-prop A → ((x : A) → is-irrefutable-prop (B x)) →
    is-irrefutable-prop (Σ A B)
  is-irrefutable-prop-Σ a b =
    ( is-prop-Σ
      ( is-prop-type-is-irrefutable-prop a)
      ( is-prop-type-is-irrefutable-prop ∘ b) ,
    is-irrefutable-Σ
      ( is-irrefutable-is-irrefutable-prop a)
      ( is-irrefutable-is-irrefutable-prop ∘ b))
```

### Products of irrefutable propositions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-irrefutable-prop-product :
    is-irrefutable-prop A → is-irrefutable-prop B → is-irrefutable-prop (A × B)
  is-irrefutable-prop-product a b = is-irrefutable-prop-Σ a (λ _ → b)
```

## See also

- [De Morgan's law](logic.de-morgans-law.md) is irrefutable.
