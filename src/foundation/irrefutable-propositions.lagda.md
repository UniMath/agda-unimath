# Irrefutable propositions

```agda
module foundation.irrefutable-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.function-types
open import foundation.negation
open import foundation.propositions
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import logic.double-negation-elimination
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
module _
  {l : Level} (P : Prop l)
  where

  is-irrefutable : UU l
  is-irrefutable = ¬¬ (type-Prop P)

  is-prop-is-irrefutable : is-prop is-irrefutable
  is-prop-is-irrefutable = is-prop-double-negation

  is-irrefutable-Prop : Prop l
  is-irrefutable-Prop = double-negation-Prop P
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
    is-irrefutable (P , is-prop-type-is-irrefutable-prop)
  is-irrefutable-is-irrefutable-prop = pr2 H
```

### The subuniverse of irrefutable propositions

```agda
Irrefutable-Prop : (l : Level) → UU (lsuc l)
Irrefutable-Prop l = type-subuniverse is-irrefutable-prop-Prop

make-Irrefutable-Prop :
  {l : Level} (P : Prop l) → is-irrefutable P → Irrefutable-Prop l
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

  is-irrefutable-Irrefutable-Prop : is-irrefutable prop-Irrefutable-Prop
  is-irrefutable-Irrefutable-Prop =
    is-irrefutable-is-irrefutable-prop is-irrefutable-prop-type-Irrefutable-Prop
```

## Properties

### Provable propositions are irrefutable

```agda
module _
  {l : Level} (P : Prop l)
  where

  is-irrefutable-has-element : type-Prop P → is-irrefutable P
  is-irrefutable-has-element = intro-double-negation

is-irrefutable-unit : is-irrefutable unit-Prop
is-irrefutable-unit = is-irrefutable-has-element unit-Prop star
```

### Contractible types are irrefutable propositions

```agda
is-irrefutable-prop-is-contr :
  {l : Level} {P : UU l} → is-contr P → is-irrefutable-prop P
is-irrefutable-prop-is-contr H =
  ( is-prop-is-contr H , intro-double-negation (center H))
```

### If it is irrefutable that a proposition is irrefutable, then the proposition is irrefutable

```agda
module _
  {l : Level} (P : Prop l)
  where

  is-idempotent-is-irrefutable :
    is-irrefutable (is-irrefutable-Prop P) → is-irrefutable P
  is-idempotent-is-irrefutable =
    double-negation-elim-neg (¬ (type-Prop P))
```

### Decidability is irrefutable

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

### Double negation elimination is irrefutable

```agda
is-irrefutable-double-negation-elim :
  {l : Level} {A : UU l} → ¬¬ (has-double-negation-elim A)
is-irrefutable-double-negation-elim H =
  H (λ f → ex-falso (f (λ a → H (λ _ → a))))
```

### Dependent sums of of irrefutable propositions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-irrefutable-Σ :
    ¬¬ A → ((x : A) → ¬¬ B x) → ¬¬ (Σ A B)
  is-irrefutable-Σ nna nnb nab = nna (λ a → nnb a (λ b → nab (a , b)))

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

  is-irrefutable-product : ¬¬ A → ¬¬ B → ¬¬ (A × B)
  is-irrefutable-product nna nnb = is-irrefutable-Σ nna (λ _ → nnb)

  is-irrefutable-prop-product :
    is-irrefutable-prop A → is-irrefutable-prop B → is-irrefutable-prop (A × B)
  is-irrefutable-prop-product a b = is-irrefutable-prop-Σ a (λ _ → b)
```

### Coproducts of irrefutable propositions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-irrefutable-coproduct-inl : ¬¬ A → ¬¬ (A + B)
  is-irrefutable-coproduct-inl nna x = nna (x ∘ inl)

  is-irrefutable-coproduct-inr : ¬¬ B → ¬¬ (A + B)
  is-irrefutable-coproduct-inr nnb x = nnb (x ∘ inr)
```

## See also

- [De Morgan's law](logic.de-morgans-law.md) is irrefutable.
