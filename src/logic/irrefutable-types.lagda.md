# Irrefutable types

```agda
module logic.irrefutable-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.function-types
open import foundation.inhabited-types
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
{{#concept "irrefutable types" Agda=Irrefutable-Type}}, or
{{#concept "double negation
dense types" Agda=Irrefutable-Type}}, consists of types `X` for which the [double negation](foundation.double-negation.md)
`¬¬X` is true.

**Terminology.** The term _dense_ used here is in the sense of dense with
respect to a
[reflective subuniverse](orthogonal-factorization-systems.reflective-global-subuniverses.md)/[modality](orthogonal-factorization-systems.higher-modalities.md),
or connected. Here, it means that the double negation of `X` is contractible.
Since negations are propositions, it thus suffices that the double negation is
true.

## Definitions

### The predicate on a type of being irrefutable

```agda
is-irrefutable : {l : Level} → UU l → UU l
is-irrefutable X = ¬¬ X

is-prop-is-irrefutable : {l : Level} {X : UU l} → is-prop (is-irrefutable X)
is-prop-is-irrefutable = is-prop-double-negation

is-irrefutable-prop-Type : {l : Level} → UU l → Prop l
is-irrefutable-prop-Type X = (is-irrefutable X , is-prop-is-irrefutable)
```

### The subuniverse of irrefutable types

```agda
Irrefutable-Type : (l : Level) → UU (lsuc l)
Irrefutable-Type l = type-subuniverse is-irrefutable-prop-Type

make-Irrefutable-Type :
  {l : Level} {X : UU l} → is-irrefutable X → Irrefutable-Type l
make-Irrefutable-Type {X = X} is-irrefutable-X = (X , is-irrefutable-X)

module _
  {l : Level} (X : Irrefutable-Type l)
  where

  type-Irrefutable-Type : UU l
  type-Irrefutable-Type = pr1 X

  is-irrefutable-Irrefutable-Type : is-irrefutable type-Irrefutable-Type
  is-irrefutable-Irrefutable-Type = pr2 X
```

## Properties

### Provable types are irrefutable

```agda
is-irrefutable-has-element : {l : Level} {X : UU l} → X → is-irrefutable X
is-irrefutable-has-element = intro-double-negation

is-irrefutable-unit : is-irrefutable unit
is-irrefutable-unit = is-irrefutable-has-element star
```

### Inhabited types are irrefutable

```agda
is-irrefutable-is-inhabited :
  {l : Level} {X : UU l} → is-inhabited X → is-irrefutable X
is-irrefutable-is-inhabited = intro-double-negation-type-trunc-Prop
```

### Contractible types are irrefutable

```agda
is-irrefutable-is-contr :
  {l : Level} {X : UU l} → is-contr X → is-irrefutable X
is-irrefutable-is-contr H = intro-double-negation (center H)
```

### If it is irrefutable that a type is irrefutable, then the type is irrefutable

```agda
is-idempotent-is-irrefutable :
  {l : Level} {X : UU l} → is-irrefutable (is-irrefutable X) → is-irrefutable X
is-idempotent-is-irrefutable {X = X} = double-negation-elim-neg (¬ X)
```

### Decidability is irrefutable

```agda
is-irrefutable-is-decidable :
  {l : Level} {A : UU l} → is-irrefutable (is-decidable A)
is-irrefutable-is-decidable H = H (inr (H ∘ inl))
```

### Double negation elimination is irrefutable

```agda
is-irrefutable-double-negation-elim :
  {l : Level} {A : UU l} → is-irrefutable (has-double-negation-elim A)
is-irrefutable-double-negation-elim H =
  H (λ f → ex-falso (f (λ a → H (λ _ → a))))
```

### Dependent sums of irrefutable types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-irrefutable-Σ :
    is-irrefutable A → ((x : A) → is-irrefutable (B x)) → is-irrefutable (Σ A B)
  is-irrefutable-Σ nna nnb nab = nna (λ a → nnb a (λ b → nab (a , b)))
```

### Products of irrefutable types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-irrefutable-product :
    is-irrefutable A → is-irrefutable B → is-irrefutable (A × B)
  is-irrefutable-product nna nnb = is-irrefutable-Σ nna (λ _ → nnb)
```

### Coproducts of irrefutable types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-irrefutable-coproduct-inl : is-irrefutable A → is-irrefutable (A + B)
  is-irrefutable-coproduct-inl nna x = nna (x ∘ inl)

  is-irrefutable-coproduct-inr : is-irrefutable B → is-irrefutable (A + B)
  is-irrefutable-coproduct-inr nnb x = nnb (x ∘ inr)
```

## See also

- [Irrefutable propositions](foundation.irrefutable-propositions.md)
- [De Morgan's law](logic.de-morgans-law.md) is irrefutable
