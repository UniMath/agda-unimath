# Coinhabited types

```agda
module foundation.coinhabited-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

Two types `A` and `B` are said to be
{{#concept "coinhabited" Agda=is-coinhabited}} if `A` is
[inhabited](foundation.inhabited-types.md)
[if and only if](foundation.logical-equivalences.md) `B` is.

## Definitions

### The predicate of being coinhabited

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  is-coinhabited-Prop : Prop (l1 ⊔ l2)
  is-coinhabited-Prop = iff-Prop (is-inhabited-Prop A) (is-inhabited-Prop B)

  is-coinhabited : UU (l1 ⊔ l2)
  is-coinhabited = type-Prop is-coinhabited-Prop
```

### Every type is coinhabited with itself

```agda
module _
  {l : Level} (A : UU l)
  where

  is-coinhabited-self : is-coinhabited A A
  is-coinhabited-self = id-iff
```

### Coinhabitedness is a transitive relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-coinhabited-comp :
    is-coinhabited B C → is-coinhabited A B → is-coinhabited A C
  is-coinhabited-comp = _∘iff_
```

### Coinhabitedness is a symmetric relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-coinhabited-inv : is-coinhabited A B → is-coinhabited B A
  is-coinhabited-inv = inv-iff
```

### Forward and backward implications of coinhabited types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  forward-implication-is-coinhabited' : is-coinhabited A B → A → is-inhabited B
  forward-implication-is-coinhabited' e a =
    forward-implication e (unit-trunc-Prop a)

  forward-implication-is-coinhabited :
    is-coinhabited A B → is-inhabited A → is-inhabited B
  forward-implication-is-coinhabited = forward-implication

  backward-implication-is-coinhabited' : is-coinhabited A B → B → is-inhabited A
  backward-implication-is-coinhabited' e b =
    backward-implication e (unit-trunc-Prop b)

  backward-implication-is-coinhabited :
    is-coinhabited A B → is-inhabited B → is-inhabited A
  backward-implication-is-coinhabited = backward-implication
```

## See also

- [Biimplication of types](foundation.biimplication.md) is a related but
  stronger notion than coinhabitedness.
