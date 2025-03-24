# Coinhabited pairs of types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.coinhabited-pairs-of-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.inhabited-types funext univalence truncations
open import foundation.logical-equivalences funext
open import foundation.propositional-truncations funext univalence
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

### Forward and backward implications of coinhabited types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  forward-implication-is-coinhabited :
    is-coinhabited A B → is-inhabited A → is-inhabited B
  forward-implication-is-coinhabited = forward-implication

  forward-implication-is-coinhabited' : is-coinhabited A B → A → is-inhabited B
  forward-implication-is-coinhabited' e a =
    forward-implication e (unit-trunc-Prop a)

  backward-implication-is-coinhabited :
    is-coinhabited A B → is-inhabited B → is-inhabited A
  backward-implication-is-coinhabited = backward-implication

  backward-implication-is-coinhabited' : is-coinhabited A B → B → is-inhabited A
  backward-implication-is-coinhabited' e b =
    backward-implication e (unit-trunc-Prop b)
```

### Every type is coinhabited with itself

```agda
module _
  {l : Level} (A : UU l)
  where

  is-reflexive-is-coinhabited : is-coinhabited A A
  is-reflexive-is-coinhabited = id-iff
```

### Coinhabitedness is a transitive relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-transitive-is-coinhabited :
    is-coinhabited B C → is-coinhabited A B → is-coinhabited A C
  is-transitive-is-coinhabited = _∘iff_
```

### Coinhabitedness is a symmetric relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-symmetric-is-coinhabited : is-coinhabited A B → is-coinhabited B A
  is-symmetric-is-coinhabited = inv-iff
```

## See also

- [Mere logical equivalence of types](foundation.mere-logical-equivalences.md)
  is a related but stronger notion than coinhabitedness.
