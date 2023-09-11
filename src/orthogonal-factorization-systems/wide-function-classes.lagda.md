# Wide function classes

```agda
module orthogonal-factorization-systems.wide-function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.function-classes
```

</details>

## Idea

We say a [function class](orthogonal-factorization-systems.function-classes.md)
is **wide** if it contains all [equivalences](foundation-core.equivalences.md)
and is [composition](foundation.function-types.md) closed. This means it is
morally a wide sub-∞-category of the ∞-category of types.

## Definition

```agda
is-wide-function-class :
  {l1 l2 : Level} → function-class l1 l1 l2 → UU (lsuc l1 ⊔ l2)
is-wide-function-class c =
  ( has-equivalences-function-class c) ×
  ( is-closed-under-composition-function-class c)

wide-function-class : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
wide-function-class l1 l2 =
  Σ (function-class l1 l1 l2) (is-wide-function-class)
```

## Properties

```agda
is-wide-function-class-Prop :
  {l1 l2 : Level} → function-class l1 l1 l2 → Prop (lsuc l1 ⊔ l2)
is-wide-function-class-Prop c =
  prod-Prop
    ( has-equivalences-function-class-Prop c)
    ( is-closed-under-composition-function-class-Prop c)

is-prop-is-wide-function-class :
  {l1 l2 : Level} (c : function-class l1 l1 l2) →
  is-prop (is-wide-function-class c)
is-prop-is-wide-function-class = is-prop-type-Prop ∘ is-wide-function-class-Prop
```
