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

We say a
[(small) function class](orthogonal-factorization-systems.function-classes.md)
is **wide** if it contains all [equivalences](foundation-core.equivalences.md)
and is composition closed. This means it is morally a wide sub-∞-category of the
∞-category of types at a fixed universe level.

## Definition

### The predicate on a small function class of being wide

```agda
module _
  {l1 l2 : Level} (P : function-class l1 l1 l2)
  where

  is-wide-function-class : UU (lsuc l1 ⊔ l2)
  is-wide-function-class =
    ( has-equivalences-function-class P) ×
    ( is-closed-under-composition-function-class P)

  is-wide-function-class-Prop : Prop (lsuc l1 ⊔ l2)
  is-wide-function-class-Prop =
    prod-Prop
      ( has-equivalences-function-class-Prop P)
      ( is-closed-under-composition-function-class-Prop P)

  is-prop-is-wide-function-class : is-prop is-wide-function-class
  is-prop-is-wide-function-class = is-prop-type-Prop is-wide-function-class-Prop

  has-equivalences-is-wide-function-class :
    is-wide-function-class → has-equivalences-function-class P
  has-equivalences-is-wide-function-class = pr1

  is-closed-under-composition-is-wide-function-class :
    is-wide-function-class → is-closed-under-composition-function-class P
  is-closed-under-composition-is-wide-function-class = pr2
```

### The type of small wide function classes

```agda
wide-function-class : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
wide-function-class l1 l2 =
  Σ (function-class l1 l1 l2) (is-wide-function-class)

module _
  {l1 l2 : Level} (P : wide-function-class l1 l2)
  where

  function-class-wide-function-class : function-class l1 l1 l2
  function-class-wide-function-class = pr1 P

  is-wide-wide-function-class :
    is-wide-function-class function-class-wide-function-class
  is-wide-wide-function-class = pr2 P

  has-equivalences-wide-function-class :
    has-equivalences-function-class function-class-wide-function-class
  has-equivalences-wide-function-class =
    has-equivalences-is-wide-function-class
      ( function-class-wide-function-class)
      ( is-wide-wide-function-class)

  is-closed-under-composition-wide-function-class :
    is-closed-under-composition-function-class
      ( function-class-wide-function-class)
  is-closed-under-composition-wide-function-class =
    is-closed-under-composition-is-wide-function-class
      ( function-class-wide-function-class)
      ( is-wide-wide-function-class)
```
