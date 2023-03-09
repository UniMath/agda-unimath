# Wide function ∞-precategories

```agda
module orthogonal-factorization-systems.wide-function-precats where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.propositions
open import foundation.universe-levels
open import orthogonal-factorization-systems.function-classes
```

</details>

## Idea

A function class that contains the identities and is composition closed
is morally a wide subpre-∞-category of the ∞-category of small types.

```agda
is-wide-function-precat :
  {l1 l2 : Level} → function-class l1 l1 l2 → UU (lsuc l1 ⊔ l2)
is-wide-function-precat c =
  has-identity-maps-function-class c × is-composition-closed-function-class c

wide-function-precat : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
wide-function-precat l1 l2 =
  Σ (function-class l1 l1 l2) (is-wide-function-precat)
```

## Properties

```agda
is-wide-function-precat-Prop :
  {l1 l2 : Level} → function-class l1 l1 l2 → Prop (lsuc l1 ⊔ l2)
is-wide-function-precat-Prop c =
  prod-Prop
    ( has-identity-maps-function-class-Prop c)
    ( is-composition-closed-function-class-Prop c)

is-prop-is-wide-function-precat :
  {l1 l2 : Level} (c : function-class l1 l1 l2) → is-prop (is-wide-function-precat c)
is-prop-is-wide-function-precat = is-prop-type-Prop ∘ is-wide-function-precat-Prop
```
