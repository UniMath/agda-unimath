# Lower bounds in posets

```agda
open import foundation.function-extensionality-axiom

module
  order-theory.lower-bounds-posets
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions funext
open import foundation.universe-levels

open import order-theory.posets funext
```

</details>

## Idea

A **lower bound** of two elements `a` and `b` in a poset `P` is an element `x`
such that both `x ≤ a` and `x ≤ b` hold. Similarly, a **lower bound** of a
family `a : I → P` of elements in `P` is an element `x` such that `x ≤ a i`
holds for every `i : I`.

## Definitions

### Binary lower bounds

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (a b x : type-Poset P)
  where

  is-binary-lower-bound-Poset-Prop : Prop l2
  is-binary-lower-bound-Poset-Prop =
    product-Prop (leq-prop-Poset P x a) (leq-prop-Poset P x b)

  is-binary-lower-bound-Poset : UU l2
  is-binary-lower-bound-Poset =
    type-Prop is-binary-lower-bound-Poset-Prop

  is-prop-is-binary-lower-bound-Poset : is-prop is-binary-lower-bound-Poset
  is-prop-is-binary-lower-bound-Poset =
    is-prop-type-Prop is-binary-lower-bound-Poset-Prop

module _
  {l1 l2 : Level} (P : Poset l1 l2) {a b x : type-Poset P}
  (H : is-binary-lower-bound-Poset P a b x)
  where

  leq-left-is-binary-lower-bound-Poset : leq-Poset P x a
  leq-left-is-binary-lower-bound-Poset = pr1 H

  leq-right-is-binary-lower-bound-Poset : leq-Poset P x b
  leq-right-is-binary-lower-bound-Poset = pr2 H
```

### Lower bounds of families of elements

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} (x : I → type-Poset P)
  where

  is-lower-bound-family-of-elements-prop-Poset : type-Poset P → Prop (l2 ⊔ l3)
  is-lower-bound-family-of-elements-prop-Poset z =
    Π-Prop I (λ i → leq-prop-Poset P z (x i))

  is-lower-bound-family-of-elements-Poset : type-Poset P → UU (l2 ⊔ l3)
  is-lower-bound-family-of-elements-Poset z =
    type-Prop (is-lower-bound-family-of-elements-prop-Poset z)

  is-prop-is-lower-bound-family-of-elements-Poset :
    (z : type-Poset P) → is-prop (is-lower-bound-family-of-elements-Poset z)
  is-prop-is-lower-bound-family-of-elements-Poset z =
    is-prop-type-Prop (is-lower-bound-family-of-elements-prop-Poset z)
```

## Properties

### Any element less than a lower bound of `a` and `b` is a lower bound of `a` and `b`

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {a b x : type-Poset P}
  (H : is-binary-lower-bound-Poset P a b x)
  where

  is-binary-lower-bound-leq-Poset :
    {y : type-Poset P} →
    leq-Poset P y x → is-binary-lower-bound-Poset P a b y
  pr1 (is-binary-lower-bound-leq-Poset K) =
    transitive-leq-Poset P _ x a
      ( leq-left-is-binary-lower-bound-Poset P H)
      ( K)
  pr2 (is-binary-lower-bound-leq-Poset K) =
    transitive-leq-Poset P _ x b
      ( leq-right-is-binary-lower-bound-Poset P H)
      ( K)
```

### Any element less than a lower bound of a family of elements `a` is a lower bound of `a`

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} {a : I → type-Poset P}
  {x : type-Poset P} (H : is-lower-bound-family-of-elements-Poset P a x)
  where

  is-lower-bound-family-of-elements-leq-Poset :
    {y : type-Poset P} → leq-Poset P y x →
    is-lower-bound-family-of-elements-Poset P a y
  is-lower-bound-family-of-elements-leq-Poset K i =
    transitive-leq-Poset P _ x (a i) (H i) K
```
