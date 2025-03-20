# Mere lifting properties

```agda
open import foundation.function-extensionality-axiom

module
  orthogonal-factorization-systems.mere-lifting-properties
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions funext
open import foundation.surjective-maps funext
open import foundation.universe-levels

open import orthogonal-factorization-systems.pullback-hom funext
```

</details>

## Idea

Given two maps, `f : A → X` and `g : B → Y`, we say that `f` has the **mere left
lifting property** with respect to `g` and that `g` has the **mere right lifting
property** with respect to `f` if the
[pullback-hom](orthogonal-factorization-systems.pullback-hom.md) is
[surjective](foundation.surjective-maps.md). This means that the type of
[lifting operations](orthogonal-factorization-systems.lifting-operations.md)
between `f` and `g` is merely [inhabited](foundation.inhabited-types.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  mere-diagonal-lift : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  mere-diagonal-lift = is-surjective (pullback-hom f g)
```

## Properties

### Mere lifting properties are properties

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  is-prop-mere-diagonal-lift : is-prop (mere-diagonal-lift f g)
  is-prop-mere-diagonal-lift = is-prop-is-surjective (pullback-hom f g)

  mere-diagonal-lift-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  mere-diagonal-lift-Prop = is-surjective-Prop (pullback-hom f g)
```
