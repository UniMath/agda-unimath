# Magmas

```agda
module structured-types.magmas where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "magma" WD="magma" WDID=Q679903 Agda=Magma}} is a type
[equipped](foundation.structure.md) with a binary operation.

## Definition

```agda
Magma : (l : Level) → UU (lsuc l)
Magma l = Σ (UU l) (λ A → A → A → A)

module _
  {l : Level} (M : Magma l)
  where

  type-Magma : UU l
  type-Magma = pr1 M

  mul-Magma : type-Magma → type-Magma → type-Magma
  mul-Magma = pr2 M

  mul-Magma' : type-Magma → type-Magma → type-Magma
  mul-Magma' x y = mul-Magma y x
```

## Structures

### Unital magmas

```agda
is-unital-Magma : {l : Level} (M : Magma l) → UU l
is-unital-Magma M = is-unital (mul-Magma M)

Unital-Magma : (l : Level) → UU (lsuc l)
Unital-Magma l = Σ (Magma l) is-unital-Magma

magma-Unital-Magma :
  {l : Level} → Unital-Magma l → Magma l
magma-Unital-Magma M = pr1 M

is-unital-magma-Unital-Magma :
  {l : Level} (M : Unital-Magma l) → is-unital-Magma (magma-Unital-Magma M)
is-unital-magma-Unital-Magma M = pr2 M
```

### Semigroups

```agda
is-semigroup-Magma : {l : Level} → Magma l → UU l
is-semigroup-Magma M =
  (x y z : type-Magma M) →
  mul-Magma M (mul-Magma M x y) z ＝ mul-Magma M x (mul-Magma M y z)
```

### Commutative magmas

```agda
is-commutative-Magma : {l : Level} → Magma l → UU l
is-commutative-Magma M =
  (x y : type-Magma M) → mul-Magma M x y ＝ mul-Magma M y x
```

### The structure of a commutative monoid on magmas

```agda
is-commutative-monoid-Magma : {l : Level} → Magma l → UU l
is-commutative-monoid-Magma M =
  ((is-semigroup-Magma M) × (is-unital-Magma M)) × (is-commutative-Magma M)

unit-is-commutative-monoid-Magma :
  {l : Level} (M : Magma l) → is-commutative-monoid-Magma M → type-Magma M
unit-is-commutative-monoid-Magma M H = pr1 (pr2 (pr1 H))
```
