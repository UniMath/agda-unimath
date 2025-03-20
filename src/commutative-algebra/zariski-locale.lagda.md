# The Zariski locale

```agda
open import foundation.function-extensionality-axiom

module
  commutative-algebra.zariski-locale
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings funext
open import commutative-algebra.intersections-radical-ideals-commutative-rings funext
open import commutative-algebra.joins-radical-ideals-commutative-rings funext
open import commutative-algebra.poset-of-radical-ideals-commutative-rings funext

open import foundation.universe-levels

open import order-theory.large-frames funext
open import order-theory.large-locales funext
```

</details>

## Idea

The **Zariski locale** of a
[commutative ring](commutative-algebra.commutative-rings.md) `A` is the
[large locale](order-theory.large-locales.md) consisting of
[radical ideals](commutative-algebra.radical-ideals-commutative-rings.md) of
`A`. Our proof of the fact that meets distribute over arbitrary joins uses the
fact that the intersection `I ∩ J` of radical ideals is equivalently described
as the radical ideal `√ IJ` of the
[product ideal](commutative-algebra.products-ideals-commutative-rings.md).

## Definition

### The Zariski frame

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  zariski-frame-Commutative-Ring :
    Large-Frame (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3) l1
  large-poset-Large-Frame
    zariski-frame-Commutative-Ring =
    radical-ideal-Commutative-Ring-Large-Poset A
  is-large-meet-semilattice-Large-Frame
    zariski-frame-Commutative-Ring =
    is-large-meet-semilattice-radical-ideal-Commutative-Ring A
  is-large-suplattice-Large-Frame zariski-frame-Commutative-Ring =
    is-large-suplattice-radical-ideal-Commutative-Ring A
  distributive-meet-sup-Large-Frame zariski-frame-Commutative-Ring =
    distributive-intersection-join-family-of-radical-ideals-Commutative-Ring A
```

### The Zariski locale

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  zariski-locale-Commutative-Ring :
    Large-Locale (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3) l1
  zariski-locale-Commutative-Ring = zariski-frame-Commutative-Ring A
```
