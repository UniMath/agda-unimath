# Initial rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.initial-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.initial-objects-large-categories funext univalence truncations

open import foundation.universe-levels

open import ring-theory.category-of-rings funext univalence truncations
open import ring-theory.rings funext univalence truncations
```

</details>

## Idea

The **initial ring** is a [ring](ring-theory.rings.md) `R` that satisfies the
universal property that for any ring `S`, the type

```text
  hom-Ring R S
```

of [ring homomorphisms](ring-theory.homomorphisms-rings.md) from `R` to `S` is
contractible.

In
[`elementary-number-theory.ring-of-integers`](elementary-number-theory.ring-of-integers.md)
we will show that `ℤ` is the initial ring.

## Definitions

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-initial-Ring : UUω
  is-initial-Ring = is-initial-obj-Large-Category Ring-Large-Category R
```
