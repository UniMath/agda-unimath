# The free ring with one generator

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.free-rings-with-one-generator
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences funext
open import foundation.universe-levels

open import ring-theory.homomorphisms-rings funext univalence truncations
open import ring-theory.rings funext univalence truncations
```

</details>

## Idea

The **free ring with one generator** is specified as a
[ring](ring-theory.rings.md) `R` equipped with an element `g : R` such that for
every ring `S` the map

```text
  hom-set-Ring R S → type-Ring S
```

given by evaluating at the element `g` is an equivalence. This property is also
called the **universal property of the free ring with one generator**. In other
words, the free ring with one generator is a representing object for the functor
`S ↦ type-Ring S`.

We will show that the polynomial ring `ℤ[x]` of polynomials with
[integer](elementary-number-theory.ring-of-integers.md) coefficients satisfies
the universal property of the free ring with one generator.

## Definitions

### The universal property of the free ring with one generator

```agda
module _
  {l : Level} (R : Ring l) (g : type-Ring R)
  where

  is-free-ring-with-one-generator : UUω
  is-free-ring-with-one-generator =
    {l2 : Level} (S : Ring l2) → is-equiv (ev-element-hom-Ring R S g)
```
