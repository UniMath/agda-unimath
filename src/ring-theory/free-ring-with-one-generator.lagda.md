# The free ring with one generator

```agda
module ring-theory.free-ring-with-one-generator where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

The **free ring with one generator** is specified as a [ring](ring-theory.rings.md) `R` equipped with an element `g : R` such that for every ring `S` the map

```text
  hom-Ring R S → type-Ring S
```

given by evaluating at the element `g` is an equivalence. This property is also called the **universal property of the free ring with one generator**. In other words, the free ring with one generator is a representing object for the functor `S ↦ type-Ring S`. We will show that the ring `ℤ` of [integers](elementary-number-theory.commutative-ring-of-integers.md) equipped with the element `1 : ℤ` satisfies the universal property of the free ring with one generator.

## Definitions

### The universal property of the free ring with one generator

```agda
module _
  {l : Level} (R : Ring l) (g : type-Ring R)
  where
  
  universal-property-free-ring-with-one-generator : UUω
  universal-property-free-ring-with-one-generator = ?
```
