# The Zariski locale

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module commutative-algebra.zariski-locale where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.joins-ideals-commutative-rings
open import commutative-algebra.joins-radical-ideals-commutative-rings
open import commutative-algebra.products-of-radical-ideals-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings
open import commutative-algebra.radicals-of-ideals-commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
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
[product ideal](commutative-algebra.products-of-ideals-commutative-rings.md).

## Definition

### The Zariski locale

To do.
