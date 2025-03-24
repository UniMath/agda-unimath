# Scalar multiplication of vectors

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module linear-algebra.scalar-multiplication-vectors
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.functoriality-vectors funext univalence truncations
open import linear-algebra.vectors funext univalence truncations
```

</details>

## Idea

Any operation `B → A → A` for some type `B` of formal scalars induces an
operation `B → vec n A → vec n A`.

## Definition

```agda
scalar-mul-vec :
  {l1 l2 : Level} {B : UU l1} {A : UU l2} {n : ℕ} →
  (B → A → A) → B → vec A n → vec A n
scalar-mul-vec μ x = map-vec (μ x)
```
