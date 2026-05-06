# Principal left ideals of semirings

```agda
module ring-theory.principal-left-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.existential-quantification
open import foundation.universe-levels

open import ring-theory.left-ideals-generated-by-elements-semirings
open import ring-theory.left-ideals-semirings
open import ring-theory.semirings
```

</details>

## Idea

A [left ideal](ring-theory.semirings.md) $I$ of a [semiring](ring-theory.semirings.md) $R$ is said to be a {{#concept "principal left ideal" Disambiguation="semiring" Agda=is-principal-left-ideal-Semiring}} if there exists an element $a \in I$ so that every element $I$ is a linear combination of $a$s {{#cite golan1999}}. In other words, the left ideal $I$ is principal if there exists an element $a$ such that for every element $b$ the [logical equivalence](foundation.logical-equivalences.md)

$$
  b ∈ I \Leftrightarrow \exists_{(x_1,y_1),\ldots,(x_n,y_n):R^2)} x_1 ay_1+\cdots x_nay_n = b.
$$

holds.

We note that principal left ideals need not be [subtractive](ring-theory.subtractive-left-ideals-semirings.md). For instance, consider the ring `R := {0,1,∞}` with addition and multiplication tables given by

```text
  + | 0 1 ∞    × | 0 1 ∞
  ---------    ---------
  0 | 0 1 ∞    0 | 0 0 0
  1 | 1 ∞ ∞    1 | 0 1 ∞
  ∞ | ∞ ∞ ∞    ∞ | 0 ∞ ∞
```

Then the left ideal `⟨∞⟩ = {0,∞}` is principal, but it is not subtractive, since two out of three of `∞ + 1 = ∞` are in the left ideal `⟨∞⟩`, but `1 ∉ ⟨∞⟩`.

## Definitions

### The predicate of being a principal left ideal of a semiring

We define principal left ideals to be those left ideals `I` for which there exists an element `a` such that `⟨a⟩` and `I` have the same elements.

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : left-ideal-Semiring l2 R)
  where

  is-principal-left-ideal-Semiring : UU (l1 ⊔ l2)
  is-principal-left-ideal-Semiring =
    exists-structure
      ( type-Semiring R)
      ( λ a →
        has-same-elements-left-ideal-Semiring R
          ( left-ideal-element-Semiring R a)
          ( I))
```

## References

{{#bibliography}}
