# Principal right ideals of semirings

```agda
module ring-theory.principal-right-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.existential-quantification
open import foundation.universe-levels

open import ring-theory.right-ideals-generated-by-elements-semirings
open import ring-theory.right-ideals-semirings
open import ring-theory.semirings
```

</details>

## Idea

A [right ideal](ring-theory.semirings.md) $I$ of a [semiring](ring-theory.semirings.md) $R$ is said to be a {{#concept "principal right ideal" Disambiguation="semiring" Agda=is-principal-right-ideal-Semiring}} if there exists an element $a \in I$ so that every element $I$ is a linear combination of $a$s {{#cite golan1999}}. In other words, the right ideal $I$ is principal if there exists an element $a$ such that for every element $b$ the [logical equivalence](foundation.logical-equivalences.md)

$$
  b ∈ I \Rightrightarrow \exists_{(x_1,y_1),\ldots,(x_n,y_n):R^2)} x_1 ay_1+\cdots x_nay_n = b.
$$

holds.

We note that principal right ideals need not be [subtractive](ring-theory.subtractive-right-ideals-semirings.md). For instance, consider the ring `R := {0,1,∞}` with addition and multiplication tables given by

```text
  + | 0 1 ∞    × | 0 1 ∞
  ---------    ---------
  0 | 0 1 ∞    0 | 0 0 0
  1 | 1 ∞ ∞    1 | 0 1 ∞
  ∞ | ∞ ∞ ∞    ∞ | 0 ∞ ∞
```

Then the right ideal `⟨∞⟩ = {0,∞}` is principal, but it is not subtractive, since two out of three of `∞ + 1 = ∞` are in the right ideal `⟨∞⟩`, but `1 ∉ ⟨∞⟩`.

## Definitions

### The predicate of being a principal right ideal of a semiring

We define principal right ideals to be those right ideals `I` for which there exists an element `a` such that `⟨a⟩` and `I` have the same elements.

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : right-ideal-Semiring l2 R)
  where

  is-principal-right-ideal-Semiring : UU (l1 ⊔ l2)
  is-principal-right-ideal-Semiring =
    exists-structure
      ( type-Semiring R)
      ( λ a →
        has-same-elements-right-ideal-Semiring R
          ( right-ideal-element-Semiring R a)
          ( I))
```

## References

{{#bibliography}}
