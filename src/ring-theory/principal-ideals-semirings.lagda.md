# Principal ideals of semirings

```agda
module ring-theory.principal-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.existential-quantification
open import foundation.universe-levels

open import ring-theory.ideals-generated-by-elements-semirings
open import ring-theory.ideals-semirings
open import ring-theory.semirings
```

</details>

## Idea

An [ideal](ring-theory.semirings.md) $I$ of a [semiring](ring-theory.semirings.md) $R$ is said to be a {{#concept "principal ideal" Disambiguation="semiring" Agda=is-principal-ideal-Semiring}} if there exists an element $a \in I$ so that every element $I$ is a linear combination of $a$s {{#cite golan1999}}. In other words, the ideal $I$ is principal if there exists an element $a$ such that for every element $b$ the [logical equivalence](foundation.logical-equivalences.md)

$$
  b ∈ I \Leftrightarrow \exists_{(x_1,y_1),\ldots,(x_n,y_n):R^2)} x_1 ay_1+\cdots x_nay_n = b.
$$

holds.

We note that principal ideals need not be [subtractive](ring-theory.subtractive-ideals-semirings.md). For instance, consider the ring `R := {0,1,∞}` with addition and multiplication tables given by

```text
  + | 0 1 ∞    × | 0 1 ∞
  ---------    ---------
  0 | 0 1 ∞    0 | 0 0 0
  1 | 1 ∞ ∞    1 | 0 1 ∞
  ∞ | ∞ ∞ ∞    ∞ | 0 ∞ ∞
```

Then the ideal `⟨∞⟩ = {0,∞}` is principal, but it is not subtractive, since two out of three of `∞ + 1 = ∞` are in the ideal `⟨∞⟩`, but `1 ∉ ⟨∞⟩`.

## Definitions

### The predicate of being a principal ideal of a semiring

We define principal ideals to be those ideals `I` for which there exists an element `a` such that `⟨a⟩` and `I` have the same elements.

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : ideal-Semiring l2 R)
  where

  is-principal-ideal-Semiring : UU (l1 ⊔ l2)
  is-principal-ideal-Semiring =
    exists-structure
      ( type-Semiring R)
      ( λ a → has-same-elements-ideal-Semiring R (ideal-element-Semiring R a) I)
```

## See also

- [Principal semirings](ring-theory.principal-semirings.md)
- [Subtractively principal semirings](ring-theory.subtractively-principal-semirings.md)
- [Principally subtractive semirings](ring-theory.principally-subtractive-semirings.md)

## References

{{#bibliography}}
