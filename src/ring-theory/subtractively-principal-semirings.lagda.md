# Subtractively principal semirings

```agda
module ring-theory.subtractively-principal-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import ring-theory.principal-ideals-semirings
open import ring-theory.semirings
open import ring-theory.subtractive-ideals-semirings
```

</details>

## Idea

A [semiring](ring-theory.semirings.md) `R` is said to be {{#concept "subtractively principal" Disambiguation="semiring" Agda=is-subtractively-principal-Semiring}} if every [subtractive ideal](ring-theory.subtractive-ideals-semirings.md) is [principal](ring-theory.principal-ideals-semirings.md).

## Definitions

### The predicate of being a subtractively principal semiring

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-subtractively-principal-Semiring-Level :
    (l : Level) → UU (l1 ⊔ lsuc l)
  is-subtractively-principal-Semiring-Level l =
    (I : subtractive-ideal-Semiring l R) →
    is-principal-ideal-Semiring R (ideal-subtractive-ideal-Semiring R I)

  is-subtractively-principal-Semiring :
    UUω
  is-subtractively-principal-Semiring =
    {l : Level} → is-subtractively-principal-Semiring-Level l
```
