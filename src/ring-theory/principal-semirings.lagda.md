# Principal semirings

```agda
module ring-theory.principal-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import ring-theory.ideals-semirings
open import ring-theory.principal-ideals-semirings
open import ring-theory.semirings
```

</details>

## Idea

A [semiring](ring-theory.semirings.md) `R` is said to be {{#concept "principal" Disambiguation="semiring" Agda=is-principal-Semiring}} if every [ideal](ring-theory.ideals-semirings.md) is [principal](ring-theory.principal-ideals-semirings.md).

## Definitions

### The predicate of being a principal semiring

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-principal-Semiring-Level :
    (l : Level) → UU (l1 ⊔ lsuc l)
  is-principal-Semiring-Level l =
    (I : ideal-Semiring l R) → is-principal-ideal-Semiring R I

  is-principal-Semiring :
    UUω
  is-principal-Semiring =
    {l : Level} → is-principal-Semiring-Level l
```
