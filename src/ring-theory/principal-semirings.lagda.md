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

**Note.** This notion is too strong, constructively. A better approach could be as follows. Consider an ideal `I`, and consider the poset `P` of principal ideals contained in `I`. We could ask:
- A Bézout condition: For any two principal ideals `J, J' ⊆ I`, there is a principal ideal `K ⊆ I` such that `J, J' ⊆ K`.
- A stronger condition: For any subset `S ⊆ I` there is a principal ideal K ⊆ I such that `S ⊆ K ⊆ I`.

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
