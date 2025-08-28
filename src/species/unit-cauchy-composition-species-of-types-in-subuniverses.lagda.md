# The unit of Cauchy composition of species of types in subuniverses

```agda
module species.unit-cauchy-composition-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.global-subuniverses
open import foundation.subuniverses
open import foundation.universe-levels

open import species.species-of-types-in-subuniverses
```

</details>

## Idea

Given a [global subuniverse](foundation.global-subuniverses.md) closed under
`is-contr`, we define the unit of the
[Cauchy composition](species.cauchy-composition-species-of-types-in-subuniverses.md)
of
[species of types in a subuniverse](species.species-of-types-in-subuniverses.md)
by

```text
  X ↦ is-contr X.
```

## Definition

```agda
module _
  {α : Level → Level} {l1 l2 : Level}
  (P : subuniverse l1 l2) (Q : global-subuniverse α)
  (C4 :
    is-closed-under-is-contr-subuniverses P
      ( subuniverse-global-subuniverse Q l1))
  where

  cauchy-composition-unit-species-subuniverse :
    species-subuniverse P (subuniverse-global-subuniverse Q l1)
  cauchy-composition-unit-species-subuniverse X =
    (is-contr (inclusion-subuniverse P X) , C4 X)
```
