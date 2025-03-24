# The unit of Cauchy composition of species of types in subuniverses

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module species.unit-cauchy-composition-species-of-types-in-subuniverses
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.global-subuniverses funext univalence
open import foundation.subuniverses funext univalence
open import foundation.universe-levels

open import species.species-of-types-in-subuniverses funext univalence
```

</details>

## Idea

Given a global subuniverse closed under `is-contr`, we define the unit of the
Cauchy composition of species of types in a subuniverse by

```text
  X ↦ is-contr X.
```

## Definition

```agda
module _
  {l1 l2 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (C4 :
    is-closed-under-is-contr-subuniverses P
      ( subuniverse-global-subuniverse Q l1))
  where

  cauchy-composition-unit-species-subuniverse :
    species-subuniverse P (subuniverse-global-subuniverse Q l1)
  cauchy-composition-unit-species-subuniverse X =
    (is-contr (inclusion-subuniverse P X) , C4 X)
```
