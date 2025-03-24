# The unit of Cauchy composition of types

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module species.unit-cauchy-composition-species-of-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types funext univalence
open import foundation.dependent-products-contractible-types funext
open import foundation.universe-levels

open import species.species-of-types funext univalence
```

</details>

## Idea

The **unit** of Cauchy composition of species of types is the species

```text
  X ↦ is-contr X.
```

## Definition

```agda
unit-species-types : {l1 : Level} → species-types l1 l1
unit-species-types = is-contr
```
