# Alkanes

```agda
open import foundation.function-extensionality-axiom

module
  organic-chemistry.alkanes
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import organic-chemistry.hydrocarbons funext
open import organic-chemistry.saturated-carbons funext
```

</details>

## Idea

An **alkane** is a hydrocarbon that only has saturated carbons, i.e., it does
not have any double or triple carbon-carbon bonds.

## Definition

```agda
is-alkane-hydrocarbon : {l1 l2 : Level} → hydrocarbon l1 l2 → UU (l1 ⊔ l2)
is-alkane-hydrocarbon H =
  (c : vertex-hydrocarbon H) → is-saturated-carbon-hydrocarbon H c
```
