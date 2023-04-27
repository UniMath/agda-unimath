# The plus-principle

```agda
module synthetic-homotopy-theory.plus-principle where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-types
open import foundation.contractible-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.acyclic-types
```

</details>

## Idea

The **plus-principle** asserts that any acyclic 1-connected type is
contractible.

## Definition

```agda
plus-principle : (l : Level) → UU (lsuc l)
plus-principle l =
  (A : UU l) → is-acyclic A → is-connected one-𝕋 A → is-contr A
```
