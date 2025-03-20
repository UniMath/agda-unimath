# The plus-principle

```agda
open import foundation.function-extensionality-axiom

module
  synthetic-homotopy-theory.plus-principle
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-types funext
open import foundation.contractible-types funext
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.acyclic-types funext
```

</details>

## Idea

The **plus-principle** asserts that any
[acyclic](synthetic-homotopy-theory.acyclic-types.md)
[1-connected type](foundation.connected-types.md) is
[contractible](foundation.contractible-types.md).

## Definition

```agda
plus-principle : (l : Level) → UU (lsuc l)
plus-principle l =
  (A : UU l) → is-acyclic A → is-connected one-𝕋 A → is-contr A
```
