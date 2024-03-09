# The homotopy preorder of types

```agda
module
  foundation.homotopy-preorder-of-types
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.implication
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

The {{#concept "homotopy preorder of types" Agda=Type-Large-Preorder}} is the
[(large) preorder](order-theory.large-preorders.md) whose objects are types, and
whose ordering relation is defined by [implications](foundation.implication.md),
i.e. by the [propositional truncation](foundation.propositional-truncations.md)
of the function types:

```text
  A ≤ B := ║(A → B)║₋₁.
```

## Definitions

### The large homotopy preorder of types

```agda
Homotopy-Type-Large-Preorder : Large-Preorder lsuc (_⊔_)
Homotopy-Type-Large-Preorder =
  λ where
  .type-Large-Preorder l → UU l
  .leq-prop-Large-Preorder → implication-prop
  .refl-leq-Large-Preorder → id-implication
  .transitive-leq-Large-Preorder X Y Z → comp-implication
```

### The small homotopy preorder of types

```agda
Homotopy-Type-Preorder : (l : Level) → Preorder (lsuc l) l
Homotopy-Type-Preorder = preorder-Large-Preorder Homotopy-Type-Large-Preorder
```
