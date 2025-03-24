# The homotopy preorder of types

```agda
module
  foundation.homotopy-preorder-of-types
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.empty-types funext univalence truncations
open import foundation.identity-types funext
open import foundation.mere-functions funext univalence truncations
open import foundation.propositional-truncations funext univalence
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.universe-levels

open import order-theory.large-preorders funext univalence truncations
open import order-theory.posets funext univalence truncations
open import order-theory.preorders funext univalence truncations
```

</details>

## Idea

The {{#concept "homotopy preorder of types" Agda=Homotopy-Type-Large-Preorder}}
is the [(large) preorder](order-theory.large-preorders.md) whose objects are
types, and whose ordering relation is defined by
[mere functions](foundation.mere-functions.md), i.e. by the
[propositional truncation](foundation.propositional-truncations.md) of the
function types:

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
  .leq-prop-Large-Preorder → prop-mere-function
  .refl-leq-Large-Preorder → refl-mere-function
  .transitive-leq-Large-Preorder X Y Z → transitive-mere-function
```

### The small homotopy preorder of types

```agda
Homotopy-Type-Preorder : (l : Level) → Preorder (lsuc l) l
Homotopy-Type-Preorder = preorder-Large-Preorder Homotopy-Type-Large-Preorder
```
