# Products of Dirichlet series of species of finite inhabited types

```agda
open import foundation.function-extensionality-axiom

module
  species.products-dirichlet-series-species-of-finite-inhabited-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext
open import foundation.universe-levels

open import species.dirichlet-series-species-of-finite-inhabited-types funext
open import species.species-of-finite-inhabited-types funext
```

</details>

## Idea

The product of two Dirichlet series is the pointwise product.

## Definition

```agda
product-dirichlet-series-species-Inhabited-Finite-Type :
  {l1 l2 l3 l4 : Level} → species-Inhabited-Finite-Type l1 l2 →
  species-Inhabited-Finite-Type l1 l3 →
  UU l4 → UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
product-dirichlet-series-species-Inhabited-Finite-Type S T X =
  dirichlet-series-species-Inhabited-Finite-Type S X ×
  dirichlet-series-species-Inhabited-Finite-Type T X
```
