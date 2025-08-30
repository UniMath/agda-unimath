# Products of Dirichlet series of species of finite inhabited types

```agda
module species.products-dirichlet-series-species-of-finite-inhabited-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.universe-levels

open import species.dirichlet-series-species-of-finite-inhabited-types
open import species.species-of-finite-inhabited-types
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of Caucy series of species of finite inhabited types" Agda=product-dirichlet-series-species-Inhabited-Finite-Type}}
of two
[Dirichlet series](species.dirichlet-series-species-of-finite-inhabited-types.md)
of
[species of types in subuniverses](species.species-of-finite-inhabited-types.md)
is just the pointwise [product](foundation.cartesian-product-types.md).

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
