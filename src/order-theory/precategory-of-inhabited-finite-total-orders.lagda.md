# The precategory of inhabited finite total orders

```agda
module order-theory.precategory-of-inhabited-finite-total-orders where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.cartesian-product-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.finite-total-orders
open import order-theory.inhabited-finite-total-orders
open import order-theory.precategory-of-posets
open import order-theory.precategory-of-total-orders
```

</details>

## Idea

The **(large) precategory of inhabited finite total orders** consists of
[inhabited finite total orders](order-theory.inhabited-finite-total-orders.md)
and [order preserving maps](order-theory.order-preserving-maps-posets.md) and is
exhibited as a
[full subprecategory](category-theory.full-large-subprecategories.md) of the
[precategory of posets](order-theory.precategory-of-posets.md).

## Definitions

### The large precategory of inhabited finite total orders

```agda
parametric-Inhabited-Total-Order-𝔽-Full-Large-Subprecategory :
  (α β : Level → Level) →
  Full-Large-Subprecategory
    ( λ l → α l ⊔ β l)
    ( parametric-Poset-Large-Precategory α β)
parametric-Inhabited-Total-Order-𝔽-Full-Large-Subprecategory α β =
  is-inhabited-finite-total-order-Poset-Prop

Inhabited-Total-Order-𝔽-Large-Precategory : Large-Precategory lsuc (_⊔_)
Inhabited-Total-Order-𝔽-Large-Precategory =
  large-precategory-Full-Large-Subprecategory
    ( Poset-Large-Precategory)
    ( parametric-Inhabited-Total-Order-𝔽-Full-Large-Subprecategory
      ( λ l → l)
      ( λ l → l))
```

### The precategory of finite total orders of universe level `l`

```agda
Inhabited-Total-Order-𝔽-Precategory : (l : Level) → Precategory (lsuc l) l
Inhabited-Total-Order-𝔽-Precategory =
  precategory-Large-Precategory Inhabited-Total-Order-𝔽-Large-Precategory
```
