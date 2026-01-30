# The precategory of total orders

```agda
module order-theory.precategory-of-total-orders where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import order-theory.precategory-of-posets
open import order-theory.total-orders
```

</details>

## Idea

The **(large) precategory of total orders** consists of
[total orders](order-theory.total-orders.md) and
[order preserving maps](order-theory.order-preserving-maps-posets.md) and is
exhibited as a
[full subprecategory](category-theory.full-large-subprecategories.md) of the
[precategory of posets](order-theory.precategory-of-posets.md).

## Definitions

### The large precategory of total orders

```agda
parametric-Total-Order-Full-Large-Subprecategory :
  (α β : Level → Level) →
  Full-Large-Subprecategory
    ( λ l → α l ⊔ β l)
    ( parametric-Poset-Large-Precategory α β)
parametric-Total-Order-Full-Large-Subprecategory α β = is-total-prop-Poset

Total-Order-Large-Precategory :
  Large-Precategory lsuc (_⊔_)
Total-Order-Large-Precategory =
  large-precategory-Full-Large-Subprecategory
    ( Poset-Large-Precategory)
    ( parametric-Total-Order-Full-Large-Subprecategory (λ l → l) (λ l → l))
```

### The precategory of total orders at a universe level

```agda
Total-Order-Precategory : (l : Level) → Precategory (lsuc l) l
Total-Order-Precategory =
  precategory-Large-Precategory Total-Order-Large-Precategory
```
