# The precategory of finite total orders

```agda
{-# OPTIONS --cubical-compatible #-}

module order-theory.precategory-of-finite-total-orders where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategories
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.universe-levels

open import order-theory.finite-total-orders
open import order-theory.precategory-of-posets
```

</details>

## Idea

The **(large) precategory of finite total orders** consists of
[finite total orders](order-theory.finite-total-orders.md) and
[order preserving maps](order-theory.order-preserving-maps-posets.md) and is
exhibited as a
[full subprecategory](category-theory.full-large-subprecategories.md) of the
[precategory of posets](order-theory.precategory-of-posets.md).

## Definitions

### The large precategory of finite total orders

```agda
parametric-Total-Order-𝔽-Full-Large-Subprecategory :
  (α β : Level → Level) →
  Full-Large-Subprecategory
    ( λ l → α l ⊔ β l)
    ( parametric-Poset-Large-Precategory α β)
parametric-Total-Order-𝔽-Full-Large-Subprecategory α β =
  is-finite-total-order-Poset-Prop

Total-Order-𝔽-Large-Precategory : Large-Precategory lsuc (_⊔_)
Total-Order-𝔽-Large-Precategory =
  large-precategory-Full-Large-Subprecategory
    ( Poset-Large-Precategory)
    ( parametric-Total-Order-𝔽-Full-Large-Subprecategory (λ l → l) (λ l → l))
```

### The precategory of finite total orders of universe level `l`

```agda
Total-Order-𝔽-Precategory : (l : Level) → Precategory (lsuc l) l
Total-Order-𝔽-Precategory =
  precategory-Large-Precategory Total-Order-𝔽-Large-Precategory
```
