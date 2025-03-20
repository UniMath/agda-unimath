# The precategory of decidable total orders

```agda
open import foundation.function-extensionality-axiom

module
  order-theory.precategory-of-decidable-total-orders
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategories funext
open import category-theory.large-precategories funext
open import category-theory.precategories funext

open import foundation.universe-levels

open import order-theory.decidable-total-orders funext
open import order-theory.precategory-of-posets funext
```

</details>

## Idea

The **(large) precategory of decidable total orders** consists of
[decidable total orders](order-theory.decidable-total-orders.md) and
[order preserving maps](order-theory.order-preserving-maps-posets.md) and is
exhibited as a
[full subprecategory](category-theory.full-large-subprecategories.md) of the
[precategory of posets](order-theory.precategory-of-posets.md).

## Definitions

### The large precategory of decidable total orders

```agda
parametric-Decidable-Total-Order-Full-Large-Subprecategory :
  (α β : Level → Level) →
  Full-Large-Subprecategory
    ( λ l → α l ⊔ β l)
    ( parametric-Poset-Large-Precategory α β)
parametric-Decidable-Total-Order-Full-Large-Subprecategory α β =
  is-decidable-total-prop-Poset

Decidable-Total-Order-Large-Precategory :
  Large-Precategory lsuc (_⊔_)
Decidable-Total-Order-Large-Precategory =
  large-precategory-Full-Large-Subprecategory
    ( Poset-Large-Precategory)
    ( parametric-Decidable-Total-Order-Full-Large-Subprecategory
      ( λ l → l)
      ( λ l → l))
```

### The precategory of total orders at a universe level

```agda
Decidable-Total-Order-Precategory : (l : Level) → Precategory (lsuc l) l
Decidable-Total-Order-Precategory =
  precategory-Large-Precategory Decidable-Total-Order-Large-Precategory
```
