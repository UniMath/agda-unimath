# Cartesian product types

```agda
module foundation.cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.cartesian-product-types public

open import foundation.subuniverses

open import foundation-core.universe-levels
```

</details>

## Definitions

### Subuniverses closed under cartesian product types

```agda
is-closed-under-products-subuniverses :
  {l1 l2 l3 l4 l5 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4)
  (R : subuniverse (l1 ⊔ l3) l5) → UU (lsuc l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
is-closed-under-products-subuniverses {l1} {l2} {l3} P Q R =
  {X : UU l1} {Y : UU l3} →
  is-in-subuniverse P X → is-in-subuniverse Q Y → is-in-subuniverse R (X × Y)

is-closed-under-products-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU (lsuc l1 ⊔ l2)
is-closed-under-products-subuniverse P =
  is-closed-under-products-subuniverses P P P
```
