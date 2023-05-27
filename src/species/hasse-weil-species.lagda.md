# Hasse-Weil species

```agda
module species.hasse-weil-species where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.commutative-finite-rings
open import finite-algebra.products-commutative-finite-rings

open import foundation.cartesian-product-types
open import foundation.equivalences
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
```

</details>

## Idea

Let `S` be a function from the type of commutative finite rings to the finite
types that preserves cartesian products. The **Hasse-Weil species** is a species
of finite inhabited types defined for any finite inhabited type `k` as

```text
Σ (p : structure-semisimple-commutative-ring-𝔽 k) ; S (commutative-finite-ring-compute-structure-semisimple-commutative-ring-𝔽 k p)
```

## Definitions

```agda
is-closed-under-products-function-from-Commutative-Ring-𝔽 :
  {l1 l2 : Level} → (Commutative-Ring-𝔽 l1 → 𝔽 l2) → UU (lsuc l1 ⊔ l2)
is-closed-under-products-function-from-Commutative-Ring-𝔽 {l1} {l2} S =
  (R1 R2 : Commutative-Ring-𝔽 l1) →
  type-𝔽 (S (prod-Commutative-Ring-𝔽 R1 R2)) ≃ (type-𝔽 (S R1) × type-𝔽 (S R2))

module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (S : Commutative-Ring-𝔽 l1 → 𝔽 l2)
  (C : is-closed-under-products-function-from-Commutative-Ring-𝔽 S)
  where

--   hasse-weil-species-Inhabited-𝔽 :
--     species-Inhabited-𝔽 l1 (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
--   hasse-weil-species-Inhabited-𝔽 ( k , (f , i)) =
--     Σ-𝔽 {!!}
--         ( λ p →
--           S
--             ( commutative-finite-ring-Semisimple-Commutative-Ring-𝔽
--               ( compute-structure-semisimple-commutative-ring-𝔽
--                 ( l3)
--                 ( l4)
--                 ( k , f)
--                 ( p))))
```
