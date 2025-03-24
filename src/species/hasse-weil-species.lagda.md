# Hasse-Weil species

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module species.hasse-weil-species
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.commutative-finite-rings funext univalence truncations
open import finite-algebra.products-commutative-finite-rings funext univalence truncations

open import foundation.cartesian-product-types funext univalence
open import foundation.equivalences funext
open import foundation.universe-levels

open import univalent-combinatorics.finite-types funext univalence truncations
```

</details>

## Idea

Let `S` be a function from the type of commutative finite rings to the finite
types that preserves cartesian products. The **Hasse-Weil species** is a species
of finite inhabited types defined for any finite inhabited type `k` as

```text
Σ (p : structure-semisimple-commutative-ring-Finite-Type k) ; S (commutative-finite-ring-finite-semisimple-commutative-ring-structure-semisimple-commutative-ring-Finite-Type k p)
```

## Definitions

```agda
is-closed-under-products-function-from-Finite-Commutative-Ring :
  {l1 l2 : Level} →
  (Finite-Commutative-Ring l1 → Finite-Type l2) →
  UU (lsuc l1 ⊔ l2)
is-closed-under-products-function-from-Finite-Commutative-Ring {l1} {l2} S =
  (R1 R2 : Finite-Commutative-Ring l1) →
  ( type-Finite-Type (S (product-Finite-Commutative-Ring R1 R2))) ≃
  ( type-Finite-Type (S R1) × type-Finite-Type (S R2))
```

```text
module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (S : Finite-Commutative-Ring l1 → Finite-Type l2)
  (C : is-closed-under-products-function-from-Finite-Commutative-Ring S)
  where

  hasse-weil-species-Inhabited-Finite-Type :
    species-Inhabited-Finite-Type l1 (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  hasse-weil-species-Inhabited-Finite-Type ( k , (f , i)) =
    Σ-Finite-Type {!!}
        ( λ p →
          S
            ( commutative-finite-ring-Semisimple-Finite-Commutative-Ring
              ( finite-semisimple-commutative-ring-structure-semisimple-commutative-ring-Finite-Type
                ( l3)
                ( l4)
                ( k , f)
                ( p))))
```
