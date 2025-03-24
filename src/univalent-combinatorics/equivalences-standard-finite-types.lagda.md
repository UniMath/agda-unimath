# Equivalences between standard finite types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module univalent-combinatorics.equivalences-standard-finite-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.exponentiation-natural-numbers funext univalence truncations
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types funext univalence
open import foundation.dependent-products-contractible-types funext
open import foundation.equivalences funext
open import foundation.functoriality-cartesian-product-types funext
open import foundation.type-arithmetic-empty-type funext univalence truncations
open import foundation.unit-type
open import foundation.universal-property-coproduct-types funext
open import foundation.universal-property-empty-type funext
open import foundation.universal-property-unit-type funext

open import univalent-combinatorics.cartesian-product-types funext univalence truncations
open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

We construct **equivalences** between (types built out of)
[standard finite types](univalent-combinatorics.standard-finite-types.md).

### The standard finite types are closed under function types

```agda
function-Fin :
  (k l : ℕ) → (Fin k → Fin l) ≃ Fin (exp-ℕ l k)
function-Fin zero-ℕ l =
  ( inv-left-unit-law-coproduct unit) ∘e
  ( equiv-is-contr (universal-property-empty' (Fin l)) is-contr-unit)
function-Fin (succ-ℕ k) l =
  ( product-Fin (exp-ℕ l k) l) ∘e
  ( equiv-product (function-Fin k l) (equiv-universal-property-unit (Fin l))) ∘e
  ( equiv-universal-property-coproduct (Fin l))

Fin-exp-ℕ : (k l : ℕ) → Fin (exp-ℕ l k) ≃ (Fin k → Fin l)
Fin-exp-ℕ k l = inv-equiv (function-Fin k l)
```
