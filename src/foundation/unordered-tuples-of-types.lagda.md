# Unordered tuples of types

```agda
module foundation.unordered-tuples-of-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels
open import foundation.unordered-tuples

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.identity-types

open import univalent-combinatorics.finite-types
```

</details>

## Idea

An unordered tuple of types is an unordered tuple of elements in a universe

## Definitions

### Unordered tuple of types

```agda
unordered-tuple-types : (l : Level) → ℕ → UU (lsuc l)
unordered-tuple-types l n = unordered-tuple n (UU l)
```

### Equivalences of unordered pairs of types

```agda
equiv-unordered-tuple-types :
  {l1 l2 : Level} (n : ℕ) →
  unordered-tuple-types l1 n → unordered-tuple-types l2 n → UU (l1 ⊔ l2)
equiv-unordered-tuple-types n A B =
  Σ ( type-unordered-tuple n A ≃ type-unordered-tuple n B)
    ( λ e →
      (i : type-unordered-tuple n A) →
      element-unordered-tuple n A i ≃
      element-unordered-tuple n B (map-equiv e i))

module _
  {l1 l2 : Level} (n : ℕ)
  (A : unordered-tuple-types l1 n) (B : unordered-tuple-types l2 n)
  (e : equiv-unordered-tuple-types n A B)
  where

  equiv-type-equiv-unordered-tuple-types :
    type-unordered-tuple n A ≃ type-unordered-tuple n B
  equiv-type-equiv-unordered-tuple-types = pr1 e

  map-equiv-type-equiv-unordered-tuple-types :
    type-unordered-tuple n A → type-unordered-tuple n B
  map-equiv-type-equiv-unordered-tuple-types =
    map-equiv equiv-type-equiv-unordered-tuple-types

  equiv-element-equiv-unordered-tuple-types :
    (i : type-unordered-tuple n A) →
    ( element-unordered-tuple n A i) ≃
    ( element-unordered-tuple n B
      ( map-equiv-type-equiv-unordered-tuple-types i))
  equiv-element-equiv-unordered-tuple-types = pr2 e
```

## Properties

### Univalence for unordered pairs of types

```agda
module _
  {l : Level} {n : ℕ} (A : unordered-tuple-types l n)
  where

  id-equiv-unordered-tuple-types : equiv-unordered-tuple-types n A A
  pr1 id-equiv-unordered-tuple-types = id-equiv
  pr2 id-equiv-unordered-tuple-types i = id-equiv

  equiv-eq-unordered-tuple-types :
    (B : unordered-tuple-types l n) → A ＝ B → equiv-unordered-tuple-types n A B
  equiv-eq-unordered-tuple-types .A refl = id-equiv-unordered-tuple-types

  is-contr-total-equiv-unordered-tuple-types :
    is-contr (Σ (unordered-tuple-types l n) (equiv-unordered-tuple-types n A))
  is-contr-total-equiv-unordered-tuple-types =
    is-contr-total-Eq-structure
      ( λ I B e →
        (i : type-unordered-tuple n A) →
        element-unordered-tuple n A i ≃ B (map-equiv e i))
      ( is-contr-total-equiv-UU-Fin {k = n} (type-unordered-tuple-UU-Fin n A))
      ( pair (type-unordered-tuple-UU-Fin n A) id-equiv)
      ( is-contr-total-equiv-fam (element-unordered-tuple n A))

  is-equiv-equiv-eq-unordered-tuple-types :
    (B : unordered-tuple-types l n) →
    is-equiv (equiv-eq-unordered-tuple-types B)
  is-equiv-equiv-eq-unordered-tuple-types =
    fundamental-theorem-id
      is-contr-total-equiv-unordered-tuple-types
      equiv-eq-unordered-tuple-types

  extensionality-unordered-tuple-types :
    (B : unordered-tuple-types l n) →
    (A ＝ B) ≃ equiv-unordered-tuple-types n A B
  pr1 (extensionality-unordered-tuple-types B) =
    equiv-eq-unordered-tuple-types B
  pr2 (extensionality-unordered-tuple-types B) =
    is-equiv-equiv-eq-unordered-tuple-types B
```
