# Distributivity of set truncation over finite products

```agda
module univalent-combinatorics.distributivity-of-set-truncation-over-finite-products where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.distributivity-of-set-truncation-over-projective-products
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.propositional-truncations
open import foundation.set-truncations
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Theorem

`trunc-Set` distributes over `Π` indexed by `Fin`.

```agda
abstract
  distributive-trunc-Π-Fin-Set :
    {l : Level} (k : ℕ) (A : Fin k → UU l) →
    is-contr
      ( Σ ( ( type-trunc-Set ((x : Fin k) → A x)) ≃
            ( (x : Fin k) → type-trunc-Set (A x)))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( map-Π (λ x → unit-trunc-Set))))
  distributive-trunc-Π-Fin-Set k A =
    distributive-trunc-Π-is-projective-Level'
      ( Fin k)
      ( A)
      ( λ P h → finite-choice-Fin k {Y = P} h)

module _
  {l : Level} (k : ℕ) (A : Fin k → UU l)
  where

  equiv-distributive-trunc-Π-Fin-Set :
    type-trunc-Set ((x : Fin k) → A x) ≃ ((x : Fin k) → type-trunc-Set (A x))
  equiv-distributive-trunc-Π-Fin-Set =
    pr1 (center (distributive-trunc-Π-Fin-Set k A))

  map-equiv-distributive-trunc-Π-Fin-Set :
    type-trunc-Set ((x : Fin k) → A x) → ((x : Fin k) → type-trunc-Set (A x))
  map-equiv-distributive-trunc-Π-Fin-Set =
    map-equiv equiv-distributive-trunc-Π-Fin-Set

  is-equiv-map-equiv-distributive-trunc-Π-Fin-Set :
    is-equiv map-equiv-distributive-trunc-Π-Fin-Set
  is-equiv-map-equiv-distributive-trunc-Π-Fin-Set =
    is-equiv-map-equiv equiv-distributive-trunc-Π-Fin-Set

  triangle-distributive-trunc-Π-Fin-Set :
    ( map-equiv-distributive-trunc-Π-Fin-Set ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-Fin-Set =
    pr2 (center (distributive-trunc-Π-Fin-Set k A))

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  abstract
    distributive-trunc-Π-count-Set :
      count A →
      is-contr
        ( Σ ( ║ ((x : A) → B x) ║₀ ≃
              ( (x : A) → ║ B x ║₀))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( map-Π (λ x → unit-trunc-Set))))
    distributive-trunc-Π-count-Set c =
      distributive-trunc-Π-is-projective-Level'
        ( A)
        ( B)
        ( λ P h → finite-choice-count {X = A} {Y = P} c h)
```

## Corollaries

### Set-truncation distributes over sets equipped with counting

```agda
module _
  {l1 l2 : Level} {A : UU l1} (c : count A) (B : A → UU l2)
  where

  equiv-distributive-trunc-Π-count-Set :
    ║ ((x : A) → B x) ║₀ ≃ ((x : A) → ║ B x ║₀)
  equiv-distributive-trunc-Π-count-Set =
    pr1 (center (distributive-trunc-Π-count-Set B c))

  map-equiv-distributive-trunc-Π-count-Set :
    ║ ((x : A) → B x) ║₀ → ((x : A) → ║ B x ║₀)
  map-equiv-distributive-trunc-Π-count-Set =
    map-equiv equiv-distributive-trunc-Π-count-Set

  is-equiv-map-equiv-distributive-trunc-Π-count-Set :
    is-equiv map-equiv-distributive-trunc-Π-count-Set
  is-equiv-map-equiv-distributive-trunc-Π-count-Set =
    is-equiv-map-equiv equiv-distributive-trunc-Π-count-Set

  triangle-distributive-trunc-Π-count-Set :
    ( map-equiv-distributive-trunc-Π-count-Set ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-count-Set =
    pr2 (center (distributive-trunc-Π-count-Set B c))
```

### Set-truncation distributes over finite sets

```agda
module _
  {l1 l2 : Level} {A : UU l1} (H : is-finite A) (B : A → UU l2)
  where

  abstract
    distributive-trunc-Π-is-finite-Set :
      is-contr
        ( Σ ( ( ║ ((x : A) → B x) ║₀) ≃
              ( (x : A) → ║ B x ║₀))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( map-Π (λ x → unit-trunc-Set))))
    distributive-trunc-Π-is-finite-Set =
      distributive-trunc-Π-is-projective-Level'
        ( A)
        ( B)
        ( λ P h → finite-choice {X = A} {Y = P} H h)

  equiv-distributive-trunc-Π-is-finite-Set :
    ║ ((x : A) → B x) ║₀ ≃ ((x : A) → ║ B x ║₀)
  equiv-distributive-trunc-Π-is-finite-Set =
    pr1 (center distributive-trunc-Π-is-finite-Set)

  map-equiv-distributive-trunc-Π-is-finite-Set :
    ║ ((x : A) → B x) ║₀ → ((x : A) → ║ B x ║₀)
  map-equiv-distributive-trunc-Π-is-finite-Set =
    map-equiv equiv-distributive-trunc-Π-is-finite-Set

  is-equiv-map-equiv-distributive-trunc-Π-is-finite-Set :
    is-equiv map-equiv-distributive-trunc-Π-is-finite-Set
  is-equiv-map-equiv-distributive-trunc-Π-is-finite-Set =
    is-equiv-map-equiv equiv-distributive-trunc-Π-is-finite-Set

  triangle-distributive-trunc-Π-is-finite-Set :
    ( map-equiv-distributive-trunc-Π-is-finite-Set ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-is-finite-Set =
    pr2 (center distributive-trunc-Π-is-finite-Set)

module _
  {l1 l2 : Level} (A : Finite-Type l1) (B : type-Finite-Type A → UU l2)
  (let H = is-finite-type-Finite-Type A)
  where

  distributive-trunc-Π-Finite-Type :
    is-contr
      ( Σ ( ( ║ ((x : type-Finite-Type A) → B x) ║₀) ≃
            ( (x : type-Finite-Type A) → ║ B x ║₀))
          ( λ e →
            ( map-equiv e ∘ unit-trunc-Set) ~
            ( map-Π (λ x → unit-trunc-Set))))
  distributive-trunc-Π-Finite-Type =
    distributive-trunc-Π-is-finite-Set H B

  equiv-distributive-trunc-Π-Finite-Type :
    ║ ((x : type-Finite-Type A) → B x) ║₀ ≃
    ((x : type-Finite-Type A) → ║ B x ║₀)
  equiv-distributive-trunc-Π-Finite-Type =
    equiv-distributive-trunc-Π-is-finite-Set H B

  map-equiv-distributive-trunc-Π-Finite-Type :
    ║ ((x : type-Finite-Type A) → B x) ║₀ →
    ((x : type-Finite-Type A) → ║ B x ║₀)
  map-equiv-distributive-trunc-Π-Finite-Type =
    map-equiv-distributive-trunc-Π-is-finite-Set H B

  is-equiv-map-equiv-distributive-trunc-Π-Finite-Type :
    is-equiv map-equiv-distributive-trunc-Π-Finite-Type
  is-equiv-map-equiv-distributive-trunc-Π-Finite-Type =
    is-equiv-map-equiv-distributive-trunc-Π-is-finite-Set H B

  triangle-distributive-trunc-Π-Finite-Type :
    ( map-equiv-distributive-trunc-Π-Finite-Type ∘ unit-trunc-Set) ~
    ( map-Π (λ x → unit-trunc-Set))
  triangle-distributive-trunc-Π-Finite-Type =
    triangle-distributive-trunc-Π-is-finite-Set H B
```

## See also

- [Finite choice](univalent-combinatorics.finite-choice.md) for distributivity
  of propositional truncation over finite products.
- Distributivity of set-truncation in particular means that finite sets are
  [cardinality-projective](set-theory.cardinality-projective-sets.md).
