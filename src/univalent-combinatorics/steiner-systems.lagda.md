# Steiner systems

```agda
module univalent-combinatorics.steiner-systems where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.decidable-subtypes
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.decidable-propositions

open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A Steiner system of type `(t,k,n) : ℕ³` consists of an `n`-element type `X`
equipped with a (decidable) set `P` of `k`-element subtypes of `X` such that
each `t`-element subtype of `X` is contained in exactly one `k`-element subtype
in `P`. A basic example is the Fano plane, which is a Steiner system of type
`(2,3,7)`.

## Definition

### Steiner systems

```agda
Steiner-System : ℕ → ℕ → ℕ → UU (lsuc lzero)
Steiner-System t k n =
  Σ ( Type-With-Cardinality-ℕ lzero n)
    ( λ X →
      Σ ( decidable-subtype lzero
          ( Σ ( decidable-subtype lzero (type-Type-With-Cardinality-ℕ n X))
              ( λ P → has-cardinality-ℕ k (type-decidable-subtype P))))
        ( λ P →
          ( Q :
            decidable-subtype lzero (type-Type-With-Cardinality-ℕ n X)) →
          has-cardinality-ℕ t (type-decidable-subtype Q) →
          is-contr
            ( Σ ( type-decidable-subtype P)
                ( λ U →
                  (x : type-Type-With-Cardinality-ℕ n X) →
                  is-in-decidable-subtype Q x →
                  is-in-decidable-subtype (pr1 (pr1 U)) x))))

module _
  {t k n : ℕ} (X : Steiner-System t k n)
  where

  type-Steiner-System : UU lzero
  type-Steiner-System = pr1 (pr1 X)

  type-with-cardinality-Steiner-System : Type-With-Cardinality-ℕ lzero n
  type-with-cardinality-Steiner-System = pr1 X

  is-finite-type-Steiner-System : is-finite type-Steiner-System
  is-finite-type-Steiner-System =
    is-finite-type-Type-With-Cardinality-ℕ
      ( n)
      ( type-with-cardinality-Steiner-System)

  has-decidable-equality-Steiner-System :
    has-decidable-equality type-Steiner-System
  has-decidable-equality-Steiner-System =
    has-decidable-equality-is-finite is-finite-type-Steiner-System

  id-decidable-prop-Steiner-System :
    (x y : type-Steiner-System) → Decidable-Prop lzero
  id-decidable-prop-Steiner-System x y =
    has-decidable-equality-eq-Decidable-Prop
    ( has-decidable-equality-Steiner-System)
    ( x)
    ( y)

  subtype-family-Steiner-System :
    decidable-subtype lzero
      (Σ (decidable-subtype lzero type-Steiner-System)
        (λ P → has-cardinality-ℕ k (type-decidable-subtype P)))
  subtype-family-Steiner-System = pr1 (pr2 X)

  subtype-subtype-family-Steiner-System :
    type-decidable-subtype subtype-family-Steiner-System →
    decidable-subtype lzero type-Steiner-System
  subtype-subtype-family-Steiner-System ((S , _) , _) = S

  steiner-property-Steiner-System :
    (Q : decidable-subtype lzero type-Steiner-System) →
      has-cardinality-ℕ t (type-decidable-subtype Q) →
      is-contr
      (Σ (type-decidable-subtype subtype-family-Steiner-System)
        (λ U →
          (x : type-Steiner-System) →
          pr1
          (prop-Decidable-Prop
            (Q x)) →
          pr1
          (prop-Decidable-Prop
            (pr1 (pr1 U) x))))
  steiner-property-Steiner-System = pr2 (pr2 X)

  subtype-map-Steiner-System :
    (Q : decidable-subtype lzero type-Steiner-System) →
    has-cardinality-ℕ t (type-decidable-subtype Q) →
    type-decidable-subtype subtype-family-Steiner-System
  subtype-map-Steiner-System Q |Q| =
    pr1 (pr1 (steiner-property-Steiner-System Q |Q|))

  subtype-subtype-map-Steiner-System :
    (Q : decidable-subtype lzero type-Steiner-System) →
    has-cardinality-ℕ t (type-decidable-subtype Q) →
    decidable-subtype lzero type-Steiner-System
  subtype-subtype-map-Steiner-System Q |Q| =
    subtype-subtype-family-Steiner-System (subtype-map-Steiner-System Q |Q|)
```
