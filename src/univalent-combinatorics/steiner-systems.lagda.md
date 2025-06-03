# Steiner systems

```agda
module univalent-combinatorics.steiner-systems where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.universe-levels

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
```
