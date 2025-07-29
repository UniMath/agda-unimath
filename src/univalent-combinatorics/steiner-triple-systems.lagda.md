# Steiner triple systems

```agda
module univalent-combinatorics.steiner-triple-systems where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-subtypes
open import foundation.disjunction
open import foundation.decidable-types
open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.truncations
open import foundation-core.subtypes
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation.decidable-equality
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation.unit-type
open import foundation-core.decidable-propositions
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.empty-types
open import foundation-core.sets
open import foundation-core.truncation-levels

open import structured-types.wild-quasigroups

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.steiner-systems
```

</details>

## Definition

```agda
Steiner-Triple-System : ℕ → UU (lsuc lzero)
Steiner-Triple-System n = Steiner-System 2 3 n
```

## Properties

### The [wild quasigroup](group-theory.quasigroups.md) of a Steiner triple system

```agda
Steiner-Triple-System-Wild-Quasigroup :
  {n : ℕ} → Steiner-Triple-System n → Wild-Quasigroup lzero
pr1 (pr1 (Steiner-Triple-System-Wild-Quasigroup {n} ((X , _) , _))) = X
pr2 (pr1 (Steiner-Triple-System-Wild-Quasigroup {n} (( X , fin-X) , triple-X , unique-triple-X))) x y with has-decidable-equality-has-cardinality-ℕ n fin-X x y
... | inl p = x
... | inr p = {!   !}
  where
  xyz :
    Σ (type-decidable-subtype triple-X) (λ U → (z : X) →
      pr1 (prop-Decidable-Prop (disjunction-Decidable-Prop
        ( Id-has-cardinality-ℕ-Decidable-Prop n fin-X z x)
        ( Id-has-cardinality-ℕ-Decidable-Prop n fin-X z y))) →
        pr1 (prop-Decidable-Prop (pr1 (pr1 U) z)))
  xyz =
    center (unique-triple-X (λ z → disjunction-Decidable-Prop
      ( Id-has-cardinality-ℕ-Decidable-Prop n fin-X z x)
      ( Id-has-cardinality-ℕ-Decidable-Prop n fin-X z y)) (unit-trunc-Prop lem))
    where
    lem :
      Fin 2 ≃ type-decidable-subtype (λ z →
        disjunction-Decidable-Prop
          ( Id-has-cardinality-ℕ-Decidable-Prop n fin-X z x)
          ( Id-has-cardinality-ℕ-Decidable-Prop n fin-X z y))
    pr1 lem (inl (inr star)) = x , inl-disjunction refl
    pr1 lem (inr star) = y , inr-disjunction refl
    pr1 (pr1 (pr2 lem)) (z , z-equals) with has-decidable-equality-has-cardinality-ℕ n fin-X z x | has-decidable-equality-has-cardinality-ℕ n fin-X z y
    ... | inl q | inl r = ex-falso (p (inv q ∙ r))
    ... | inl q | inr r = inl (inr star)
    ... | inr q | inl r = inr star
    ... | inr q | inr r = ex-falso (elim-disjunction empty-Prop q r z-equals)
    pr2 (pr1 (pr2 lem)) (z , z-equals) with has-decidable-equality-has-cardinality-ℕ n fin-X z x | has-decidable-equality-has-cardinality-ℕ n fin-X z y
    ... | inl q | inl r =
      eq-type-subtype (λ w → disjunction-Prop
        ( Id-has-cardinality-ℕ-Prop n fin-X w x)
        ( Id-has-cardinality-ℕ-Prop n fin-X w y))
      (ex-falso (p (inv q ∙ r)))
    ... | inl q | inr r =
      eq-type-subtype (λ w → disjunction-Prop
        ( Id-has-cardinality-ℕ-Prop n fin-X w x)
        ( Id-has-cardinality-ℕ-Prop n fin-X w y))
      ({!   !} ∙ inv q)
    ... | inr q | inl r =
      eq-type-subtype (λ w → disjunction-Prop
        ( Id-has-cardinality-ℕ-Prop n fin-X w x)
        ( Id-has-cardinality-ℕ-Prop n fin-X w y))
      ({!   !} ∙ inv r)
    ... | inr q | inr r =
      eq-type-subtype (λ w → disjunction-Prop
        ( Id-has-cardinality-ℕ-Prop n fin-X w x)
        ( Id-has-cardinality-ℕ-Prop n fin-X w y))
      (ex-falso (elim-disjunction empty-Prop q r z-equals))
    pr1 (pr2 (pr2 lem)) (z , z-equals) with has-decidable-equality-has-cardinality-ℕ n fin-X z x | has-decidable-equality-has-cardinality-ℕ n fin-X z y
    ... | inl q | inl r = ex-falso (p (inv q ∙ r))
    ... | inl q | inr r = inl (inr star)
    ... | inr q | inl r = inr star
    ... | inr q | inr r = ex-falso (elim-disjunction empty-Prop q r z-equals)
    pr2 (pr2 (pr2 lem)) (inl (inr star)) = {!   !}
    pr2 (pr2 (pr2 lem)) (inr star) = {!   !}
pr2 (Steiner-Triple-System-Wild-Quasigroup X) = {!   !}
```
