# The axiom of choice implies the law of excluded middle

```agda
module foundation.axiom-of-choice-implies-law-of-excluded-middle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.axiom-of-choice
open import foundation.booleans
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalence-induction
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.postcomposition-functions
open import foundation.propositional-truncations
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.weak-function-extensionality

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications

open import synthetic-homotopy-theory.suspensions-of-propositions
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

The [axiom of choice](foundation.axiom-of-choice.md) implies the
[law of excluded middle](foundation.law-of-excluded-middle.md). This is usually
recognized as {{#concept "Diaconescu's theorem"}}.

## Theorem

We follow the proof given under Theorem 10.1.14 in {{#cite UF13}}.

```agda
lem-AC-0 :
  {l : Level} → level-AC-0 l l → LEM l
lem-AC-0 ac P =
  rec-trunc-Prop
    ( is-decidable-Prop P)
    ( λ s →
      is-decidable-iff'
        ( ( iff-equiv (compute-eq-north-south-suspension-Prop P)) ∘iff
          ( ( λ p →
              ( inv (pr2 (s north-suspension))) ∙
              ( ap map-surjection-bool-suspension p) ∙
              ( pr2 (s south-suspension))) ,
            ( ap (pr1 ∘ s))))
        ( has-decidable-equality-bool
          ( pr1 (s north-suspension))
          ( pr1 (s south-suspension))))
    ( ac
      ( suspension-set-Prop P)
      ( fiber map-surjection-bool-suspension)
      ( is-surjective-map-surjection-bool-suspension))
```

## References

{{#bibliography}}
