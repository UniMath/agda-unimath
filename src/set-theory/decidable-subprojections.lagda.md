# Decidable subprojections

```agda
module set-theory.decidable-subprojections where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
open import foundation.postcomposition-functions
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
open import foundation-core.identity-types

open import logic.functoriality-existential-quantification
```

</details>

## Idea

A
{{#concept "decidable subprojection" Disambiguation="of a type" Agda=decidable-subprojection}}
of a type `α` onto a type `X` is a surjection `β ↠ X` for some
[decidable subtype](foundation.decidable-subtypes.md) `β` of `α`.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (α : UU l1) (X : UU l2)
  where

  decidable-subprojection : UU (l1 ⊔ l2 ⊔ lsuc l3)
  decidable-subprojection =
    Σ (decidable-subtype l3 α) (λ β → type-decidable-subtype β ↠ X)

  is-decidable-subprojection-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-decidable-subprojection-Prop =
    exists-structure-Prop
      ( decidable-subtype l3 α)
      ( λ β → type-decidable-subtype β ↠ X)

  is-decidable-subprojection : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-decidable-subprojection = type-Prop is-decidable-subprojection-Prop

  is-prop-is-decidable-subprojection : is-prop is-decidable-subprojection
  is-prop-is-decidable-subprojection =
    is-prop-type-Prop is-decidable-subprojection-Prop
```

## See also

- [Enumerations](set-theory.enumerations.md)
