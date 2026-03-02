# Enumerations of types

```agda
module set-theory.enumerations where
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

open import set-theory.decidable-subprojections
```

</details>

## Idea

Given a type `α`, a type `X` is said to be
`α`-{{#concept "enumerated" Disambiguation="type" Agda=enumeration}} if there is
a [surjective map](foundation.surjective-maps.md) `α ↠ 1 + X`.

If `α` and `X` are [discrete types](foundation.discrete-types.md), then `X` is
`α`-enumerated if and only if `X` is a
[retract](foundation.retracts-of-types.md) of `α` or
[empty](foundation-core.empty-types.md).

## Definitions

### The type of α-enumerations of X

```agda
enumeration : {l1 l2 : Level} (α : UU l1) (X : UU l2) → UU (l1 ⊔ l2)
enumeration α X = (α ↠ Maybe X)

module _
  {l1 l2 : Level} {α : UU l1} {X : UU l2} (E : enumeration α X)
  where

  map-enumeration : α → Maybe X
  map-enumeration = pr1 E

  is-surjective-map-enumeration : is-surjective map-enumeration
  is-surjective-map-enumeration = pr2 E
```

### The type of α-enumerations

```agda
enumerations : {l1 : Level} (l2 : Level) (α : UU l1) → UU (l1 ⊔ lsuc l2)
enumerations l2 α = Σ (UU l2) (λ X → (α ↠ Maybe X))
```

### The predicate of being α-enumerable

```agda
module _
  {l1 l2 : Level} (α : UU l1) (X : UU l2)
  where

  is-enumerable : UU (l1 ⊔ l2)
  is-enumerable = ║ enumeration α X ║₋₁

  is-prop-is-enumberable : is-prop is-enumerable
  is-prop-is-enumberable = is-prop-type-trunc-Prop

  is-enumerable-Prop : Prop (l1 ⊔ l2)
  is-enumerable-Prop = trunc-Prop (enumeration α X)
```

## Properties

### If X has an α-enumeration then X is a decidable subprojection of α

```agda
module _
  {l1 l2 : Level} {α : UU l1} {X : UU l2}
  where

  decidable-subprojection-enumeration :
    enumeration α X → decidable-subprojection l2 α X
  pr1 (pr1 (decidable-subprojection-enumeration (f , H)) n) =
    f n ≠ inr star
  pr1 (pr2 (pr1 (decidable-subprojection-enumeration (f , H)) n)) =
    is-prop-neg
  pr2 (pr2 (pr1 (decidable-subprojection-enumeration (f , H)) n)) =
    is-decidable-is-not-exception-Maybe (f n)
  pr1 (pr2 (decidable-subprojection-enumeration (f , H))) (n , p) =
    value-is-not-exception-Maybe (f n) p
  pr2 (pr2 (decidable-subprojection-enumeration (f , H))) x =
    map-trunc-Prop
      ( λ (n , p) →
        ( n , is-not-exception-is-value-Maybe (f n) (x , inv p)) ,
        ( is-injective-inl
          ( ( eq-is-not-exception-Maybe
              ( f n)
              ( is-not-exception-is-value-Maybe (f n) (x , inv p))) ∙
            ( p))))
      ( H (inl x))

  is-decidable-subprojection-is-enumerable :
    is-enumerable α X → is-decidable-subprojection l2 α X
  is-decidable-subprojection-is-enumerable H =
    apply-universal-property-trunc-Prop H
      ( is-decidable-subprojection-Prop l2 α X)
      ( unit-trunc-Prop ∘ decidable-subprojection-enumeration)
```

### The empty type is α-enumerable iff α is inhabited

```agda
module _
  {l : Level} {α : UU l}
  where

  enumeration-emtpy : is-inhabited α → enumeration α empty
  enumeration-emtpy |x₀| =
    ( ( λ _ → exception-Maybe) ,
      ( λ where (inr _) → map-trunc-Prop (_, refl) |x₀|))

  is-inhabited-enumeration-empty : enumeration α empty → is-inhabited α
  is-inhabited-enumeration-empty (f , H) =
    map-trunc-Prop pr1 (H exception-Maybe)
```

## See also

- [Enumerations by fixed points of the maybe-monad](set-theory.enumerations-fixed-points-maybe.md)
