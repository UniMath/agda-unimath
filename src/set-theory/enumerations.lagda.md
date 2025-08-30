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

A type `X` is
`α`-{{#concept "enumerable" Disambiguation="type" Agda=is-enumerable}} if there
[exists](foundation.existential-quantification.md) an `α`-enumeration of `X`.

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

### Direct α-enumerability

A type `X` is {{#concept "directly α-enumerable" Agda=is-directly-enumerable}}
if there is a surjective map `α ↠ X`.

```agda
is-directly-enumerable-Prop : {l1 l2 : Level} → UU l1 → UU l2 → Prop (l1 ⊔ l2)
is-directly-enumerable-Prop α X = ∃ (α → X) (is-surjective-Prop)

is-directly-enumerable : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
is-directly-enumerable α X = type-Prop (is-directly-enumerable-Prop α X)

is-prop-is-directly-enumerable :
  {l1 l2 : Level} (α : UU l1) (X : UU l2) → is-prop (is-directly-enumerable α X)
is-prop-is-directly-enumerable α X =
  is-prop-type-Prop (is-directly-enumerable-Prop α X)

module _
  {l1 l2 : Level} {α : UU l1} {X : UU l2} (x₀ : X)
  where

  is-directly-enumerable-is-enumerable :
    is-enumerable α X → is-directly-enumerable α X
  is-directly-enumerable-is-enumerable H =
    apply-universal-property-trunc-Prop H
      ( is-directly-enumerable-Prop α X)
      ( λ P →
        unit-trunc-Prop
          ( f ∘ pr1 P , is-surjective-comp is-surjective-f (pr2 P)))
    where
    f : Maybe X → X
    f (inl x) = x
    f (inr _) = x₀

    is-surjective-f : is-surjective f
    is-surjective-f x = unit-trunc-Prop (inl x , refl)
```

For the converse, we need a shifting structure `α ≃ Maybe α`. See
[enumerations by fixed points of the maybe-monad](set-theory.enumerations-fixed-points-maybe.md).

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

### α-enumerations transfer along covers

```agda
module _
  {l1 l2 l3 : Level} {α : UU l1} {A : UU l2} {B : UU l3}
  where

  is-directly-enumerable-is-directly-enumerably-indexed' :
    {f : A → B} → is-surjective f →
    is-directly-enumerable α A → is-directly-enumerable α B
  is-directly-enumerable-is-directly-enumerably-indexed' {f} F =
    map-exists (is-surjective) (postcomp α f) (λ _ → is-surjective-comp F)

  is-directly-enumerable-is-directly-enumerably-indexed :
    (A ↠ B) → is-directly-enumerable α A → is-directly-enumerable α B
  is-directly-enumerable-is-directly-enumerably-indexed (f , F) =
    is-directly-enumerable-is-directly-enumerably-indexed' F

  is-enumerable-is-enumerably-indexed' :
    {f : A → B} → is-surjective f → is-enumerable α A → is-enumerable α B
  is-enumerable-is-enumerably-indexed' {f} F =
    map-exists
      ( is-surjective)
      ( postcomp α (map-Maybe f))
      ( λ _ → is-surjective-comp (is-surjective-map-is-surjective-Maybe F))

  is-enumerable-is-enumerably-indexed :
    (A ↠ B) → is-enumerable α A → is-enumerable α B
  is-enumerable-is-enumerably-indexed (f , F) =
    is-enumerable-is-enumerably-indexed' F
```

### Retracts of α-enumerable types are α-enumerable

```agda
module _
  {l1 l2 l3 : Level} {α : UU l1} {A : UU l2} {B : UU l3} (R : B retract-of A)
  where

  is-directly-enumerable-retract-of :
    is-directly-enumerable α A → is-directly-enumerable α B
  is-directly-enumerable-retract-of =
    is-directly-enumerable-is-directly-enumerably-indexed'
      { f = map-retraction-retract R}
      ( is-surjective-has-section
        ( inclusion-retract R , is-retraction-map-retraction-retract R))

  is-enumerable-retract-of :
    is-enumerable α A → is-enumerable α B
  is-enumerable-retract-of =
    is-enumerable-is-enumerably-indexed'
      { f = map-retraction-retract R}
      ( is-surjective-has-section
        ( inclusion-retract R , is-retraction-map-retraction-retract R))
```

### α-enumerable types are closed under equivalences

```agda
module _
  {l1 l2 l3 : Level} {α : UU l1} {A : UU l2} {B : UU l3} (e : B ≃ A)
  where

  is-directly-enumerable-equiv :
    is-directly-enumerable α A → is-directly-enumerable α B
  is-directly-enumerable-equiv =
    is-directly-enumerable-retract-of (retract-equiv e)

  is-enumerable-equiv :
    is-enumerable α A → is-enumerable α B
  is-enumerable-equiv =
    is-enumerable-retract-of (retract-equiv e)
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

  is-enumerable-empty : is-inhabited α → is-enumerable α empty
  is-enumerable-empty |x₀| =
    unit-trunc-Prop ( enumeration-emtpy |x₀|)

  is-enumerable-empty' : α → is-enumerable α empty
  is-enumerable-empty' x₀ = is-enumerable-empty (unit-trunc-Prop x₀)

  is-inhabited-enumeration-empty : enumeration α empty → is-inhabited α
  is-inhabited-enumeration-empty (f , H) =
    map-trunc-Prop pr1 (H exception-Maybe)

  is-inhabited-is-enumerable-empty : is-enumerable α empty → is-inhabited α
  is-inhabited-is-enumerable-empty =
    rec-trunc-Prop (is-inhabited-Prop α) is-inhabited-enumeration-empty
```

## See also

- [Enumerations by fixed points of the maybe-monad](set-theory.enumerations-fixed-points-maybe.md)
