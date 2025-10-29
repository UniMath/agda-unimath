# Elementhood structures

```agda
module set-theory.elementhood-structures where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.separated-types-subuniverses
open import foundation.subtypes
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.torsorial-type-families

open import order-theory.accessible-elements-relations
open import order-theory.preorders

open import orthogonal-factorization-systems.reflective-global-subuniverses
```

</details>

## Idea

Given a type `A` and a [binary relation](foundation.binary-relations.md)
`_∈_ : A → A → Type` dubbed an _elementhood relation_, we say that the
elementhood relation is
{{#concept "extensional" Disambiguation="elementhood" Agda=is-extensional-elementhood-Relation}}
if the canonical map

```text
  (x = y) → (Π (u : A), (u ∈ x) ≃ (u ∈ y))
```

is an [equivalence](foundation-core.equivalences.md).

An extensional elementhood relation on `A` endows the type `A` with the
[structure](foundation.structure.md) of
{{#concept "elementhood" Disambiguation="on a type" Agda=Elementhood-Structure}}.

## Definitions

### The canonical comparison map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (_∈_ : Relation l2 A)
  where

  equiv-elementhood-eq-Relation :
    (x y : A) → (x ＝ y) → (u : A) → (u ∈ x) ≃ (u ∈ y)
  equiv-elementhood-eq-Relation x .x refl u = id-equiv
```

### The extensionality predicate on elementhood relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (_∈_ : Relation l2 A)
  where

  is-extensional-elementhood-Relation : UU (l1 ⊔ l2)
  is-extensional-elementhood-Relation =
    (x y : A) → is-equiv (equiv-elementhood-eq-Relation _∈_ x y)

  abstract
    is-prop-is-extensional-elementhood-Relation :
      is-prop is-extensional-elementhood-Relation
    is-prop-is-extensional-elementhood-Relation =
      is-prop-Π
        ( λ x →
          is-prop-Π
            ( λ y →
              is-property-is-equiv (equiv-elementhood-eq-Relation _∈_ x y)))

  is-extensional-elementhood-prop-Relation : Prop (l1 ⊔ l2)
  is-extensional-elementhood-prop-Relation =
    ( is-extensional-elementhood-Relation ,
      is-prop-is-extensional-elementhood-Relation)
```

### The type of elementhood structures on a type

```agda
Elementhood-Structure :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Elementhood-Structure l2 A =
  type-subtype (is-extensional-elementhood-prop-Relation {l2 = l2} {A})

module _
  {l1 l2 : Level} {A : UU l1} (R@(_∈_ , _) : Elementhood-Structure l2 A)
  where

  elementhood-Elementhood-Structure : Relation l2 A
  elementhood-Elementhood-Structure = pr1 R

  is-extensional-Elementhood-Structure :
    is-extensional-elementhood-Relation elementhood-Elementhood-Structure
  is-extensional-Elementhood-Structure = pr2 R

  equiv-eq-Elementhood-Structure :
    (x y : A) → (x ＝ y) → (u : A) → (u ∈ x) ≃ (u ∈ y)
  equiv-eq-Elementhood-Structure =
    equiv-elementhood-eq-Relation _∈_

  extensionality-Elementhood-Structure :
    (x y : A) → (x ＝ y) ≃ ((u : A) → (u ∈ x) ≃ (u ∈ y))
  extensionality-Elementhood-Structure x y =
    ( equiv-eq-Elementhood-Structure x y ,
      is-extensional-Elementhood-Structure x y)

  inv-extensionality-Elementhood-Structure :
    (x y : A) → ((u : A) → (u ∈ x) ≃ (u ∈ y)) ≃ (x ＝ y)
  inv-extensionality-Elementhood-Structure x y =
    inv-equiv (extensionality-Elementhood-Structure x y)

  eq-equiv-Elementhood-Structure :
    (x y : A) → ((u : A) → (u ∈ x) ≃ (u ∈ y)) → (x ＝ y)
  eq-equiv-Elementhood-Structure x y =
    map-inv-equiv (extensionality-Elementhood-Structure x y)
```

### The type of elements of an element

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R@(_∈_ , _) : Elementhood-Structure l2 A)
  where

  element-Elementhood-Structure : A → UU (l1 ⊔ l2)
  element-Elementhood-Structure x = Σ A (_∈ x)
```

## Properties

### Elementhood relations valued in localizations

If the elementhood relation `_∈_ : A → A → Type` is valued in a
[localization](orthogonal-factorization-systems.reflective-global-subuniverses.md)
`ℒ`, then `A` is `ℒ`-[separated](foundation.separated-types-subuniverses.md).

This is a generalization of Proposition 1 of {{#cite GS24}}.

**Proof.** By extensionality, `(x ＝ y) ≃ ((u : A) → (u ∈ x) ≃ (u ∈ y))`, and
the right hand side is a dependent product of equivalence types between
`ℒ`-types, and so is itself an `ℒ`-type. ∎

```agda
module _
  {α β : Level → Level} {l1 l2 : Level}
  (ℒ : reflective-global-subuniverse α β)
  {A : UU l1} (R@(_∈_ , _) : Elementhood-Structure l2 A)
  where

  abstract
    is-separated-is-in-global-reflective-subuniverse-Elementhood-Structure :
      ((x y : A) → is-in-reflective-global-subuniverse ℒ (x ∈ y)) →
      (x y : A) → is-in-reflective-global-subuniverse ℒ (x ＝ y)
    is-separated-is-in-global-reflective-subuniverse-Elementhood-Structure
      H x y =
      is-closed-under-equiv-reflective-global-subuniverse ℒ
        ( (u : A) → (u ∈ x) ≃ (u ∈ y))
        ( x ＝ y)
        ( inv-extensionality-Elementhood-Structure R x y)
        ( is-in-reflective-global-subuniverse-Π ℒ
          ( λ u → is-in-reflective-global-subuniverse-equiv ℒ (H u x) (H u y)))
```

### Uniqueness of comprehensions

This is Proposition 4 of {{#cite GS24}}.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R@(_∈_ , _) : Elementhood-Structure l2 A)
  where

  abstract
    uniqueness-comprehension-Elementhood-Structure' :
      {l3 : Level} (ϕ : A → UU l3) →
      is-proof-irrelevant (Σ A (λ x → (u : A) → ϕ u ≃ (u ∈ x)))
    uniqueness-comprehension-Elementhood-Structure' ϕ (x , α) =
      is-contr-equiv'
        ( Σ A (x ＝_))
        ( equiv-tot
          ( λ y →
            equiv-Π-equiv-family
              ( λ u → equiv-precomp-equiv (α u) (u ∈ y)) ∘e
              ( extensionality-Elementhood-Structure R x y)))
        ( is-torsorial-Id x)

  abstract
    uniqueness-comprehension-Elementhood-Structure :
      {l3 : Level} (ϕ : A → UU l3) →
      is-prop (Σ A (λ x → (u : A) → ϕ u ≃ (u ∈ x)))
    uniqueness-comprehension-Elementhood-Structure ϕ =
      is-prop-is-proof-irrelevant
        ( uniqueness-comprehension-Elementhood-Structure' ϕ)
```

## References

{{#bibliography}}

## External links

- <https://git.app.uib.no/hott/hott-set-theory/-/blob/master/src/e-structure/core.agda>
