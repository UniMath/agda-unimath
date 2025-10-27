# Material types

```agda
module set-theory.material-types where
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
open import foundation.locally-small-types
open import foundation.propositions
open import foundation.separated-types-subuniverses
open import foundation.subtypes
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.torsorial-type-families

open import order-theory.accessible-elements-relations
open import order-theory.preorders

open import orthogonal-factorization-systems.reflective-global-subuniverses

open import set-theory.elementhood-structures
```

</details>

## Idea

A {{#concept "material type" Agda=Material-Type}} is a type `A` equipped with an
[elementhood structure](set-theory.elementhood-structures.md), i.e., a
type-valued relation `_∈_ : A → A → Type` such that
`(x ＝ y) ≃ ((u : A) → (u ∈ x) ≃ (u ∈ y))` for all `x y : A`.

**Terminology.** Such structures are commonly referred to as _material sets_
{{#cite GS24}}. However, we reserve this name for material
[0-types](foundation-core.sets.md).

## Definitions

### The type of material types

```agda
Material-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Material-Type l1 l2 = Σ (UU l1) (Elementhood-Structure l2)

module _
  {l1 l2 : Level} (A : Material-Type l1 l2)
  where

  type-Material-Type : UU l1
  type-Material-Type = pr1 A

  elementhood-structure-Material-Type :
    Elementhood-Structure l2 type-Material-Type
  elementhood-structure-Material-Type = pr2 A

  elementhood-Material-Type : Relation l2 type-Material-Type
  elementhood-Material-Type =
    elementhood-Elementhood-Structure
      ( elementhood-structure-Material-Type)

  is-extensional-elementhood-structure-Material-Type :
    is-extensional-elementhood-Relation elementhood-Material-Type
  is-extensional-elementhood-structure-Material-Type =
    is-extensional-Elementhood-Structure
      ( elementhood-structure-Material-Type)

module _
  {l1 l2 : Level} (A : Material-Type l1 l2)
  (let _∈_ = elementhood-Material-Type A)
  where

  equiv-elementhood-eq-Material-Type :
    (x y : type-Material-Type A) →
    (x ＝ y) → (u : type-Material-Type A) → (u ∈ x) ≃ (u ∈ y)
  equiv-elementhood-eq-Material-Type =
    equiv-eq-Elementhood-Structure
      ( elementhood-structure-Material-Type A)

  extensionality-Material-Type :
    (x y : type-Material-Type A) →
    (x ＝ y) ≃ ((u : type-Material-Type A) → (u ∈ x) ≃ (u ∈ y))
  extensionality-Material-Type =
    extensionality-Elementhood-Structure
      ( elementhood-structure-Material-Type A)

  inv-extensionality-Material-Type :
    (x y : type-Material-Type A) →
    ((u : type-Material-Type A) → (u ∈ x) ≃ (u ∈ y)) ≃ (x ＝ y)
  inv-extensionality-Material-Type =
    inv-extensionality-Elementhood-Structure
      ( elementhood-structure-Material-Type A)

  eq-equiv-elementhood-Material-Type :
    (x y : type-Material-Type A) →
    ((u : type-Material-Type A) → (u ∈ x) ≃ (u ∈ y)) → (x ＝ y)
  eq-equiv-elementhood-Material-Type =
    eq-equiv-Elementhood-Structure
      ( elementhood-structure-Material-Type A)
```

### The type of elements of an element

```agda
module _
  {l1 l2 : Level} (A : Material-Type l1 l2)
  where

  element-Material-Type : type-Material-Type A → UU (l1 ⊔ l2)
  element-Material-Type =
    element-Elementhood-Structure (elementhood-structure-Material-Type A)
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
  (A : Material-Type l1 l2)
  (let _∈_ = elementhood-Material-Type A)
  where

  abstract
    is-separated-type-is-in-global-reflective-subuniverse-elementhood-Material-Type :
      ( (x y : type-Material-Type A) →
        is-in-reflective-global-subuniverse ℒ (x ∈ y)) →
      (x y : type-Material-Type A) →
      is-in-reflective-global-subuniverse ℒ (x ＝ y)
    is-separated-type-is-in-global-reflective-subuniverse-elementhood-Material-Type =
      is-separated-is-in-global-reflective-subuniverse-Elementhood-Structure ℒ
      ( elementhood-structure-Material-Type A)
```

### Uniqueness of comprehensions

This is Proposition 4 of {{#cite GS24}}.

```agda
module _
  {l1 l2 : Level} (A : Material-Type l1 l2)
  (let _∈_ = elementhood-Material-Type A)
  where

  abstract
    uniqueness-comprehension-Material-Type' :
      {l3 : Level} (ϕ : type-Material-Type A → UU l3) →
      is-proof-irrelevant
        ( Σ ( type-Material-Type A)
            ( λ x → (u : type-Material-Type A) → ϕ u ≃ (u ∈ x)))
    uniqueness-comprehension-Material-Type' =
      uniqueness-comprehension-Elementhood-Structure'
        ( elementhood-structure-Material-Type A)

  abstract
    uniqueness-comprehension-Material-Type :
      {l3 : Level} (ϕ : type-Material-Type A → UU l3) →
      is-prop
        ( Σ ( type-Material-Type A)
            ( λ x → (u : type-Material-Type A) → ϕ u ≃ (u ∈ x)))
    uniqueness-comprehension-Material-Type =
      uniqueness-comprehension-Elementhood-Structure
        ( elementhood-structure-Material-Type A)
```

## References

{{#bibliography}}
