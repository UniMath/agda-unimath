# Material sets

```agda
module set-theory.material-sets where
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

A {{#concept "material set" Agda=Material-Set}} is a type `A` equipped with an
[elementhood structure](set-theory.elementhood-structures.md), i.e., a
type-valued relation `_∈_ : A → A → Type` such that
`(x ＝ y) ≃ ((u : A) → (u ∈ x) ≃ (u ∈ y))` for all `x y : A`.

**Terminology.** Note that a material set does not generally define a homotopy
set in the sense of [0-types](foundation-core.sets.md). Here, by _set_ is is
instead meant that we have structure with an appropriate notion of
"elementhood".

## Definitions

### The type of material sets

```agda
Material-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Material-Set l1 l2 = Σ (UU l1) (Elementhood-Structure l2)

module _
  {l1 l2 : Level} (A : Material-Set l1 l2)
  where

  type-Material-Set : UU l1
  type-Material-Set = pr1 A

  elementhood-structure-Material-Set :
    Elementhood-Structure l2 type-Material-Set
  elementhood-structure-Material-Set = pr2 A

  elementhood-Material-Set : Relation l2 type-Material-Set
  elementhood-Material-Set =
    elementhood-Elementhood-Structure
      ( elementhood-structure-Material-Set)

  is-extensional-elementhood-structure-Material-Set :
    is-extensional-elementhood-Relation elementhood-Material-Set
  is-extensional-elementhood-structure-Material-Set =
    is-extensional-Elementhood-Structure
      ( elementhood-structure-Material-Set)

module _
  {l1 l2 : Level} (A : Material-Set l1 l2)
  (let _∈_ = elementhood-Material-Set A)
  where

  equiv-elementhood-eq-Material-Set :
    (x y : type-Material-Set A) →
    (x ＝ y) → (u : type-Material-Set A) → (u ∈ x) ≃ (u ∈ y)
  equiv-elementhood-eq-Material-Set =
    equiv-eq-Elementhood-Structure
      ( elementhood-structure-Material-Set A)

  extensionality-Material-Set :
    (x y : type-Material-Set A) →
    (x ＝ y) ≃ ((u : type-Material-Set A) → (u ∈ x) ≃ (u ∈ y))
  extensionality-Material-Set =
    extensionality-Elementhood-Structure
      ( elementhood-structure-Material-Set A)

  inv-extensionality-Material-Set :
    (x y : type-Material-Set A) →
    ((u : type-Material-Set A) → (u ∈ x) ≃ (u ∈ y)) ≃ (x ＝ y)
  inv-extensionality-Material-Set =
    inv-extensionality-Elementhood-Structure
      ( elementhood-structure-Material-Set A)

  eq-equiv-elementhood-Material-Set :
    (x y : type-Material-Set A) →
    ((u : type-Material-Set A) → (u ∈ x) ≃ (u ∈ y)) → (x ＝ y)
  eq-equiv-elementhood-Material-Set =
    eq-equiv-Elementhood-Structure
      ( elementhood-structure-Material-Set A)
```

### The type of elements of an element

```agda
module _
  {l1 l2 : Level} (A : Material-Set l1 l2)
  where

  element-Material-Set : type-Material-Set A → UU (l1 ⊔ l2)
  element-Material-Set =
    element-Elementhood-Structure (elementhood-structure-Material-Set A)
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
  (A : Material-Set l1 l2)
  (let _∈_ = elementhood-Material-Set A)
  where

  abstract
    is-separated-type-is-in-global-reflective-subuniverse-elementhood-Material-Set :
      ( (x y : type-Material-Set A) →
        is-in-reflective-global-subuniverse ℒ (x ∈ y)) →
      (x y : type-Material-Set A) →
      is-in-reflective-global-subuniverse ℒ (x ＝ y)
    is-separated-type-is-in-global-reflective-subuniverse-elementhood-Material-Set =
      is-separated-is-in-global-reflective-subuniverse-Elementhood-Structure ℒ
      ( elementhood-structure-Material-Set A)
```

### Uniqueness of comprehensions

This is Proposition 4 of {{#cite GS24}}.

```agda
module _
  {l1 l2 : Level} (A : Material-Set l1 l2)
  (let _∈_ = elementhood-Material-Set A)
  where

  abstract
    uniqueness-comprehension-Material-Set' :
      {l3 : Level} (ϕ : type-Material-Set A → UU l3) →
      is-proof-irrelevant
        ( Σ ( type-Material-Set A)
            ( λ x → (u : type-Material-Set A) → ϕ u ≃ (u ∈ x)))
    uniqueness-comprehension-Material-Set' =
      uniqueness-comprehension-Elementhood-Structure'
        ( elementhood-structure-Material-Set A)

  abstract
    uniqueness-comprehension-Material-Set :
      {l3 : Level} (ϕ : type-Material-Set A → UU l3) →
      is-prop
        ( Σ ( type-Material-Set A)
            ( λ x → (u : type-Material-Set A) → ϕ u ≃ (u ∈ x)))
    uniqueness-comprehension-Material-Set =
      uniqueness-comprehension-Elementhood-Structure
        ( elementhood-structure-Material-Set A)
```

## References

{{#bibliography}}
