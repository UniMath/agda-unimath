# De Morgan sheaves

```agda
module logic.de-morgan-sheaves where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.fibers-of-maps
open import foundation.diagonal-maps-of-types
open import foundation.unit-type
open import foundation.subtypes
open import foundation.precomposition-functions
open import foundation.empty-types
open import foundation.propositional-truncations
open import foundation.universal-property-propositional-truncation
open import foundation.irrefutable-propositions
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.identity-types
open import foundation.embeddings
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions

open import logic.de-morgans-law
open import logic.de-morgan-types
open import logic.double-negation-stable-subtypes
open import foundation.decidable-subtypes
open import logic.de-morgan-maps

open import orthogonal-factorization-systems.double-negation-sheaves
open import orthogonal-factorization-systems.null-types
```

</details>

## Idea

{{#concept "De morgan sheaves" Agda=is-de-morgan-sheaf}} are types that are
[null](orthogonal-factorization-systems.null-types.md) at
[propositions](foundation-core.propositions.md) of the form `¬P ∨ ¬¬P`.

De Morgan sheaves are closely related to, but a strictly weaker notion than
[double negation sheaves](orthogonal-factorization-systems.double-negation-sheaves.md).

## Definitions

### The property of being a De Morgan sheaf

**Note.** We present De Morgan sheaves as types that are null at `¬ P + ¬¬ P`
for all _types_ `P`, this is equivalent to being null at `¬ P ∨ ¬¬ P` for all
propositions `P`. The latter presentation demonstrates that De Morgan
sheafification is a lex accessible modality.

```agda
is-de-morgan-sheaf :
  (l1 : Level) {l2 : Level} (A : UU l2) → UU (lsuc l1 ⊔ l2)
is-de-morgan-sheaf l1 A =
  (P : UU l1) → is-null (is-decidable (¬ P)) A

is-prop-is-de-morgan-sheaf :
  {l1 l2 : Level} {A : UU l2} → is-prop (is-de-morgan-sheaf l1 A)
is-prop-is-de-morgan-sheaf {A = A} =
  is-prop-Π (λ P → is-prop-is-null (is-decidable (¬ P)) A)
```

### The subuniverse of De Morgan sheaves

```agda
De-Morgan-Sheaf : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
De-Morgan-Sheaf l1 l2 = Σ (UU l1) (is-de-morgan-sheaf l2)

module _
  {l1 l2 : Level} (A : De-Morgan-Sheaf l1 l2)
  where

  type-De-Morgan-Sheaf : UU l1
  type-De-Morgan-Sheaf = pr1 A

  is-de-morgan-type-De-Morgan-Sheaf : is-de-morgan-sheaf l2 type-De-Morgan-Sheaf
  is-de-morgan-type-De-Morgan-Sheaf = pr2 A
```

## Properties

### If the De Morgan predicate is idempotent at a type, then the type is De Morgan

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  is-de-morgan-is-idempotent-is-de-morgan' :
    (is-de-morgan (is-de-morgan A) → is-de-morgan A) → is-de-morgan A
  is-de-morgan-is-idempotent-is-de-morgan' f = f (inr is-irrefutable-is-de-morgan)
```

### The empty type is a De Morgan sheaf

```agda
is-de-morgan-sheaf-empty :
  {l : Level} → is-de-morgan-sheaf l empty
is-de-morgan-sheaf-empty P =
  is-equiv-has-converse empty-Prop
    ( neg-type-Prop (is-decidable (¬ P)))
    ( is-irrefutable-is-decidable)
```

### Contractible types are De Morgan sheaves

```agda
is-de-morgan-sheaf-is-contr :
  {l1 l2 : Level} {A : UU l1} → is-contr A → is-de-morgan-sheaf l2 A
is-de-morgan-sheaf-is-contr is-contr-A P =
  is-null-is-contr (is-decidable (¬ P)) is-contr-A
```

### Double negation sheaves are De Morgan sheaves

```agda
is-de-morgan-sheaf-is-double-negation-sheaf :
  {l1 l2 : Level} {A : UU l1} →
  is-double-negation-sheaf l2 A →
  is-de-morgan-sheaf l2 A
is-de-morgan-sheaf-is-double-negation-sheaf H P =
  H (is-decidable-prop-Irrefutable-Prop (neg-type-Prop P))
```

### If a type is a De Morgan sheaf at propositions then it is a De Morgan sheaf at all types

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  is-de-morgan-sheaf-is-de-morgan-sheaf-Prop :
    ((P : Prop l2) → is-null (is-decidable (¬ (type-Prop P))) A) →
    is-de-morgan-sheaf l2 A
  is-de-morgan-sheaf-is-de-morgan-sheaf-Prop H B =
    is-null-equiv-exponent
      ( inv-equiv equiv-is-de-morgan-trunc)
      ( H (trunc-Prop B))
```

## References

{{#bibliography}}

## External links

- [De Morganization](https://ncatlab.org/nlab/show/De+Morganization) at $n$Lab
