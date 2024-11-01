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
open import foundation.empty-types
open import foundation.irrefutable-propositions
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions

open import logic.de-morgans-law

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

## Properties

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

## References

{{#bibliography}}

## External links

- [De Morganization](https://ncatlab.org/nlab/show/De+Morganization) at $n$Lab
