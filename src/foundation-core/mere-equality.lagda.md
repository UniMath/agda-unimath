# Mere equality

```agda
module foundation-core.mere-equality where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.binary-relations
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

Two elements in a type are said to be {{#concept "merely equal" Agda=mere-eq}} if there is an element of the
[propositionally truncated](foundation.propositional-truncations.md) [identity type](foundation-core.identity-types.md) between them.

## Definitions

### Mere equality

```agda
module _
  {l : Level} {A : UU l}
  where

  mere-eq-Prop : A → A → Prop l
  mere-eq-Prop x y = trunc-Prop (x ＝ y)

  mere-eq : A → A → UU l
  mere-eq x y = type-Prop (mere-eq-Prop x y)

  is-prop-mere-eq : (x y : A) → is-prop (mere-eq x y)
  is-prop-mere-eq x y = is-prop-type-trunc-Prop
```

## Properties

### Reflexivity

```agda
abstract
  refl-mere-eq :
    {l : Level} {A : UU l} → is-reflexive (mere-eq {l} {A})
  refl-mere-eq _ = unit-trunc-Prop refl
```

### Symmetry

```agda
abstract
  symmetric-mere-eq :
    {l : Level} {A : UU l} → is-symmetric (mere-eq {l} {A})
  symmetric-mere-eq _ _ = map-trunc-Prop inv
```

### Transitivity

```agda
abstract
  transitive-mere-eq :
    {l : Level} {A : UU l} → is-transitive (mere-eq {l} {A})
  transitive-mere-eq x y z p q =
    apply-universal-property-trunc-Prop q
      ( mere-eq-Prop x z)
      ( λ p' → map-trunc-Prop (p' ∙_) p)
```
