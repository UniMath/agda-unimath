# Psuedometric spaces

```agda
module metric-spaces.pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.neighbourhood-relations
```

</details>

## Idea

A {{#concept "pseudometric space" Agda=Pseudometric-Space}} is a type equipped a
symmetric reflexive triangular
[neighbourhood-relation](metric-spaces.neighbourhood-relations.md).

## Definitions

### The property of being a pseudometric neighbourhood-relation on a type

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : neighbourhood-Relation-Prop l2 A)
  where

  is-pseudometric-neighbourhood : UU (l1 ⊔ l2)
  is-pseudometric-neighbourhood =
    ( is-symmetric-neighbourhood B) ×
    ( is-reflexive-neighbourhood B) ×
    ( is-triangular-neighbourhood B)

  is-prop-is-pseudometric-neighbourhood : is-prop is-pseudometric-neighbourhood
  is-prop-is-pseudometric-neighbourhood =
    is-prop-product
      ( is-prop-is-symmetric-neighbourhood B)
      ( is-prop-product
        ( is-prop-is-reflexive-neighbourhood B)
        ( is-prop-is-triangular-neighbourhood B))

  is-pseudometric-prop-neighbourhood : Prop (l1 ⊔ l2)
  is-pseudometric-prop-neighbourhood =
    is-pseudometric-neighbourhood , is-prop-is-pseudometric-neighbourhood
```

### Pseudometric structures over a type

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  Pseudometric-Structure : UU (l1 ⊔ lsuc l2)
  Pseudometric-Structure =
    Σ ( neighbourhood-Relation-Prop l2 A)
      ( is-pseudometric-neighbourhood A)
```

```agda
module _
  {l1 l2 : Level} (A : UU l1) (S : Pseudometric-Structure l2 A)
  where

  neighbourhood-Pseudometric-Structure : neighbourhood-Relation-Prop l2 A
  neighbourhood-Pseudometric-Structure = pr1 S

  is-pseudometric-neighbourhood-Pseudometric-Structure :
    is-pseudometric-neighbourhood A neighbourhood-Pseudometric-Structure
  is-pseudometric-neighbourhood-Pseudometric-Structure = pr2 S
```

### The type of pseudometric spaces

```agda
Pseudometric-Space : (l : Level) → UU (lsuc l)
Pseudometric-Space l = Σ (UU l) (Pseudometric-Structure l)

module _
  {l : Level} (M : Pseudometric-Space l)
  where

  type-Pseudometric-Space : UU l
  type-Pseudometric-Space = pr1 M

  structure-Pseudometric-Space :
    Pseudometric-Structure l type-Pseudometric-Space
  structure-Pseudometric-Space = pr2 M

  neighbourhood-Pseudometric-Space :
    neighbourhood-Relation-Prop l type-Pseudometric-Space
  neighbourhood-Pseudometric-Space = pr1 structure-Pseudometric-Space

  is-pseudometric-neighbourhood-Pseudometric-Space :
    is-pseudometric-neighbourhood
      type-Pseudometric-Space
      neighbourhood-Pseudometric-Space
  is-pseudometric-neighbourhood-Pseudometric-Space =
    pr2 structure-Pseudometric-Space

  is-in-neighbourhood-Pseudometric-Space :
    ℚ⁺ → Relation l type-Pseudometric-Space
  is-in-neighbourhood-Pseudometric-Space =
    is-in-neighbourhood neighbourhood-Pseudometric-Space

  is-symmetric-neighbourhood-Pseudometric-Space :
    is-symmetric-neighbourhood neighbourhood-Pseudometric-Space
  is-symmetric-neighbourhood-Pseudometric-Space =
    pr1 is-pseudometric-neighbourhood-Pseudometric-Space

  is-reflexive-neighbourhood-Pseudometric-Space :
    is-reflexive-neighbourhood neighbourhood-Pseudometric-Space
  is-reflexive-neighbourhood-Pseudometric-Space =
    pr1 (pr2 is-pseudometric-neighbourhood-Pseudometric-Space)

  is-triangular-neighbourhood-Pseudometric-Space :
    is-triangular-neighbourhood neighbourhood-Pseudometric-Space
  is-triangular-neighbourhood-Pseudometric-Space =
    pr2 (pr2 is-pseudometric-neighbourhood-Pseudometric-Space)
```

## Properties

### Equal elements in a pseudometric space are indistinguishable

```agda
module _
  {l : Level} (M : Pseudometric-Space l) (x y : type-Pseudometric-Space M)
  where

  indistinguishable-eq-Pseudometric-Space :
    x ＝ y →
    is-indistinguishable-in-neighbourhood
      ( neighbourhood-Pseudometric-Space M)
      ( x)
      ( y)
  indistinguishable-eq-Pseudometric-Space =
    indistinguishable-eq-reflexive-neighbourhood
      ( neighbourhood-Pseudometric-Space M)
      ( is-reflexive-neighbourhood-Pseudometric-Space M)
      ( x)
      ( y)
```

### Any set can be equipped with a pseudometric structure

```agda
module _
  {l : Level} (A : Set l)
  where

  discrete-Pseudometric-Structure : Pseudometric-Structure l (type-Set A)
  pr1 discrete-Pseudometric-Structure d = Id-Prop A
  pr2 discrete-Pseudometric-Structure =
    ( λ d x y H → inv H) ,
    ( λ d x → refl) ,
    ( λ x y z d₁ d₂ H K → K ∙ H)

  discrete-Pseudometric-Space : Pseudometric-Space l
  discrete-Pseudometric-Space = (type-Set A , discrete-Pseudometric-Structure)
```

## See also

- Metric spaces are defined in the
  [metric-spaces](metric-spaces.metric-spaces.md) module.
