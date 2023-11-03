# ω-Finite types

```agda
module univalent-combinatorics.omega-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

The subuniverse of **ω-finite type** is the least subuniverse containing `∅`,
`𝟙`, and is closed under pushouts. The category of ω-finite types has
coproducts, cartesian products, and pushouts, but is not closed under pullbacks,
truncations, retracts, exponents, dependent products, quotients of segal
groupoids.

The notion of ω-finite types was introduced by Mathieu Anel during the _Beyond
Finite Sets_ workshop in Copenhagen, on May 15th 2023.

## Definition

### The predicate of being ω-finite

```agda
data ω-finite-structure : UU lzero → UU (lsuc lzero) where
  ω-finite-structure-empty : ω-finite-structure empty
  ω-finite-structure-unit : ω-finite-structure unit
  ω-finite-structure-pushout :
    {S : UU lzero} {A : UU lzero} {B : UU lzero} →
    (f : S → A) (g : S → B) →
    ω-finite-structure S →
    ω-finite-structure A →
    ω-finite-structure B →
    ω-finite-structure (pushout f g)

is-ω-finite-Prop : UU lzero → Prop (lsuc lzero)
is-ω-finite-Prop A = trunc-Prop (ω-finite-structure A)

is-ω-finite : UU lzero → UU (lsuc lzero)
is-ω-finite X = type-Prop (is-ω-finite-Prop X)
```

### The type of ω-finite types

```agda
ω-Finite-Type : UU (lsuc lzero)
ω-Finite-Type = Σ (UU lzero) is-ω-finite

module _
  (X : ω-Finite-Type)
  where

  type-ω-Finite-Type : UU lzero
  type-ω-Finite-Type = pr1 X

  is-ω-finite-ω-Finite-Type : is-ω-finite type-ω-Finite-Type
  is-ω-finite-ω-Finite-Type = pr2 X
```
