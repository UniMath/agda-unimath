# Extensional pseudometric spaces (WIP)

```agda
module metric-spaces.extensional-pseudometric-spaces-WIP where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.pseudometric-spaces-WIP
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

A [pseudometric space](metric-spaces.pseudometric-spaces-WIP.md) is called
{{#concept "extensional" Disambiguation="pseudometric space" Agda=is-extensional-Pseudometric-Space-WIP}}
if any of the following equivalent condition holds:

- any [similar](metric-spaces.similarity-of-elements-pseudometric-spaces.md)
  elements are [identical](foundation-core.identity-types.md);
- the similarity relation has [propositional](foundation.propositions.md)
  fibers;
- the similarity relation is [torsorial](foundation.torsorial-type-families.md).

The carrier type of an extensional pseudometric space is a
[set](foundation.sets.md) and the
[discrete pseudometric structure](metric-spaces.discrete-pseudometric-structures.md)
over a set is extensional.

## Definitions

### The property of being an extensional pseudometric space

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  where

  is-extensional-prop-Pseudometric-Space-WIP : Prop (l1 ⊔ l2)
  is-extensional-prop-Pseudometric-Space-WIP =
    Π-Prop
      ( type-Pseudometric-Space-WIP A)
      ( is-prop-Prop ∘
        Σ (type-Pseudometric-Space-WIP A) ∘
        sim-Pseudometric-Space-WIP A)

  is-extensional-Pseudometric-Space-WIP : UU (l1 ⊔ l2)
  is-extensional-Pseudometric-Space-WIP =
    type-Prop is-extensional-prop-Pseudometric-Space-WIP

  is-prop-is-extensional-Pseudometric-Space-WIP :
    is-prop is-extensional-Pseudometric-Space-WIP
  is-prop-is-extensional-Pseudometric-Space-WIP =
    is-prop-type-Prop is-extensional-prop-Pseudometric-Space-WIP
```

### Tightness of a pseudometric space

A pseudometric space is
{{#concept "tight" Disambiguation="pseudometric" Agda=is-tight-Pseudometric-Space-WIP}}
if any two
[similar](metric-spaces.similarity-of-elements-pseudometric-spaces.md) elements
are [equal](foundation-core.identity-types.md).

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  where

  is-tight-Pseudometric-Space-WIP : UU (l1 ⊔ l2)
  is-tight-Pseudometric-Space-WIP =
    (x y : type-Pseudometric-Space-WIP A) →
    sim-Pseudometric-Space-WIP A x y →
    x ＝ y
```

## Properties

### Any tight pseudometric space is extensional

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  (T : is-tight-Pseudometric-Space-WIP A)
  where

  is-extensional-is-tight-Pseudometric-Space :
    is-extensional-Pseudometric-Space-WIP A
  is-extensional-is-tight-Pseudometric-Space x =
    is-prop-all-elements-equal
      ( λ (u , I) (v , J) →
        eq-type-subtype
          ( sim-prop-Pseudometric-Space-WIP A x)
          ( inv (T x u I) ∙ T x v J))
```

### Characterization of equality in an extensional pseudometric space

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  (E : is-extensional-Pseudometric-Space-WIP A)
  where

  is-torsorial-sim-is-extensional-Pseudometric-Space-WIP :
    (x : type-Pseudometric-Space-WIP A) →
    is-torsorial (sim-Pseudometric-Space-WIP A x)
  is-torsorial-sim-is-extensional-Pseudometric-Space-WIP x =
    is-proof-irrelevant-is-prop
      ( E x)
      ( x , refl-sim-Pseudometric-Space-WIP A x)

  is-fiberwise-equiv-sim-eq-is-extensional-Pseudometric-Space-WIP :
    (x y : type-Pseudometric-Space-WIP A) →
    is-equiv (sim-eq-Pseudometric-Space-WIP A x y)
  is-fiberwise-equiv-sim-eq-is-extensional-Pseudometric-Space-WIP x =
    fundamental-theorem-id
      ( is-torsorial-sim-is-extensional-Pseudometric-Space-WIP x)
      ( sim-eq-Pseudometric-Space-WIP A x)

  equiv-sim-eq-is-extensional-Pseudometric-Space-WIP :
    (x y : type-Pseudometric-Space-WIP A) →
    (x ＝ y) ≃ (sim-Pseudometric-Space-WIP A x y)
  equiv-sim-eq-is-extensional-Pseudometric-Space-WIP x y =
    ( sim-eq-Pseudometric-Space-WIP A x y) ,
    ( is-fiberwise-equiv-sim-eq-is-extensional-Pseudometric-Space-WIP x y)

  eq-sim-is-extensional-Pseudometric-Space-WIP :
    (x y : type-Pseudometric-Space-WIP A) →
    sim-Pseudometric-Space-WIP A x y →
    x ＝ y
  eq-sim-is-extensional-Pseudometric-Space-WIP x y =
    map-inv-equiv (equiv-sim-eq-is-extensional-Pseudometric-Space-WIP x y)
```

### Any extensional pseudometric is tight

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  (E : is-extensional-Pseudometric-Space-WIP A)
  where

  is-tight-is-extensional-Pseudometric-Space-WIP :
    is-tight-Pseudometric-Space-WIP A
  is-tight-is-extensional-Pseudometric-Space-WIP =
    eq-sim-is-extensional-Pseudometric-Space-WIP A E
```

### The carrier type of an extensional pseudometric space is a set

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  (E : is-extensional-Pseudometric-Space-WIP A)
  where

  is-set-type-is-extensional-Pseudometric-Space-WIP :
    is-set (type-Pseudometric-Space-WIP A)
  is-set-type-is-extensional-Pseudometric-Space-WIP x y =
    is-prop-is-equiv
      ( is-fiberwise-equiv-sim-eq-is-extensional-Pseudometric-Space-WIP
        ( A)
        ( E)
        ( x)
        ( y))
      ( is-prop-sim-Pseudometric-Space-WIP A x y)
```

## See also

- [metric spaces](metric-spaces.metric-spaces-WIP.md): the type of extensional
  pseudometric spaces.
