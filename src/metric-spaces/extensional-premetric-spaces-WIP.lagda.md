# Extensional premetric spaces (WIP)

```agda
module metric-spaces.extensional-premetric-spaces-WIP where
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

open import metric-spaces.premetric-spaces-WIP
open import metric-spaces.similarity-of-elements-premetric-spaces
```

</details>

## Idea

A [premetric space](metric-spaces.premetric-spaces-WIP.md) is called
{{#concept "extensional" Disambiguation="premetric space" Agda=is-extensional-Premetric-Space-WIP}}
if any of the following equivalent condition holds:

- any [similar](metric-spaces.similarity-of-elements-premetric-spaces.md)
  elements are [identical](foundation-core.identity-types.md);
- the similarity relation has [propositional](foundation.propositions.md)
  fibers;
- the similarity relation is [torsorial](foundation.torsorial-type-families.md).

The carrier type of an extensional premetric space is a
[set](foundation.sets.md) and the
[discrete premetric structure](metric-spaces.discrete-premetric-structures.md)
over a set is extensional.

## Definitions

### The property of being an extensional premetric space

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  is-extensional-prop-Premetric-Space-WIP : Prop (l1 ⊔ l2)
  is-extensional-prop-Premetric-Space-WIP =
    Π-Prop
      ( type-Premetric-Space-WIP A)
      ( is-prop-Prop ∘
        Σ (type-Premetric-Space-WIP A) ∘
        sim-Premetric-Space-WIP A)

  is-extensional-Premetric-Space-WIP : UU (l1 ⊔ l2)
  is-extensional-Premetric-Space-WIP =
    type-Prop is-extensional-prop-Premetric-Space-WIP

  is-prop-is-extensional-Premetric-Space-WIP :
    is-prop is-extensional-Premetric-Space-WIP
  is-prop-is-extensional-Premetric-Space-WIP =
    is-prop-type-Prop is-extensional-prop-Premetric-Space-WIP
```

### Tightness of a premetric space

A premetric space is
{{#concept "tight" Disambiguation="premetric" Agda=is-tight-Premetric-Space-WIP}}
if any two [similar](metric-spaces.similarity-of-elements-premetric-spaces.md)
elements are [equal](foundation-core.identity-types.md).

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  is-tight-Premetric-Space-WIP : UU (l1 ⊔ l2)
  is-tight-Premetric-Space-WIP =
    (x y : type-Premetric-Space-WIP A) →
    sim-Premetric-Space-WIP A x y →
    x ＝ y
```

## Properties

### Any tight premetric space is extensional

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  (T : is-tight-Premetric-Space-WIP A)
  where

  is-extensional-is-tight-Premetric-Space :
    is-extensional-Premetric-Space-WIP A
  is-extensional-is-tight-Premetric-Space x =
    is-prop-all-elements-equal
      ( λ (u , I) (v , J) →
        eq-type-subtype
          ( sim-prop-Premetric-Space-WIP A x)
          ( inv (T x u I) ∙ T x v J))
```

### Characterization of equality in an extensional premetric space

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  (E : is-extensional-Premetric-Space-WIP A)
  where

  is-torsorial-sim-is-extensional-Premetric-Space-WIP :
    (x : type-Premetric-Space-WIP A) →
    is-torsorial (sim-Premetric-Space-WIP A x)
  is-torsorial-sim-is-extensional-Premetric-Space-WIP x =
    is-proof-irrelevant-is-prop
      ( E x)
      ( x , refl-sim-Premetric-Space-WIP A x)

  is-fiberwise-equiv-sim-eq-is-extensional-Premetric-Space-WIP :
    (x y : type-Premetric-Space-WIP A) →
    is-equiv (sim-eq-Premetric-Space-WIP A x y)
  is-fiberwise-equiv-sim-eq-is-extensional-Premetric-Space-WIP x =
    fundamental-theorem-id
      ( is-torsorial-sim-is-extensional-Premetric-Space-WIP x)
      ( sim-eq-Premetric-Space-WIP A x)

  equiv-sim-eq-is-extensional-Premetric-Space-WIP :
    (x y : type-Premetric-Space-WIP A) →
    (x ＝ y) ≃ (sim-Premetric-Space-WIP A x y)
  equiv-sim-eq-is-extensional-Premetric-Space-WIP x y =
    ( sim-eq-Premetric-Space-WIP A x y) ,
    ( is-fiberwise-equiv-sim-eq-is-extensional-Premetric-Space-WIP x y)

  eq-sim-is-extensional-Premetric-Space-WIP :
    (x y : type-Premetric-Space-WIP A) →
    sim-Premetric-Space-WIP A x y →
    x ＝ y
  eq-sim-is-extensional-Premetric-Space-WIP x y =
    map-inv-equiv (equiv-sim-eq-is-extensional-Premetric-Space-WIP x y)
```

### Any extensional premetric is tight

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  (E : is-extensional-Premetric-Space-WIP A)
  where

  is-tight-is-extensional-Premetric-Space-WIP :
    is-tight-Premetric-Space-WIP A
  is-tight-is-extensional-Premetric-Space-WIP =
    eq-sim-is-extensional-Premetric-Space-WIP A E
```

### The carrier type of an extensional premetric space is a set

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  (E : is-extensional-Premetric-Space-WIP A)
  where

  is-set-type-is-extensional-Premetric-Space-WIP :
    is-set (type-Premetric-Space-WIP A)
  is-set-type-is-extensional-Premetric-Space-WIP x y =
    is-prop-is-equiv
      ( is-fiberwise-equiv-sim-eq-is-extensional-Premetric-Space-WIP
        ( A)
        ( E)
        ( x)
        ( y))
      ( is-prop-sim-Premetric-Space-WIP A x y)
```

## See also

- [metric spaces](metric-spaces.metric-spaces-WIP.md): the type of extensional
  premetric spaces.
