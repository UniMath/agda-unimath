# Extensionality of pseudometric spaces

```agda
module metric-spaces.extensional-pseudometric-spaces where
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

open import metric-spaces.pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

A [pseudometric space](metric-spaces.pseudometric-spaces.md) is called
{{#concept "extensional" Disambiguation="pseudometric space" Agda=is-extensional-Pseudometric-Space}}
if any of the following equivalent conditions holds:

- [similar](metric-spaces.similarity-of-elements-pseudometric-spaces.md)
  elements are [identical](foundation-core.identity-types.md);
- the similarity relation has [propositional](foundation.propositions.md)
  fibers;
- the similarity relation is [torsorial](foundation.torsorial-type-families.md).

The carrier type of an extensional pseudometric space is a
[set](foundation.sets.md).

## Definitions

### The property of being an extensional pseudometric space

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  is-extensional-prop-Pseudometric-Space : Prop (l1 ⊔ l2)
  is-extensional-prop-Pseudometric-Space =
    Π-Prop
      ( type-Pseudometric-Space A)
      ( is-prop-Prop ∘
        Σ (type-Pseudometric-Space A) ∘
        sim-Pseudometric-Space A)

  is-extensional-Pseudometric-Space : UU (l1 ⊔ l2)
  is-extensional-Pseudometric-Space =
    type-Prop is-extensional-prop-Pseudometric-Space

  is-prop-is-extensional-Pseudometric-Space :
    is-prop is-extensional-Pseudometric-Space
  is-prop-is-extensional-Pseudometric-Space =
    is-prop-type-Prop is-extensional-prop-Pseudometric-Space
```

### Tightness of a pseudometric space

A pseudometric space is
{{#concept "tight" Disambiguation="pseudometric" Agda=is-tight-Pseudometric-Space}}
if any two
[similar](metric-spaces.similarity-of-elements-pseudometric-spaces.md) elements
are [equal](foundation-core.identity-types.md).

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  is-tight-Pseudometric-Space : UU (l1 ⊔ l2)
  is-tight-Pseudometric-Space =
    (x y : type-Pseudometric-Space A) →
    sim-Pseudometric-Space A x y →
    x ＝ y
```

## Properties

### Tight pseudometric spaces are extensional

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  (T : is-tight-Pseudometric-Space A)
  where

  is-extensional-is-tight-Pseudometric-Space :
    is-extensional-Pseudometric-Space A
  is-extensional-is-tight-Pseudometric-Space x =
    is-prop-all-elements-equal
      ( λ (u , I) (v , J) →
        eq-type-subtype
          ( sim-prop-Pseudometric-Space A x)
          ( inv (T x u I) ∙ T x v J))
```

### Characterization of equality in an extensional pseudometric space

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  (E : is-extensional-Pseudometric-Space A)
  where

  is-torsorial-sim-is-extensional-Pseudometric-Space :
    (x : type-Pseudometric-Space A) →
    is-torsorial (sim-Pseudometric-Space A x)
  is-torsorial-sim-is-extensional-Pseudometric-Space x =
    is-proof-irrelevant-is-prop
      ( E x)
      ( x , refl-sim-Pseudometric-Space A x)

  is-fiberwise-equiv-sim-eq-is-extensional-Pseudometric-Space :
    (x y : type-Pseudometric-Space A) →
    is-equiv (sim-eq-Pseudometric-Space A x y)
  is-fiberwise-equiv-sim-eq-is-extensional-Pseudometric-Space x =
    fundamental-theorem-id
      ( is-torsorial-sim-is-extensional-Pseudometric-Space x)
      ( sim-eq-Pseudometric-Space A x)

  equiv-sim-eq-is-extensional-Pseudometric-Space :
    (x y : type-Pseudometric-Space A) →
    (x ＝ y) ≃ (sim-Pseudometric-Space A x y)
  equiv-sim-eq-is-extensional-Pseudometric-Space x y =
    ( sim-eq-Pseudometric-Space A x y) ,
    ( is-fiberwise-equiv-sim-eq-is-extensional-Pseudometric-Space x y)

  eq-sim-is-extensional-Pseudometric-Space :
    (x y : type-Pseudometric-Space A) →
    sim-Pseudometric-Space A x y →
    x ＝ y
  eq-sim-is-extensional-Pseudometric-Space x y =
    map-inv-equiv (equiv-sim-eq-is-extensional-Pseudometric-Space x y)
```

### Extensional pseudometric spaces are tight

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  (E : is-extensional-Pseudometric-Space A)
  where

  is-tight-is-extensional-Pseudometric-Space :
    is-tight-Pseudometric-Space A
  is-tight-is-extensional-Pseudometric-Space =
    eq-sim-is-extensional-Pseudometric-Space A E
```

### The carrier type of an extensional pseudometric space is a set

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  (E : is-extensional-Pseudometric-Space A)
  where

  is-set-type-is-extensional-Pseudometric-Space :
    is-set (type-Pseudometric-Space A)
  is-set-type-is-extensional-Pseudometric-Space x y =
    is-prop-is-equiv
      ( is-fiberwise-equiv-sim-eq-is-extensional-Pseudometric-Space
        ( A)
        ( E)
        ( x)
        ( y))
      ( is-prop-sim-Pseudometric-Space A x y)
```

## See also

- Extensional
  pseudometric spaces are called [metric spaces](metric-spaces.metric-spaces.md).
