# Pseudometric spaces

```agda
module metric-spaces.pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.premetric-spaces
open import metric-spaces.premetric-structures
```

</details>

## Idea

A {{#concept "pseudometric space" Agda=Pseudometric-Space}} is a
[premetric space](metric-spaces.premetric-spaces.md) whose
[premetric](metric-spaces.premetric-structures.md) is symmetric reflexive and
triangular.

Indistiguishability in a pseudometric space is an
[equivalence relation](foundation.equivalence-relations.md).

## Definitions

### The property of being a pseudometric premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-pseudometric-prop-Premetric : Prop (l1 ⊔ l2)
  is-pseudometric-prop-Premetric =
    product-Prop
      ( is-symmetric-prop-Premetric B)
      ( product-Prop
        ( is-reflexive-prop-Premetric B)
        ( is-triangular-prop-Premetric B))

  is-pseudometric-Premetric : UU (l1 ⊔ l2)
  is-pseudometric-Premetric =
    type-Prop is-pseudometric-prop-Premetric

  is-prop-is-pseudometric-Premetric :
    is-prop is-pseudometric-Premetric
  is-prop-is-pseudometric-Premetric =
    is-prop-type-Prop is-pseudometric-prop-Premetric
```

### The property of being a pseudometric premetric space

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  where

  is-pseudometric-prop-Premetric-Space : Prop (l1 ⊔ l2)
  is-pseudometric-prop-Premetric-Space =
    is-pseudometric-prop-Premetric (structure-Premetric-Space A)

  is-pseudometric-Premetric-Space : UU (l1 ⊔ l2)
  is-pseudometric-Premetric-Space =
    type-Prop is-pseudometric-prop-Premetric-Space

  is-prop-is-pseudometric-Premetric-Space :
    is-prop is-pseudometric-Premetric-Space
  is-prop-is-pseudometric-Premetric-Space =
    is-prop-type-Prop is-pseudometric-prop-Premetric-Space
```

### The type of pseudometric spaces

```agda
Pseudometric-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Pseudometric-Space l1 l2 =
  type-subtype (is-pseudometric-prop-Premetric-Space {l1} {l2})

module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  premetric-Pseudometric-Space : Premetric-Space l1 l2
  premetric-Pseudometric-Space = pr1 M

  type-Pseudometric-Space : UU l1
  type-Pseudometric-Space =
    type-Premetric-Space premetric-Pseudometric-Space

  structure-Pseudometric-Space : Premetric l2 type-Pseudometric-Space
  structure-Pseudometric-Space =
    structure-Premetric-Space premetric-Pseudometric-Space

  is-pseudometric-structure-Pseudometric-Space :
    is-pseudometric-Premetric structure-Pseudometric-Space
  is-pseudometric-structure-Pseudometric-Space = pr2 M

  is-symmetric-structure-Pseudometric-Space :
    is-symmetric-Premetric structure-Pseudometric-Space
  is-symmetric-structure-Pseudometric-Space =
    pr1 is-pseudometric-structure-Pseudometric-Space

  is-reflexive-structure-Pseudometric-Space :
    is-reflexive-Premetric structure-Pseudometric-Space
  is-reflexive-structure-Pseudometric-Space =
    pr1 (pr2 is-pseudometric-structure-Pseudometric-Space)

  is-triangular-structure-Pseudometric-Space :
    is-triangular-Premetric structure-Pseudometric-Space
  is-triangular-structure-Pseudometric-Space =
    pr2 (pr2 is-pseudometric-structure-Pseudometric-Space)
```

### Indistiguishability in a pseudometric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (x y : type-Pseudometric-Space M)
  where

  is-indistinguishable-prop-Pseudometric-Space : Prop l2
  is-indistinguishable-prop-Pseudometric-Space =
    is-indistinguishable-prop-Premetric (structure-Pseudometric-Space M) x y

  is-indistinguishable-Pseudometric-Space : UU l2
  is-indistinguishable-Pseudometric-Space =
    type-Prop is-indistinguishable-prop-Pseudometric-Space

  is-prop-is-indistinguishable-Pseudometric-Space :
    is-prop is-indistinguishable-Pseudometric-Space
  is-prop-is-indistinguishable-Pseudometric-Space =
    is-prop-type-Prop is-indistinguishable-prop-Pseudometric-Space
```

### The type of functions between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  where

  function-carrier-type-Pseudometric-Space : UU (l1 ⊔ l1')
  function-carrier-type-Pseudometric-Space =
    type-Pseudometric-Space A → type-Pseudometric-Space B
```

## Properties

### Equal elements in a pseudometric space are indistinguishable

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  {x y : type-Pseudometric-Space M} (e : x ＝ y)
  where

  indistinguishable-eq-Pseudometric-Space :
    is-indistinguishable-Pseudometric-Space M x y
  indistinguishable-eq-Pseudometric-Space =
    indistinguishable-eq-reflexive-Premetric
      ( structure-Pseudometric-Space M)
      ( is-reflexive-structure-Pseudometric-Space M)
      ( e)
```

### Indistiguishability in a pseudometric space is an equivalence relation

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  is-equivalence-relation-is-indistinguishable-Pseudometric-Space :
    is-equivalence-relation
      (is-indistinguishable-prop-Pseudometric-Space M)
  is-equivalence-relation-is-indistinguishable-Pseudometric-Space =
    ( is-reflexive-is-indistinguishable-reflexive-Premetric
      ( structure-Pseudometric-Space M)
      ( is-reflexive-structure-Pseudometric-Space M)) ,
    ( is-symmetric-is-indistinguishable-is-symmetric-Premetric
      ( structure-Pseudometric-Space M)
      ( is-symmetric-structure-Pseudometric-Space M)) ,
    ( is-transitive-is-indistinguishable-triangular-Premetric
      ( structure-Pseudometric-Space M)
      ( is-triangular-structure-Pseudometric-Space M))
```

### Any set can be equipped with a pseudometric structure

```agda
module _
  {l : Level} (A : Set l)
  where

  discrete-Pseudometric-Space : Pseudometric-Space l l
  pr1 discrete-Pseudometric-Space = (type-Set A , λ d → Id-Prop A)
  pr2 discrete-Pseudometric-Space =
    ( λ d x y H → inv H) ,
    ( λ d x → refl) ,
    ( λ x y z d d' H K → K ∙ H)
```

## See also

- Metric spaces are defined in [metric-spaces](metric-spaces.metric-spaces.md).