# Isometries between premetric spaces

```agda
module metric-spaces.isometries-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.extensional-premetric-structures
open import metric-spaces.premetric-spaces
open import metric-spaces.uniformly-continuous-functions-premetric-spaces
```

</details>

## Idea

A function `f` between [premetric spaces](metric-spaces.premetric-spaces.md) is
an
{{#concept "isometry" Disambiguation="between premetric spaces" Agda=is-isometry-Premetric-Space}}
if any of the following equal conditions holds:

- it preserves and reflects
  [`d`-neighborhoods](metric-spaces.premetric-structures.md);
- the upper bounds on the distance between any two points and their image by `f`
  are the same;
- the premetric on the domain of `f` is the
  [preimage](metric-spaces.induced-premetric-structures-on-preimages.md) by `f`
  of the premetric on its codomain.

## Definitions

### The property of being a isometry between premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : map-type-Premetric-Space A B)
  where

  is-isometry-prop-Premetric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-isometry-prop-Premetric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( type-Premetric-Space A)
          ( λ x →
            Π-Prop
              ( type-Premetric-Space A)
              ( λ y →
                iff-Prop
                  ( structure-Premetric-Space A d x y)
                  ( structure-Premetric-Space B d (f x) (f y)))))

  is-isometry-Premetric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-isometry-Premetric-Space =
    type-Prop is-isometry-prop-Premetric-Space

  is-prop-is-isometry-Premetric-Space : is-prop is-isometry-Premetric-Space
  is-prop-is-isometry-Premetric-Space =
    is-prop-type-Prop is-isometry-prop-Premetric-Space
```

### The type of isometries between premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  where

  isometry-Premetric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometry-Premetric-Space = type-subtype (is-isometry-prop-Premetric-Space A B)
```

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : isometry-Premetric-Space A B)
  where

  map-isometry-Premetric-Space : map-type-Premetric-Space A B
  map-isometry-Premetric-Space = pr1 f

  is-isometry-map-isometry-Premetric-Space :
    is-isometry-Premetric-Space A B map-isometry-Premetric-Space
  is-isometry-map-isometry-Premetric-Space = pr2 f
```

## Properties

### Equality of isometries in premetric spaces is characterized by homotopies between their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f g : isometry-Premetric-Space A B)
  where

  equiv-eq-htpy-map-isometry-Premetric-Space :
    ( f ＝ g) ≃
    ( map-isometry-Premetric-Space A B f ~
      map-isometry-Premetric-Space A B g)
  equiv-eq-htpy-map-isometry-Premetric-Space =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-isometry-prop-Premetric-Space A B)
      ( f)
      ( g)

  eq-htpy-map-isometry-Premetric-Space :
    ( map-isometry-Premetric-Space A B f ~
      map-isometry-Premetric-Space A B g) →
    ( f ＝ g)
  eq-htpy-map-isometry-Premetric-Space =
    map-inv-equiv equiv-eq-htpy-map-isometry-Premetric-Space
```

### Composition of isometries between premetric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Premetric-Space l1a l2a)
  (B : Premetric-Space l1b l2b)
  (C : Premetric-Space l1c l2c)
  (g : map-type-Premetric-Space B C)
  (f : map-type-Premetric-Space A B)
  where

  preserves-isometry-comp-function-Premetric-Space :
    is-isometry-Premetric-Space B C g →
    is-isometry-Premetric-Space A B f →
    is-isometry-Premetric-Space A C (g ∘ f)
  preserves-isometry-comp-function-Premetric-Space H K d x y =
    (H d (f x) (f y)) ∘iff (K d x y)
```

### The inverse of an isometric equivalence between premetric spaces is an isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : map-type-Premetric-Space A B)
  (E : is-equiv f)
  (I : is-isometry-Premetric-Space A B f)
  where

  is-isometry-map-inv-is-equiv-is-isometry-Premetric-Space :
    is-isometry-Premetric-Space B A (map-inv-is-equiv E)
  is-isometry-map-inv-is-equiv-is-isometry-Premetric-Space d x y =
    logical-equivalence-reasoning
      ( neighborhood-Premetric-Space B d x y)
      ↔ ( neighborhood-Premetric-Space B d
          ( f (map-inv-is-equiv E x))
          ( f (map-inv-is-equiv E y)))
        by
          binary-tr
            ( λ u v →
              ( neighborhood-Premetric-Space B d x y) ↔
              ( neighborhood-Premetric-Space B d u v))
            ( inv (is-section-map-inv-is-equiv E x))
            ( inv (is-section-map-inv-is-equiv E y))
            ( id-iff)
      ↔ ( neighborhood-Premetric-Space A d
          ( map-inv-is-equiv E x)
          ( map-inv-is-equiv E y))
        by
          inv-iff
            ( I d (map-inv-is-equiv E x) (map-inv-is-equiv E y))
```

### Isometries preserve and reflect indistinguishability

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : isometry-Premetric-Space A B)
  {x y : type-Premetric-Space A}
  where

  preserves-is-indistinguishable-map-isometry-Premetric-Space :
    ( is-indistinguishable-Premetric-Space A x y) →
    ( is-indistinguishable-Premetric-Space
      ( B)
      ( map-isometry-Premetric-Space A B f x)
      ( map-isometry-Premetric-Space A B f y))
  preserves-is-indistinguishable-map-isometry-Premetric-Space H d =
    forward-implication
      ( is-isometry-map-isometry-Premetric-Space A B f d x y)
      ( H d)

  reflects-is-indistinguishable-map-isometry-Premetric-Space :
    ( is-indistinguishable-Premetric-Space
      ( B)
      ( map-isometry-Premetric-Space A B f x)
      ( map-isometry-Premetric-Space A B f y)) →
    ( is-indistinguishable-Premetric-Space A x y)
  reflects-is-indistinguishable-map-isometry-Premetric-Space H d =
    backward-implication
      ( is-isometry-map-isometry-Premetric-Space A B f d x y)
      ( H d)
```

### Any isometry between extensional premetric spaces is an embedding

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (I : is-extensional-Premetric (structure-Premetric-Space A))
  (J : is-extensional-Premetric (structure-Premetric-Space B))
  (f : isometry-Premetric-Space A B)
  where

  is-injective-map-isometry-is-extensional-Premetric-Space :
    is-injective (map-isometry-Premetric-Space A B f)
  is-injective-map-isometry-is-extensional-Premetric-Space {x} {y} =
    ( eq-indistinguishable-is-extensional-Premetric
      ( structure-Premetric-Space A)
      ( I)) ∘
    ( reflects-is-indistinguishable-map-isometry-Premetric-Space
      ( A)
      ( B)
      ( f)) ∘
    ( indistinguishable-eq-is-extensional-Premetric
      ( structure-Premetric-Space B)
      ( J))

  is-emb-map-isometry-is-extensional-Premetric-Space :
    is-emb (map-isometry-Premetric-Space A B f)
  is-emb-map-isometry-is-extensional-Premetric-Space =
    is-emb-is-injective
      ( is-set-has-extensional-Premetric (structure-Premetric-Space B) J)
      ( is-injective-map-isometry-is-extensional-Premetric-Space)
```

### Any isometry between premetric spaces is uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l3 l4)
  where

  is-uniformly-continuous-map-isometry-Premetric-Space :
    (f : isometry-Premetric-Space A B) →
    is-uniformly-continuous-map-Premetric-Space A B
      (map-isometry-Premetric-Space A B f)
  is-uniformly-continuous-map-isometry-Premetric-Space f =
    intro-exists
      ( id)
      ( λ x ε x' →
        forward-implication
          ( is-isometry-map-isometry-Premetric-Space A B f ε x x'))
```
