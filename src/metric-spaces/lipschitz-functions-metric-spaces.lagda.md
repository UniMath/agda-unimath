# Lipschitz functions between metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.lipschitz-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.sequences

open import logic.functoriality-existential-quantification

open import metric-spaces.elements-at-bounded-distance-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

A
[positive rational number](elementary-number-theory.positive-rational-numbers.md)
`α : ℚ⁺` is a
{{#concept "Lipschitz constant" Disambiguation="of a function between metric spaces" Agda=lipschitz-constant-function-Metric-Space}}
for a [function](metric-spaces.functions-metric-spaces.md) `f : A → B` between
[metric spaces](metric-spaces.metric-spaces.md) if for any `x y : A`, if `d` is
an upper bound of the distance between `x` and `y` in `A`, then `α * d` is an
upper bound on the distance between `f x` and `f y` in `B`. If `α` is a
Lipschitz constant for `f`, then `f` is called an **α-Lipschitz** function. A
function that admits a Lipschitz constant is called a
{{#concept "Lipschitz function" Disambiguation="between metric spaces" WD="Lipschitz function" WDID=Q652707 Agda=lipschitz-function-Metric-Space}}.
Lipschitz maps between metric spaces preserve
[elements at bounded distance](metric-spaces.elements-at-bounded-distance-metric-spaces.md).

## Definitions

### The property of being a Lipschitz constant of a map between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : type-function-Metric-Space A B)
  where

  is-lipschitz-constant-prop-function-Metric-Space :
    ℚ⁺ → Prop (l1 ⊔ l2 ⊔ l2')
  is-lipschitz-constant-prop-function-Metric-Space α =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( type-Metric-Space A)
          ( λ x →
            Π-Prop
            ( type-Metric-Space A)
            ( λ y →
              hom-Prop
                ( neighborhood-prop-Metric-Space A d x y)
                ( neighborhood-prop-Metric-Space B (α *ℚ⁺ d) (f x) (f y)))))

  is-lipschitz-constant-function-Metric-Space : ℚ⁺ → UU (l1 ⊔ l2 ⊔ l2')
  is-lipschitz-constant-function-Metric-Space α =
    type-Prop (is-lipschitz-constant-prop-function-Metric-Space α)

  is-prop-is-lipschitz-constant-function-Metric-Space :
    (α : ℚ⁺) →
    is-prop (is-lipschitz-constant-function-Metric-Space α)
  is-prop-is-lipschitz-constant-function-Metric-Space α =
    is-prop-type-Prop (is-lipschitz-constant-prop-function-Metric-Space α)

  lipschitz-constant-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l2')
  lipschitz-constant-function-Metric-Space =
    type-subtype is-lipschitz-constant-prop-function-Metric-Space
```

### The property of being a Lipschitz function

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  is-lipschitz-function-prop-Metric-Space :
    type-function-Metric-Space A B → Prop (l1 ⊔ l2 ⊔ l2')
  is-lipschitz-function-prop-Metric-Space f =
    is-inhabited-subtype-Prop
      (is-lipschitz-constant-prop-function-Metric-Space A B f)

  is-lipschitz-function-Metric-Space :
    type-function-Metric-Space A B → UU (l1 ⊔ l2 ⊔ l2')
  is-lipschitz-function-Metric-Space f =
    type-Prop (is-lipschitz-function-prop-Metric-Space f)

  is-prop-is-lipschitz-function-Metric-Space :
    (f : type-function-Metric-Space A B) →
    is-prop (is-lipschitz-function-Metric-Space f)
  is-prop-is-lipschitz-function-Metric-Space f =
    is-prop-type-Prop (is-lipschitz-function-prop-Metric-Space f)
```

### The type of Lipschitz functions between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  lipschitz-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  lipschitz-function-Metric-Space =
    type-subtype (is-lipschitz-function-prop-Metric-Space A B)

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : lipschitz-function-Metric-Space A B)
  where

  map-lipschitz-function-Metric-Space :
    type-function-Metric-Space A B
  map-lipschitz-function-Metric-Space = pr1 f

  is-lipschitz-map-lipschitz-function-Metric-Space :
    is-lipschitz-function-Metric-Space A B map-lipschitz-function-Metric-Space
  is-lipschitz-map-lipschitz-function-Metric-Space = pr2 f
```

## Properties

### Constant functions are α-Lipschitz functions for all `α : ℚ⁺`

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : type-function-Metric-Space A B)
  where

  all-lipschitz-constant-is-constant-function-Metric-Space :
    ( (x y : type-Metric-Space A) → f x ＝ f y) →
    ( α : ℚ⁺) →
    is-lipschitz-constant-function-Metric-Space A B f α
  all-lipschitz-constant-is-constant-function-Metric-Space H α d x y _ =
    sim-eq-Metric-Space B (f x) (f y) (H x y) (α *ℚ⁺ d)
```

### Short functions are Lipschitz functions with Lipschitz constant equal to 1

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : type-function-Metric-Space A B)
  where

  is-one-lipschitz-constant-is-short-function-Metric-Space :
    is-short-function-Metric-Space A B f →
    is-lipschitz-constant-function-Metric-Space A B f one-ℚ⁺
  is-one-lipschitz-constant-is-short-function-Metric-Space H d x y Nxy =
    inv-tr
      ( is-upper-bound-dist-Metric-Space B (f x) (f y))
      ( left-unit-law-mul-ℚ⁺ d)
      ( H d x y Nxy)

  is-short-is-one-lipshitz-constant-function-Metric-Space :
    is-lipschitz-constant-function-Metric-Space A B f one-ℚ⁺ →
    is-short-function-Metric-Space A B f
  is-short-is-one-lipshitz-constant-function-Metric-Space L d x y Nxy =
    tr
      ( is-upper-bound-dist-Metric-Space B (f x) (f y))
      ( left-unit-law-mul-ℚ⁺ d)
      ( L d x y Nxy)
```

### Lipschitz functions are uniformly continuous

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : type-function-Metric-Space A B)
  where

  modulus-of-uniform-continuity-lipschitz-constant-function-Metric-Space :
    lipschitz-constant-function-Metric-Space A B f →
    modulus-of-uniform-continuity-function-Metric-Space A B f
  modulus-of-uniform-continuity-lipschitz-constant-function-Metric-Space
    ( α , L) =
    ( mul-ℚ⁺ (inv-ℚ⁺ α)) ,
    ( λ x d y H →
      tr
        ( is-upper-bound-dist-Metric-Space B (f x) (f y))
        ( ( inv (associative-mul-ℚ⁺ α (inv-ℚ⁺ α) d)) ∙
          ( ap (λ y → y *ℚ⁺ d) (right-inverse-law-mul-ℚ⁺ α)) ∙
          ( left-unit-law-mul-ℚ⁺ d))
        ( L (inv-ℚ⁺ α *ℚ⁺ d) x y H))

  is-uniformly-continuous-is-lipschitz-function-Metric-Space :
    is-lipschitz-function-Metric-Space A B f →
    is-uniformly-continuous-function-Metric-Space A B f
  is-uniformly-continuous-is-lipschitz-function-Metric-Space =
    map-is-inhabited
      modulus-of-uniform-continuity-lipschitz-constant-function-Metric-Space

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  uniformly-continuous-lipschitz-function-Metric-Space :
    lipschitz-function-Metric-Space A B →
    uniformly-continuous-function-Metric-Space A B
  uniformly-continuous-lipschitz-function-Metric-Space f =
    ( map-lipschitz-function-Metric-Space A B f) ,
    ( is-uniformly-continuous-is-lipschitz-function-Metric-Space
      ( A)
      ( B)
      ( map-lipschitz-function-Metric-Space A B f)
      ( is-lipschitz-map-lipschitz-function-Metric-Space A B f))
```

### The product of Lipschitz constants of maps is a Lipschitz constant of their composition

```agda
module _
  {la la' lb lb' lc lc' : Level}
  (A : Metric-Space la la')
  (B : Metric-Space lb lb')
  (C : Metric-Space lc lc')
  (g : type-function-Metric-Space B C)
  (f : type-function-Metric-Space A B)
  where

  mul-comp-lipschitz-constant-function-Metric-Space :
    (α β : ℚ⁺) →
    is-lipschitz-constant-function-Metric-Space B C g α →
    is-lipschitz-constant-function-Metric-Space A B f β →
    is-lipschitz-constant-function-Metric-Space A C (g ∘ f) (α *ℚ⁺ β)
  mul-comp-lipschitz-constant-function-Metric-Space α β Hg Hf d x y Nxy =
    inv-tr
      ( λ ε → neighborhood-Metric-Space C ε (g (f x)) (g (f y)))
      ( associative-mul-ℚ⁺ α β d)
      ( Hg (β *ℚ⁺ d) (f x) (f y) (Hf d x y Nxy))
```

### The composition of Lipschitz maps is Lipschitz

```agda
module _
  {la la' lb lb' lc lc' : Level}
  (A : Metric-Space la la')
  (B : Metric-Space lb lb')
  (C : Metric-Space lc lc')
  where

  comp-is-lipschitz-function-Metric-Space :
    (g : type-function-Metric-Space B C) →
    (f : type-function-Metric-Space A B) →
    is-lipschitz-function-Metric-Space B C g →
    is-lipschitz-function-Metric-Space A B f →
    is-lipschitz-function-Metric-Space A C (g ∘ f)
  comp-is-lipschitz-function-Metric-Space g f =
    map-binary-trunc-Prop
      ( λ (α , Lg) (β , Lf) →
        α *ℚ⁺ β ,
        mul-comp-lipschitz-constant-function-Metric-Space A B C g f α β Lg Lf)
```

### Composition of Lipschitz functions

```agda
module _
  {la la' lb lb' lc lc' : Level}
  (A : Metric-Space la la')
  (B : Metric-Space lb lb')
  (C : Metric-Space lc lc')
  where

  comp-lipschitz-function-Metric-Space :
    lipschitz-function-Metric-Space B C →
    lipschitz-function-Metric-Space A B →
    lipschitz-function-Metric-Space A C
  comp-lipschitz-function-Metric-Space g f =
    ( map-lipschitz-function-Metric-Space B C g ∘
      map-lipschitz-function-Metric-Space A B f) ,
    ( comp-is-lipschitz-function-Metric-Space
      ( A)
      ( B)
      ( C)
      ( map-lipschitz-function-Metric-Space B C g)
      ( map-lipschitz-function-Metric-Space A B f)
      ( is-lipschitz-map-lipschitz-function-Metric-Space B C g)
      ( is-lipschitz-map-lipschitz-function-Metric-Space A B f))
```

### Being a Lipschitz map is homotopy invariant

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f g : type-function-Metric-Space A B)
  (f~g : f ~ g)
  where

  lipschitz-constant-htpy-function-Metric-Space :
    lipschitz-constant-function-Metric-Space A B f →
    lipschitz-constant-function-Metric-Space A B g
  lipschitz-constant-htpy-function-Metric-Space =
    tot
      ( λ α H d x y N →
        binary-tr
          ( neighborhood-Metric-Space B (α *ℚ⁺ d))
          ( f~g x)
          ( f~g y)
          ( H d x y N))

  is-lipschitz-htpy-function-Metric-Space :
    is-lipschitz-function-Metric-Space A B f →
    is-lipschitz-function-Metric-Space A B g
  is-lipschitz-htpy-function-Metric-Space =
    map-is-inhabited lipschitz-constant-htpy-function-Metric-Space
```

### Lipschitz maps preserve elements at bounded distance

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : type-function-Metric-Space A B)
  (Lf : is-lipschitz-function-Metric-Space A B f)
  where

  preserves-bounded-dist-is-lipschitz-function-Metric-Space :
    (x y : type-Metric-Space A) →
    bounded-dist-Metric-Space A x y →
    bounded-dist-Metric-Space B (f x) (f y)
  preserves-bounded-dist-is-lipschitz-function-Metric-Space x y =
    map-binary-exists
      ( is-upper-bound-dist-Metric-Space B (f x) (f y))
      ( mul-ℚ⁺)
      ( λ α d Hα → Hα d x y)
      ( Lf)

  map-element-at-bounded-dist-is-lipschitz-function-Metric-Space :
    (x : type-Metric-Space A) →
    element-at-bounded-dist-Metric-Space A x →
    element-at-bounded-dist-Metric-Space B (f x)
  map-element-at-bounded-dist-is-lipschitz-function-Metric-Space x =
    map-Σ
      ( bounded-dist-Metric-Space B (f x))
      ( f)
      ( preserves-bounded-dist-is-lipschitz-function-Metric-Space x)

  eq-value-map-element-at-bounded-dist-is-lipschitz-funtion-Metric-Space :
    (x : type-Metric-Space A) (N : element-at-bounded-dist-Metric-Space A x) →
    value-element-at-bounded-dist-Metric-Space
      ( B)
      ( f x)
      ( map-element-at-bounded-dist-is-lipschitz-function-Metric-Space x N) ＝
    f (value-element-at-bounded-dist-Metric-Space A x N)
  eq-value-map-element-at-bounded-dist-is-lipschitz-funtion-Metric-Space x N =
    refl
```

## External links

- [Lipschitz maps](https://en.wikipedia.org/wiki/Lipschitz_continuity) at
  Wikipedia
