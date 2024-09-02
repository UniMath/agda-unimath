# Mere homotopies

```agda
module foundation.mere-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.homotopies
open import foundation-core.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "mere homotopy" Agda=mere-htpy}} between two dependent functions
`f g : (a : A) → B a` is an element of the
[propositional truncation](foundation.propositional-truncations.md)

```text
  ║ f ~ g ║₋₁
```

of the type of [homotopies](foundation-core.homotopies.md) between `f` and `g`.

## Definitions

### Mere homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f g : (x : A) → B x)
  where

  mere-htpy-Prop : Prop (l1 ⊔ l2)
  mere-htpy-Prop = trunc-Prop (f ~ g)

  mere-htpy : UU (l1 ⊔ l2)
  mere-htpy = type-trunc-Prop (f ~ g)

  is-prop-mere-htpy : is-prop mere-htpy
  is-prop-mere-htpy = is-prop-type-trunc-Prop
```

### The mere homotopy component of a function type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x)
  where

  mere-htpy-component : UU (l1 ⊔ l2)
  mere-htpy-component = Σ ((x : A) → B x) (mere-htpy f)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f : (x : A) → B x}
  (g : mere-htpy-component f)
  where

  map-mere-htpy-component : (x : A) → B x
  map-mere-htpy-component = pr1 g

  mere-htpy-base-function-mere-htpy-component :
    mere-htpy f map-mere-htpy-component
  mere-htpy-base-function-mere-htpy-component = pr2 g
```

## Properties

### The mere homotopy relation is an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    refl-mere-htpy : (f : (x : A) → B x) → mere-htpy f f
    refl-mere-htpy f = unit-trunc-Prop refl-htpy

  abstract
    transitive-mere-htpy :
      is-transitive (mere-htpy {B = B})
    transitive-mere-htpy f g h r s =
      apply-twice-universal-property-trunc-Prop r s
        ( mere-htpy-Prop f h)
        ( λ H K → unit-trunc-Prop (K ∙h H))

  abstract
    symmetric-mere-htpy : is-symmetric (mere-htpy {B = B})
    symmetric-mere-htpy f g r =
      apply-universal-property-trunc-Prop r
        ( mere-htpy-Prop g f)
        ( λ H → unit-trunc-Prop (inv-htpy H))

  mere-htpy-Equivalence-Relation :
    equivalence-relation (l1 ⊔ l2) ((x : A) → B x)
  pr1 mere-htpy-Equivalence-Relation = mere-htpy-Prop
  pr1 (pr2 mere-htpy-Equivalence-Relation) = refl-mere-htpy
  pr1 (pr2 (pr2 mere-htpy-Equivalence-Relation)) = symmetric-mere-htpy
  pr2 (pr2 (pr2 mere-htpy-Equivalence-Relation)) = transitive-mere-htpy
```

### Two functions are merely homotopic if and only if they are merely equal

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f g : (x : A) → B x)
  where

  abstract
    mere-eq-mere-htpy : mere-htpy f g → mere-eq f g
    mere-eq-mere-htpy = map-trunc-Prop eq-htpy

  abstract
    mere-htpy-mere-eq : mere-eq f g → mere-htpy f g
    mere-htpy-mere-eq = map-trunc-Prop htpy-eq

  equiv-mere-htpy-mere-eq : mere-eq f g ≃ mere-htpy f g
  equiv-mere-htpy-mere-eq = equiv-trunc-Prop equiv-funext
```

### The base function of a mere homotopy component

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x)
  where

  base-function-mere-htpy-component : mere-htpy-component f
  pr1 base-function-mere-htpy-component = f
  pr2 base-function-mere-htpy-component = refl-mere-htpy f
```

### Any two elements functions in a mere homotopy component are merely homotopy

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x)
  where

  abstract
    mere-htpy-mere-htpy-component :
      (g h : mere-htpy-component f) →
      mere-htpy (map-mere-htpy-component g) (map-mere-htpy-component h)
    mere-htpy-mere-htpy-component g h =
      transitive-mere-htpy
        ( map-mere-htpy-component g)
        ( f)
        ( map-mere-htpy-component h)
        ( mere-htpy-base-function-mere-htpy-component h)
        ( symmetric-mere-htpy f
          ( map-mere-htpy-component g)
          ( mere-htpy-base-function-mere-htpy-component g))
```

### The mere homotopy component of any function is connected

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x)
  where

  abstract
    is-0-connected-mere-htpy-component : is-0-connected (mere-htpy-component f)
    is-0-connected-mere-htpy-component =
      is-0-connected-mere-eq
        ( base-function-mere-htpy-component f)
        ( λ (g , H) →
          {!!})
```

### The mere homotopy component of a function is an ∞-group
