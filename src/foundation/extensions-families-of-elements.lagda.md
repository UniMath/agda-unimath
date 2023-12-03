# Extensions of families of elements

```agda
module foundation.extensions-families-of-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.lifts-families-of-elements
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Consider a family of elements `a : I → A`, a type family `B` over `A` and a
[lift](foundation.lifts-families-of-elements.md)

```text
  b : (i : I) → B (a i)
```

of the family of elements `a`. An
{{#concept "extension" Disambiguation="family of elements"}} of `b` to `A`
consists of a family of elements `f : (x : A) → B x` equipped with a
[homotopy](foundation-core.homotopies.md) `f ∘ a ~ b`.

More generally, given a family of elements `a : (i : I) → A i`, a type family
`B` over `A`, and a dependent lift

```text
  b : (i : I) → B i (a i)
```

of the family of elements `A`, a
{{#concet "dependent extension" Disambiguation"family of elements"}} of `b` to
`A` consists of a family of elements

```text
  f : (i : I) (x : A i) → B i x
```

equipped with a homotopy `(i : I) → f i (a i) ＝ b i`.

## Definitions

### Evaluating families of elements at lifts of families of elements

We will define an evaluation map

```text
  ((b : B) (z : F b) → P b z) → ((a : A) → P (f a) (δ a))
```

for any type family `F : B → 𝒰` equipped with a lift `δ : (a : A) → F (f a)`.
This map takes a dependent function `h` and evaluates it at the values of the
lift `δ`.

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (a : (i : I) → A i)
  {B : (i : I) → A i → UU l3}
  where

  ev-dependent-lift-family-of-elements :
    ((i : I) (x : A i) → B i x) → dependent-lift-family-of-elements a B
  ev-dependent-lift-family-of-elements h i = h i (a i)

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} (a : I → A) {B : A → UU l3}
  where

  ev-lift-family-of-elements :
    ((x : A) → B x) → lift-family-of-elements a B
  ev-lift-family-of-elements h i = h (a i)
```

### Dependent extensions of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (a : (i : I) → A i)
  (B : (i : I) → A i → UU l3) (b : dependent-lift-family-of-elements a B)
  where

  is-dependent-extension-lift-family-of-elements :
    (f : (i : I) (x : A i) → B i x) → UU (l1 ⊔ l3)
  is-dependent-extension-lift-family-of-elements f =
    ev-dependent-lift-family-of-elements a f ~ b

  dependent-extension-lift-family-of-elements : UU (l1 ⊔ l2 ⊔ l3)
  dependent-extension-lift-family-of-elements =
    Σ ((i : I) (x : A i) → B i x) is-dependent-extension-lift-family-of-elements

  module _
    (f : dependent-extension-lift-family-of-elements)
    where

    family-of-elements-dependent-extension-lift-family-of-elements :
      (i : I) (x : A i) → B i x
    family-of-elements-dependent-extension-lift-family-of-elements = pr1 f

    is-dependent-extension-dependent-extension-lift-family-of-elements :
      is-dependent-extension-lift-family-of-elements
        ( family-of-elements-dependent-extension-lift-family-of-elements)
    is-dependent-extension-dependent-extension-lift-family-of-elements = pr2 f
```

### Dependent-extensions of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} (a : I → A)
  (B : A → UU l3) (b : lift-family-of-elements a B)
  where

  is-extension-lift-family-of-elements : (f : (x : A) → B x) → UU (l1 ⊔ l3)
  is-extension-lift-family-of-elements f = ev-lift-family-of-elements a f ~ b

  extension-lift-family-of-elements : UU (l1 ⊔ l2 ⊔ l3)
  extension-lift-family-of-elements =
    Σ ((x : A) → B x) is-extension-lift-family-of-elements

  module _
    (f : extension-lift-family-of-elements)
    where

    family-of-elements-extension-lift-family-of-elements : (x : A) → B x
    family-of-elements-extension-lift-family-of-elements = pr1 f

    is-extension-extension-lift-family-of-elements :
      is-extension-lift-family-of-elements
        ( family-of-elements-extension-lift-family-of-elements)
    is-extension-extension-lift-family-of-elements = pr2 f
```
