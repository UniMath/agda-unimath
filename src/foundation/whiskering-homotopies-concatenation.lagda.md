# Whiskering homotopies with respect to concatenation

```agda
module foundation.whiskering-homotopies-concatenation where
```

<details><summary>Imports</summary>

```agda
open import foundation.functoriality-dependent-function-types
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation
open import foundation.whiskering-operations

open import foundation-core.equivalences
open import foundation-core.homotopies
```

</details>

## Idea

Consider a homotopy `H : f ~ g` and a homotopy `K : I ~ J` between two
homotopies `I J : g ~ f`. The
{{#concept "left whiskering" Disambiguation="homotopies with respect to concatenation" Agda=left-whisker-concat-htpy}}
of `H` and `K` is a homotopy `H ∙h I ~ H ∙h J`. In other words, left whiskering of
homotopies with respect to concatenation is a
[whiskering operation](foundation.whiskering-operations.md)

```text
  (H : f ~ g) {I J : g ~ h} → I ~ J → H ∙h I ~ H ∙h K.
```

Similarly, we introduce
{{#concept 'right whiskering" Disambiguation="homotopies with respect to concatenation' Agda=right-whisker-concat-htpy}}
to be an operation

```text
  {H I : f ~ g} → H ~ I → (J : g ~ h) → H ∙h J ~ I ∙h J.
```

## Definitions

### Left whiskering of homotopies with respect to concatenation

Left whiskering of homotopies with respect to concatenation is an operation

```text
  (H : f ~ g) {I J : g ~ h} → I ~ J → H ∙h I ~ H ∙h K.
```

We implement the left whiskering operation of homotopies with respect to
concatenation as an instance of a general left whiskering operation.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  left-whisker-concat-htpy :
    left-whiskering-operation ((x : A) → B x) (_~_) (_∙h_) (_~_)
  left-whisker-concat-htpy H K x = left-whisker-concat (H x) (K x)
```

### Right whiskering of homotopies with respect to concatenation

Right whiskering of homotopies with respect to concatenation is an operation

```text
  {H I : f ~ g} → H ~ I → (J : g ~ h) → H ∙h J ~ I ∙h J.
```

We implement the right whiskering operation of homotopies with respect to
concatenation as an instance of a general right whiskering operation.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  right-whisker-concat-htpy :
    right-whiskering-operation ((x : A) → B x) (_~_) (_∙h_) (_~_)
  right-whisker-concat-htpy K J x = right-whisker-concat (K x) (J x)
```

## Properties

### Left whiskering of homotopies with respect to concatenation is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-equiv-left-whisker-concat-htpy :
    {f g h : (x : A) → B x} (H : f ~ g) {I J : g ~ h} →
    is-equiv (left-whisker-concat-htpy H {I} {J})
  is-equiv-left-whisker-concat-htpy H =
    is-equiv-map-Π-is-fiberwise-equiv
      ( λ x → is-equiv-left-whisker-concat (H x))
```

### Right whiskering of homotopies with respect to concatenation is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-equiv-right-whisker-concat-htpy :
    {f g h : (x : A) → B x} {H I : f ~ g} (J : g ~ h) →
    is-equiv (λ (K : H ~ I) → right-whisker-concat-htpy K J)
  is-equiv-right-whisker-concat-htpy J =
    is-equiv-map-Π-is-fiberwise-equiv
      ( λ x → is-equiv-right-whisker-concat (J x))
```

### The unit and absorption laws for left whiskering of homotopies with respect to concatenation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  left-unit-law-left-whisker-concat-htpy :
    {f g : (x : A) → B x} {I J : f ~ g} (K : I ~ J) →
    left-whisker-concat-htpy refl-htpy K ~ K
  left-unit-law-left-whisker-concat-htpy K x =
    left-unit-law-left-whisker-concat (K x)

  right-absorption-law-left-whisker-concat-htpy :
    {f g h : (x : A) → B x} (H : f ~ g) {I : g ~ h} →
    left-whisker-concat-htpy H (refl-htpy' I) ~ refl-htpy
  right-absorption-law-left-whisker-concat-htpy H x =
    right-absorption-law-left-whisker-concat (H x) _
```

### The unit and absorption laws for right whiskering of homotopies with respect to concatenation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  left-absorption-law-right-whisker-concat-htpy :
    {f g h : (x : A) → B x} {H : f ~ g} (J : g ~ h) →
    right-whisker-concat-htpy (refl-htpy' H) J ~ refl-htpy
  left-absorption-law-right-whisker-concat-htpy J x =
    left-absorption-law-right-whisker-concat _ (J x)

  right-unit-law-right-whisker-concat-htpy :
    {f g : (x : A) → B x} {I J : f ~ g} (K : I ~ J) →
    right-unit-htpy ∙h K ~
    right-whisker-concat-htpy K refl-htpy ∙h right-unit-htpy
  right-unit-law-right-whisker-concat-htpy K x =
    right-unit-law-right-whisker-concat (K x)
```
