# Whiskering identifications

```agda
module foundation.whiskering-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
```

</details>

## Idea

Consider two [identifications](foundation-core.identity-types.md) `p q : x ＝ y`
in a type `A`. The whiskering operations are operations that take
identifications `p ＝ q` to identifications `r ∙ p ＝ r ∙ q` or to
identifications `p ∙ r ＝ q ∙ r`.

The
{{#concept "left whiskering" Disambiguation="identifcations" Agda=left-whisker-identification"}}
operation takes an identification `r : z ＝ x` and an identification `p ＝ q` to
an identification `r ∙ p ＝ r ∙ q`. Similarly, the
{{#concept "right whiskering" Disambiguation="identifications" Agda=right-whisker-identification"}}
operation takes an identification `r : y ＝ z` and an identification `p ＝ q` to
an identification `p ∙ r ＝ q ∙ r`.

The whiskering operations can be defined by the
[acion on identifications](foundation.action-on-identifications-functions.md) of
concatenation. Since concatenation on either side is an
[equivalence](foundation-core.equivalences.md), it follows that the whiskering
operations are equivalences.

## Definitions

### Left whiskering of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  left-whisker-identification :
    (p : x ＝ y) {q q' : y ＝ z} → q ＝ q' → (p ∙ q) ＝ (p ∙ q')
  left-whisker-identification p β = ap (p ∙_) β
```

### Right whiskering of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  right-whisker-identification :
    {p p' : x ＝ y} → p ＝ p' → (q : y ＝ z) → (p ∙ q) ＝ (p' ∙ q)
  right-whisker-identification α q = ap (_∙ q) α
```

## Properties

### Left whiskering of identifications is an equivalence

```agda
module _
  {l : Level} {A : UU l} {x y z : A} (p : x ＝ y) {q q' : y ＝ z}
  where

  is-equiv-left-whisker-identification :
    is-equiv (left-whisker-identification p {q} {q'})
  is-equiv-left-whisker-identification =
    is-emb-is-equiv (is-equiv-concat p z) q q'

  equiv-left-whisker-identification : (q ＝ q') ≃ (p ∙ q ＝ p ∙ q')
  pr1 equiv-left-whisker-identification =
    left-whisker-identification p
  pr2 equiv-left-whisker-identification =
    is-equiv-left-whisker-identification
```

### Right whiskering of identification is an equivalence

```agda
module _
  {l : Level} {A : UU l} {x y z : A} {p p' : x ＝ y} (q : y ＝ z)
  where

  is-equiv-right-whisker-identification :
    is-equiv (λ (α : p ＝ p') → right-whisker-identification α q)
  is-equiv-right-whisker-identification =
    is-emb-is-equiv (is-equiv-concat' x q) p p'

  equiv-right-whisker-identification : (p ＝ p') ≃ (p ∙ q ＝ p' ∙ q)
  pr1 equiv-right-whisker-identification α =
    right-whisker-identification α q
  pr2 equiv-right-whisker-identification =
    is-equiv-right-whisker-identification
```

### The unit and absorption laws for left whiskering of identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  left-unit-law-left-whisker-identification :
    {x y : A} {p p' : x ＝ y} (α : p ＝ p') →
    left-whisker-identification refl α ＝ α
  left-unit-law-left-whisker-identification refl = refl

  right-absorption-law-left-whisker-identification :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    left-whisker-identification p (refl {x = q}) ＝ refl
  right-absorption-law-left-whisker-identification p q = refl
```

### The unit and absorption laws for right whiskering of identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  right-unit-law-right-whisker-identification :
    {x y : A} {p p' : x ＝ y} (α : p ＝ p') →
    right-whisker-identification α refl ＝
    right-unit ∙ α ∙ inv right-unit
  right-unit-law-right-whisker-identification {p = refl} refl = refl

  left-absorption-law-right-whisker-identification :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    right-whisker-identification (refl {x = p}) q ＝ refl
  left-absorption-law-right-whisker-identification p q = refl
```

### Commutativity of left and right whiskering of identifications

Consider four identifications `p p' : x ＝ y` and `q q' : y ＝ z` in a type `A`.
Then the square of identifications

```text
                         right-whisker α q
                 p ∙ q ---------------------> p' ∙ q
                   |                             |
  left-whisker p β |                             | left-whisker p' β
                   ∨                             ∨
                 p ∙ q' --------------------> p' ∙ q'
                         right-whisker α q'
```

commutes. There are at least two natural ways in which this square is seen to
commute:

1. The square commutes by naturality of the homotopy
   `α ↦ left-whisker-identification α β`.
2. The transposed square commutes by the naturality of the homotopy
   `β ↦ right-whisker-identification α β`.

These two ways in which the square commutes are inverse to each other.

**Note.** The following statements could have been formalized using [commuting squares of identifications](foundation.commuting-squares-of-identifications.md). However, in order to avoid cyclic module dependencies in the library we avoid doing so.

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  commutative-left-whisker-right-whisker-identification :
    {q q' : y ＝ z} (β : q ＝ q') {p p' : x ＝ y} (α : p ＝ p') →
    left-whisker-identification p β ∙ right-whisker-identification α q' ＝
    right-whisker-identification α q ∙ left-whisker-identification p' β
  commutative-left-whisker-right-whisker-identification β =
    nat-htpy (λ α → left-whisker-identification α β)

  commutative-right-whisker-left-whisker-identification :
    {p p' : x ＝ y} (α : p ＝ p') {q q' : y ＝ z} (β : q ＝ q') →
    right-whisker-identification α q ∙ left-whisker-identification p' β ＝
    left-whisker-identification p β ∙ right-whisker-identification α q'
  commutative-right-whisker-left-whisker-identification α =
    nat-htpy (right-whisker-identification α)

  compute-inv-commutative-left-whisker-right-whisker-identification :
    {q q' : y ＝ z} (β : q ＝ q') {p p' : x ＝ y} (α : p ＝ p') →
    inv (commutative-right-whisker-left-whisker-identification α β) ＝
    commutative-left-whisker-right-whisker-identification β α
  compute-inv-commutative-left-whisker-right-whisker-identification refl refl =
    refl
```
