# Whiskering homotopies

```agda
module foundation.whiskering-homotopies where

open import foundation-core.whiskering-homotopies public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-identifications
open import foundation.homotopy-induction
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-identifications

open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.postcomposition-functions
open import foundation-core.precomposition-functions
```

</details>

## Idea

There are two **whiskering operations** on
[homotopies](foundation-core.homotopies.md). The **left whiskering** operation
assumes a diagram of the form

```text
      f
    ----->     h
  A -----> B -----> C
      g
```

and is defined to be a function `h ·l_ : (f ~ g) → (h ∘ f ~ h ∘ g)`. The **right
whiskering** operation assumes a diagram of the form

```text
               g
      f      ----->
  A -----> B -----> C
               h
```

and is defined to be a function `_·r f : (g ~ h) → (g ∘ f ~ h ∘ f)`.

**Note**: The infix whiskering operators `_·l_` and `_·r_` use the
[middle dot](https://codepoints.net/U+00B7) `·` (agda-input: `\cdot`
`\centerdot`), as opposed to the infix homotopy concatenation operator `_∙h_`
which uses the [bullet operator](https://codepoints.net/U+2219) `∙` (agda-input:
`\.`). If these look the same in your editor, we suggest that you change your
font. For more details, see [How to install](HOWTO-INSTALL.md).

## Properties

### Computation of function extensionality on whiskerings

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  { f g : B → C} (h : A → B)
  where

  compute-eq-htpy-htpy-eq-right-whisker :
    ( p : f ＝ g) →
    eq-htpy ((htpy-eq p) ·r h) ＝ ap (precomp h C) p
  compute-eq-htpy-htpy-eq-right-whisker refl =
    eq-htpy-refl-htpy (f ∘ h)

  compute-eq-right-whisker-htpy :
    ( H : f ~ g) →
    eq-htpy (H ·r h) ＝ ap (precomp h C) (eq-htpy H)
  compute-eq-right-whisker-htpy H =
    ( ap
      ( λ K → eq-htpy (K ·r h))
      ( inv (is-section-eq-htpy H))) ∙
    ( compute-eq-htpy-htpy-eq-right-whisker (eq-htpy H))
```

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  { f g : A → B} (h : B → C)
  where

  compute-eq-htpy-htpy-eq-left-whisker :
    ( p : f ＝ g) → eq-htpy (h ·l (htpy-eq p)) ＝ ap (postcomp A h) p
  compute-eq-htpy-htpy-eq-left-whisker refl =
    eq-htpy-refl-htpy (h ∘ f)

  compute-eq-left-whisker-htpy :
    (H : f ~ g) →
    eq-htpy (h ·l H) ＝ ap (postcomp A h) (eq-htpy H)
  compute-eq-left-whisker-htpy H =
    ( ap
      ( λ K → eq-htpy (h ·l K))
      ( inv (is-section-eq-htpy H))) ∙
    ( compute-eq-htpy-htpy-eq-left-whisker (eq-htpy H))
```

### Whiskering a square of homotopies by a homotopy is an equivalence

A
[commuting square of homotopies](foundation.commuting-squares-of-homotopies.md)
may be whiskered by a homotopy `L` on the left or right, which results in a
commuting square of homotopies with `L` appended or prepended to the two ways of
going around the square.

Diagrammatically, we may turn the pasting diagram

```text
        H
    f ~~~~~ g
    ︴      ︴
 H' ︴  ⇗   ︴ K
    ︴      ︴
   g' ~~~~~ h ~~~~~ k
       K'       L
```

into a commmuting square

```text
        H
    f ~~~~~ g
    ︴      ︴
 H' ︴  ⇗   ︴K ∙h L
    ︴      ︴
   g' ~~~~~ k
     K' ∙h L   ,
```

and similarly for the other side.

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  { f g g' h k : A → B}
  where

  module _
    ( H : f ~ g) (H' : f ~ g') {K : g ~ h} {K' : g' ~ h} (L : h ~ k)
    where

    equiv-right-whisker-coherence-square-htpy :
      ( coherence-square-homotopies H H' K K') ≃
      ( coherence-square-homotopies H H' (K ∙h L) (K' ∙h L))
    equiv-right-whisker-coherence-square-htpy =
      equiv-Π-equiv-family
        ( λ a →
          equiv-right-whisker-coherence-square-identifications
            ( H a)
            ( H' a)
            ( K a)
            ( K' a)
            ( L a))

    right-whisker-coherence-square-htpy :
      coherence-square-homotopies H H' K K' →
      coherence-square-homotopies H H' (K ∙h L) (K' ∙h L)
    right-whisker-coherence-square-htpy = map-equiv equiv-right-whisker-coherence-square-htpy

    right-unwhisker-coherence-square-htpy :
      coherence-square-homotopies H H' (K ∙h L) (K' ∙h L) →
      coherence-square-homotopies H H' K K'
    right-unwhisker-coherence-square-htpy = map-inv-equiv equiv-right-whisker-coherence-square-htpy

  module _
    ( L : k ~ f) {H : f ~ g} {H' : f ~ g'} {K : g ~ h} {K' : g' ~ h}
    where

    equiv-left-whisker-coherence-square-htpy :
      ( coherence-square-homotopies H H' K K') ≃
      ( coherence-square-homotopies (L ∙h H) (L ∙h H') K K')
    equiv-left-whisker-coherence-square-htpy =
      equiv-Π-equiv-family
        ( λ a →
          equiv-left-whisker-coherence-square-identifications
            ( L a)
            ( H a)
            ( H' a)
            ( K a)
            ( K' a))

    left-whisker-coherence-square-htpy :
      coherence-square-homotopies H H' K K' →
      coherence-square-homotopies (L ∙h H) (L ∙h H') K K'
    left-whisker-coherence-square-htpy = map-equiv equiv-left-whisker-coherence-square-htpy

    left-unwhisker-coherence-square-htpy :
      coherence-square-homotopies (L ∙h H) (L ∙h H') K K' →
      coherence-square-homotopies H H' K K'
    left-unwhisker-coherence-square-htpy = map-inv-equiv equiv-left-whisker-coherence-square-htpy

module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  { f g h h' k m : A → B}
  ( H : f ~ g) {K : g ~ h} {K' : g ~ h'} {L : h ~ k} {L' : h' ~ k} (M : k ~ m)
  where

  equiv-double-whisker-coherence-square-htpy :
    ( coherence-square-homotopies K K' L L') ≃
    ( coherence-square-homotopies (H ∙h K) (H ∙h K') (L ∙h M) (L' ∙h M))
  equiv-double-whisker-coherence-square-htpy =
    equiv-Π-equiv-family
      ( λ a →
        equiv-double-whisker-square-identifications
          ( H a)
          ( K a)
          ( K' a)
          ( L a)
          ( L' a)
          ( M a))

  double-whisker-coherence-square-htpy :
    ( coherence-square-homotopies K K' L L') →
    ( coherence-square-homotopies (H ∙h K) (H ∙h K') (L ∙h M) (L' ∙h M))
  double-whisker-coherence-square-htpy = map-equiv equiv-double-whisker-coherence-square-htpy

  both-unwhisker-coherence-square-htpy :
    ( coherence-square-homotopies (H ∙h K) (H ∙h K') (L ∙h M) (L' ∙h M)) →
    ( coherence-square-homotopies K K' L L')
  both-unwhisker-coherence-square-htpy = map-inv-equiv equiv-double-whisker-coherence-square-htpy
```

### Whiskering a square of homotopies by a map

Given a square of homotopies

```text
        H
    g ~~~~~ h
    ︴      ︴
 H' ︴  ⇗   ︴ K
    ︴      ︴
   h' ~~~~~ k
       K'
```

and a map `f`, we may whisker it by a map on the left into a square of
homotopies

```text
           f ·l H
         fg ~~~~~ fh
         ︴        ︴
 f ·l H' ︴   ⇗    ︴f ·l K
         ︴        ︴
        fh' ~~~~~ fk
           f ·l K' ,
```

and similarly we may whisker it on the right.

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  ( f : B → C) {g h h' k : A → B}
  ( H : g ~ h) (H' : g ~ h') {K : h ~ k} {K' : h' ~ k}
  where

  ap-left-whisker-coherence-square-homotopies :
    coherence-square-homotopies H H' K K' →
    coherence-square-homotopies (f ·l H) (f ·l H') (f ·l K) (f ·l K')
  ap-left-whisker-coherence-square-homotopies α a =
    map-coherence-square-identifications f (H a) (H' a) (K a) (K' a) (α a)

module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  { g h h' k : B → C} (H : g ~ h) (H' : g ~ h') {K : h ~ k} {K' : h' ~ k}
  ( f : A → B)
  where

  ap-right-whisker-coherence-square-homotopies :
    coherence-square-homotopies H H' K K' →
    coherence-square-homotopies (H ·r f) (H' ·r f) (K ·r f) (K' ·r f)
  ap-right-whisker-coherence-square-homotopies α = α ·r f
```

### The two definitions of horizontal concatenation of homotopies agree

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  coh-left-unit-horizontal-concat-htpy :
    {f : (x : A) → B x} {g g' : {x : A} → B x → C x}
    (G : {x : A} → g {x} ~ g' {x}) →
    horizontal-concat-htpy (refl-htpy' f) G ~
    horizontal-concat-htpy' (refl-htpy' f) G
  coh-left-unit-horizontal-concat-htpy G = inv-htpy-right-unit-htpy

  coh-right-unit-horizontal-concat-htpy :
    {f f' : (x : A) → B x} {g : {x : A} → B x → C x}
    (F : f ~ f') →
    horizontal-concat-htpy F (refl-htpy' g) ~
    horizontal-concat-htpy' F (refl-htpy' g)
  coh-right-unit-horizontal-concat-htpy F = right-unit-htpy

  coh-horizontal-concat-htpy :
    {f f' : (x : A) → B x} {g g' : {x : A} → B x → C x}
    (F : f ~ f') (G : {x : A} → g {x} ~ g' {x}) →
    horizontal-concat-htpy F G ~ horizontal-concat-htpy' F G
  coh-horizontal-concat-htpy {f} F G =
    ind-htpy f
      ( λ f' F → horizontal-concat-htpy F G ~ horizontal-concat-htpy' F G)
      ( coh-left-unit-horizontal-concat-htpy G)
      ( F)
```

## See also

- For interactions between whiskering and exponentiation, see
  [`foundation.composition-algebra`](foundation.composition-algebra.md).
