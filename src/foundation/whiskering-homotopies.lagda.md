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
open import foundation.function-extensionality
open import foundation.path-algebra
open import foundation.postcomposition-functions
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
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

  compute-eq-htpy-htpy-eq-right-whisk :
    ( p : f ＝ g) →
    eq-htpy ((htpy-eq p) ·r h) ＝ ap (precomp h C) p
  compute-eq-htpy-htpy-eq-right-whisk refl =
    eq-htpy-refl-htpy (f ∘ h)

  compute-eq-htpy-right-whisk :
    ( H : f ~ g) →
    eq-htpy (H ·r h) ＝ ap (precomp h C) (eq-htpy H)
  compute-eq-htpy-right-whisk H =
    ( ap
      ( λ K → eq-htpy (K ·r h))
      ( inv (is-section-eq-htpy H))) ∙
    ( compute-eq-htpy-htpy-eq-right-whisk (eq-htpy H))
```

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  { f g : A → B} (h : B → C)
  where

  compute-eq-htpy-htpy-eq-left-whisk :
    ( p : f ＝ g) → eq-htpy (h ·l (htpy-eq p)) ＝ ap (postcomp A h) p
  compute-eq-htpy-htpy-eq-left-whisk refl =
    eq-htpy-refl-htpy (h ∘ f)

  compute-eq-htpy-left-whisk :
    (H : f ~ g) →
    eq-htpy (h ·l H) ＝ ap (postcomp A h) (eq-htpy H)
  compute-eq-htpy-left-whisk H =
    ( ap
      ( λ K → eq-htpy (h ·l K))
      ( inv (is-section-eq-htpy H))) ∙
    ( compute-eq-htpy-htpy-eq-left-whisk (eq-htpy H))
```

### Whiskerings of higher homotopies are equivalences

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  { f g g' h k : A → B}
  where

  module _
    ( H : f ~ g) (H' : f ~ g') {K : g ~ h} {K' : g' ~ h} (L : h ~ k)
    where

    equiv-right-whisk-square-htpy :
      ( coherence-square-homotopies H H' K K') ≃
      ( coherence-square-homotopies H H' (K ∙h L) (K' ∙h L))
    equiv-right-whisk-square-htpy =
      equiv-Π-equiv-family
        ( λ a → equiv-right-whisk-square-identification (H a) (H' a) (L a))

    right-whisk-square-htpy :
      coherence-square-homotopies H H' K K' →
      coherence-square-homotopies H H' (K ∙h L) (K' ∙h L)
    right-whisk-square-htpy = map-equiv equiv-right-whisk-square-htpy

    right-unwhisk-square-htpy :
      coherence-square-homotopies H H' (K ∙h L) (K' ∙h L) →
      coherence-square-homotopies H H' K K'
    right-unwhisk-square-htpy = map-inv-equiv equiv-right-whisk-square-htpy

  module _
    ( H : k ~ f) {K : f ~ g} {K' : f ~ g'} {L : g ~ h} {L' : g' ~ h}
    where

    equiv-left-whisk-square-htpy :
      ( coherence-square-homotopies K K' L L') ≃
      ( coherence-square-homotopies (H ∙h K) (H ∙h K') L L')
    equiv-left-whisk-square-htpy =
      equiv-Π-equiv-family
        ( λ a → equiv-left-whisk-square-identification (H a))

    left-whisk-square-htpy :
      coherence-square-homotopies K K' L L' →
      coherence-square-homotopies (H ∙h K) (H ∙h K') L L'
    left-whisk-square-htpy = map-equiv equiv-left-whisk-square-htpy

    left-unwhisk-square-htpy :
      coherence-square-homotopies (H ∙h K) (H ∙h K') L L' →
      coherence-square-homotopies K K' L L'
    left-unwhisk-square-htpy = map-inv-equiv equiv-left-whisk-square-htpy

module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  { f g h h' k m : A → B}
  ( H : f ~ g) {K : g ~ h} {K' : g ~ h'} {L : h ~ k} {L' : h' ~ k} (M : k ~ m)
  where

  equiv-both-whisk-square-htpy :
    ( coherence-square-homotopies K K' L L') ≃
    ( coherence-square-homotopies (H ∙h K) (H ∙h K') (L ∙h M) (L' ∙h M))
  equiv-both-whisk-square-htpy =
    equiv-Π-equiv-family
      ( λ a → equiv-both-whisk-square-identifications (H a) (M a))

  both-whisk-square-htpy :
    ( coherence-square-homotopies K K' L L') →
    ( coherence-square-homotopies (H ∙h K) (H ∙h K') (L ∙h M) (L' ∙h M))
  both-whisk-square-htpy = map-equiv equiv-both-whisk-square-htpy

  both-unwhisk-square-htpy :
    ( coherence-square-homotopies (H ∙h K) (H ∙h K') (L ∙h M) (L' ∙h M)) →
    ( coherence-square-homotopies K K' L L')
  both-unwhisk-square-htpy = map-inv-equiv equiv-both-whisk-square-htpy
```

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  ( f : B → C) {g h h' k : A → B}
  ( H : g ~ h) (H' : g ~ h') {K : h ~ k} {K' : h' ~ k}
  where

  ap-left-whisk-coherence-square-homotopies :
    coherence-square-homotopies H H' K K' →
    coherence-square-homotopies (f ·l H) (f ·l H') (f ·l K) (f ·l K')
  ap-left-whisk-coherence-square-homotopies α a =
    coherence-square-identifications-ap f (H a) (H' a) (K a) (K' a) (α a)
```
