# Whiskering homotopies with respect to composition

```agda
module foundation.whiskering-homotopies-composition where

open import foundation-core.whiskering-homotopies-composition public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation-core.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-identifications
open import foundation.homotopy-induction
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

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

and is defined to be a function `H ↦ h ·l H : (f ~ g) → (h ∘ f ~ h ∘ g)`. The
**right whiskering** operation assumes a diagram of the form

```text
               g
      f      ----->
  A -----> B -----> C
               h
```

and is defined to be a function `H ↦ H ·r f : (g ~ h) → (g ∘ f ~ h ∘ f)`.

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
    eq-htpy (htpy-eq p ·r h) ＝ ap (precomp h C) p
  compute-eq-htpy-htpy-eq-right-whisker refl =
    eq-htpy-refl-htpy (f ∘ h)

  compute-eq-right-whisker-comp :
    ( H : f ~ g) →
    eq-htpy (H ·r h) ＝ ap (precomp h C) (eq-htpy H)
  compute-eq-right-whisker-comp H =
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
    ( p : f ＝ g) → eq-htpy (h ·l htpy-eq p) ＝ ap (postcomp A h) p
  compute-eq-htpy-htpy-eq-left-whisker refl =
    eq-htpy-refl-htpy (h ∘ f)

  compute-eq-left-whisker-comp :
    (H : f ~ g) →
    eq-htpy (h ·l H) ＝ ap (postcomp A h) (eq-htpy H)
  compute-eq-left-whisker-comp H =
    ( ap
      ( λ K → eq-htpy (h ·l K))
      ( inv (is-section-eq-htpy H))) ∙
    ( compute-eq-htpy-htpy-eq-left-whisker (eq-htpy H))
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
