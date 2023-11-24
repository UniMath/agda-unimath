# Whiskering homotopies

```agda
module foundation.whiskering-homotopies where

open import foundation-core.whiskering-homotopies public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.postcomposition-functions
open import foundation.universe-levels

open import foundation-core.function-types
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
