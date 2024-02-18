# Postcomposition of dependent functions

```agda
module foundation.postcomposition-dependent-functions where

open import foundation-core.postcomposition-dependent-functions public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

Given a type `A` and a dependent map `f : {a : A} → X a → Y a`, the
{{#concept "dependent postcomposition function" Agda=postcomp-Π}}

```text
  f ∘ - : ((a : A) → X a) → ((a : A) → Y a)
```

is defined by `λ h x → f (h x)`.

Note that, as opposed to
[precomposition of dependent functions](foundation-core.precomposition-dependent-functions.md),
the use-case for postcomposition of dependent functions is very limited, since
the definition of `f` depends on the particular choice of `A`. Once we allow `A`
to vary while keeping `f` fixed, we reduce to the case of
[postcomposition of (nondependent) functions](foundation-core.postcomposition-functions.md).

## Properties

### The action on identifications of postcomposition by a map

Consider a map `f : {x : A} → B x → C x` and two functions
`g h : (x : A) → B x`. Then the
[action on identifications](foundation.action-on-identifications-functions.md)
`ap (postcomp-Π A f)` fits in a
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
                   ap (postcomp-Π A f)
       (g ＝ h) -------------------------> (g ∘ f ＝ h ∘ f)
          |                                       |
  htpy-eq |                                       | htpy-eq
          V                                       V
       (g ~ h) --------------------------> (g ∘ f ~ h ∘ f).
                          f ·l_
```

Similarly, the action on identifications `ap (postcomp-Π A f)` also fits in a
commuting square

```text
                    ap (postcomp-Π A f)
       (g ＝ h) -------------------------> (g ∘ f ＝ h ∘ f)
          ^                                       ^
  eq-htpy |                                       | eq-htpy
          |                                       |
       (g ~ h) --------------------------> (g ∘ f ~ h ∘ f).
                          f ·l_
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : {x : A} → B x → C x) {g h : (x : A) → B x}
  where

  compute-htpy-eq-ap-postcomp-Π :
    coherence-square-maps
      ( ap (postcomp-Π A f) {x = g} {y = h})
      ( htpy-eq)
      ( htpy-eq)
      ( f ·l_)
  compute-htpy-eq-ap-postcomp-Π refl = refl

  compute-eq-htpy-ap-postcomp-Π :
    coherence-square-maps
      ( f ·l_)
      ( eq-htpy)
      ( eq-htpy)
      ( ap (postcomp-Π A f))
  compute-eq-htpy-ap-postcomp-Π =
    coherence-square-maps-inv-equiv-vertical
      ( ap (postcomp-Π A f))
      ( equiv-funext)
      ( equiv-funext)
      ( f ·l_)
      ( compute-htpy-eq-ap-postcomp-Π)
```
