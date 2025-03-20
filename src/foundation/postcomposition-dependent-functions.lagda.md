# Postcomposition of dependent functions

```agda
open import foundation.function-extensionality-axiom

module
  foundation.postcomposition-dependent-functions
  (funext : function-extensionality)
  where

open import foundation-core.postcomposition-dependent-functions public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality funext

open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps funext
open import foundation-core.identity-types
```

</details>

## Idea

Given a type `A` and a family of maps `f : {a : A} → X a → Y a`, the
{{#concept "postcomposition function" Disambiguation="of dependent functions by a family of maps" Agda=postcomp-Π}}
of dependent functions `(a : A) → X a` by the family of maps `f`

```text
  postcomp-Π A f : ((a : A) → X a) → ((a : A) → Y a)
```

is defined by `λ h x → f (h x)`.

Note that, since the definition of the family of maps `f` depends on the base
`A`, postcomposition of dependent functions does not generalize
[postcomposition of functions](foundation-core.postcomposition-functions.md) in
the same way that
[precomposition of dependent functions](foundation-core.precomposition-dependent-functions.md)
generalizes
[precomposition of functions](foundation-core.precomposition-functions.md). If
`A` can vary while keeping `f` fixed, we have necessarily reduced to the case of
[postcomposition of functions](foundation-core.postcomposition-functions.md).

## Properties

### The action on identifications of postcomposition by a family map

Consider a map `f : {x : A} → B x → C x` and two functions
`g h : (x : A) → B x`. Then the
[action on identifications](foundation.action-on-identifications-functions.md)
`ap (postcomp-Π A f)` fits in a
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
                   ap (postcomp-Π A f)
       (g ＝ h) -------------------------> (f ∘ g ＝ f ∘ h)
          |                                       |
  htpy-eq |                                       | htpy-eq
          ∨                                       ∨
       (g ~ h) --------------------------> (f ∘ g ~ f ∘ h).
                          f ·l_
```

Similarly, the action on identifications `ap (postcomp-Π A f)` fits in a
commuting square

```text
                    ap (postcomp-Π A f)
       (g ＝ h) -------------------------> (f ∘ g ＝ f ∘ h)
          ∧                                       ∧
  eq-htpy |                                       | eq-htpy
          |                                       |
       (g ~ h) --------------------------> (f ∘ g ~ f ∘ h).
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
    vertical-inv-equiv-coherence-square-maps
      ( ap (postcomp-Π A f))
      ( equiv-funext)
      ( equiv-funext)
      ( f ·l_)
      ( compute-htpy-eq-ap-postcomp-Π)
```
