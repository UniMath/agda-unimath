# The action of functions on higher identifications

```agda
module foundation.action-on-higher-identifications-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.path-algebra
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-identifications
open import foundation-core.constant-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Any map `f : A → B` has an
{{#concept "action on higher identifications" Disambiguation="functions" Agda=ap²}},
which is a map

```text
  ap² f : (p ＝ q) → (ap f p ＝ ap f q)
```

Here `p q : x ＝ y` are [identifications](foundation-core.identity-types.md) in
the type `A`. The action of `f` on higher identifications is defined by

```text
  ap² f := ap (ap f).
```

## Definitions

### The action of functions on higher identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x y : A}
  {p q : x ＝ y} (f : A → B) (α : p ＝ q)
  where

  ap² : ap f p ＝ ap f q
  ap² = ap (ap f) α
```

## Properties

### The inverse law of the action of functions on higher identifications

Consider an identification `α : p ＝ q` between two identifications
`p q : x ＝ y` in a type `A`, and consider a map `f : A → B`. Then the square of
identifications

```text
                      ap² f (horizontal-inv-Id² α)
        ap f (inv p) ------------------------------> ap f (inv q)
             |                                            |
  ap-inv f p |                                            | ap-inv f q
             ∨                                            ∨
        inv (ap f p) ------------------------------> inv (ap f q)
                      horizontal-inv-Id² (ap² f α)
```

[commutes](foundation.commuting-squares-of-identifications.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x y : A}
  {p q : x ＝ y} (f : A → B) (α : p ＝ q)
  where

  compute-inv-ap² :
    coherence-square-identifications
      ( ap² f (horizontal-inv-Id² α))
      ( ap-inv f p)
      ( ap-inv f q)
      ( horizontal-inv-Id² (ap² f α))
  compute-inv-ap² =
    ( ( inv (horizontal-concat-Id² refl (ap-comp inv (ap f) α))) ∙
      ( nat-htpy (ap-inv f) α)) ∙
    ( horizontal-concat-Id² (ap-comp (ap f) inv α) refl)
```

### The action of the identity function on higher identifications is trivial

Consider an identification `α : p ＝ q` between two identifications
`p q : x ＝ y` in a type `A`. Then the square of identifications

```text
                ap² id α
       ap id p ----------> ap id q
          |                    |
  ap-id p |                    | ap-id q
          ∨                    ∨
          p -----------------> q
                     α
```

commutes.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x y : A}
  {p q : x ＝ y} (α : p ＝ q)
  where

  compute-id-ap² :
    coherence-square-identifications (ap² id α) (ap-id p) (ap-id q) α
  compute-id-ap² =
    horizontal-concat-Id² refl (inv (ap-id α)) ∙ nat-htpy ap-id α
```

### The action of a composite function on higher identifications

Consider an identification `α : p ＝ q` between two identifications
`p q : x ＝ y` in a type `A` and consider two functions `f : A → B` and
`g : B → C`. Then the square of identifications

```text
                         ap² (g ∘ f) α
          ap (g ∘ f) p -----------------> ap (g ∘ f) q
                |                               |
  ap-comp g f p |                               | ap-comp g f q
                ∨                               ∨
          ap g (ap f p) ----------------> ap g (ap f q)
                         ap² g (ap² f α)
```

commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {x y : A} {p q : x ＝ y} (g : B → C) (f : A → B) (α : p ＝ q)
  where

  compute-comp-ap² :
    coherence-square-identifications
      ( ap² (g ∘ f) α)
      ( ap-comp g f p)
      ( ap-comp g f q)
      ( (ap² g ∘ ap² f) α)
  compute-comp-ap² =
    ( horizontal-concat-Id² refl (inv (ap-comp (ap g) (ap f) α))) ∙
    ( nat-htpy (ap-comp g f) α)
```

### The action of a constant function on higher identifications is constant

Consider an identification `α : p ＝ q` between two identifications
`p q : x ＝ y` in a type `A` and consider an element `b : B`. Then the triangle
of identifications

```text
                 ap² (const b) α
  ap (const b) p ---------------> ap (const b) q
                 \              /
      ap-const b p \          / ap-const b q
                     ∨      ∨
                       refl
```

[commutes](foundation.commuting-triangles-of-identifications.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x y : A}
  {p q : x ＝ y} (α : p ＝ q)
  where

  compute-const-ap² :
    (b : B) →
    coherence-square-identifications
      ( ap² (const A b) α)
      ( ap-const b p)
      ( ap-const b q)
      ( refl)
  compute-const-ap² b =
    ( inv (horizontal-concat-Id² refl (ap-const refl α))) ∙
    ( nat-htpy (ap-const b) α)
```

## See also

- [Action of functions on identifications](foundation.action-on-identifications-functions.md)
- [Action of binary functions on identifications](foundation.action-on-identifications-binary-functions.md).
- [Action of dependent functions on identifications](foundation.action-on-identifications-dependent-functions.md).
