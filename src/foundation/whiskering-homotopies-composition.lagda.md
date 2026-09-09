# Whiskering homotopies with respect to composition

```agda
module foundation.whiskering-homotopies-composition where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

There are two
{{#concept "whiskering operations" Disambiguation="homotopies with respect to compostion"}}
on [homotopies](foundation-core.homotopies.md) with respect to composition. The
{{#concept "left whiskering" Disambiguation="homotopies with respect to composition" Agda=left-whisker-comp}}
operation of homotopies with respect to composition assumes a diagram of maps of
the form

```text
      f
    ----->     h
  A -----> B -----> C
      g
```

and is defined to be the function `H ↦ h ·l H : (f ~ g) → (h ∘ f ~ h ∘ g)`. The
{{#concept "right whiskering" Disambiguation="homotopies with respect to composition" Agda=right-whisker-comp}}
operation of homotopies with respect to composition assumes a diagram of maps
the form

```text
               g
      f      ----->
  A -----> B -----> C
               h
```

and is defined to be the function `H ↦ H ·r f : (g ~ h) → (g ∘ f ~ h ∘ f)`.

**Note.** The infix whiskering operators `_·l_` and `_·r_` use the
[middle dot](https://codepoints.net/U+00B7) `·` (agda-input: `\cdot`
`\centerdot`), as opposed to the infix homotopy concatenation operator `_∙h_`
which uses the [bullet operator](https://codepoints.net/U+2219) `∙` (agda-input:
`\.`). If these look the same in your editor, we suggest that you change your
font. For more details, see [How to install](HOWTO-INSTALL.md).

**Note.** We will define the whiskering operations with respect to function
composition for dependent functions. The definition of `whiskering-operations`
in [whiskering operations](foundation.whiskering-operations.md) does not support
this level of generality, so we will not be able to use it here.

## Definitions

### Left whiskering of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  left-whisker-comp :
    (h : {x : A} → B x → C x)
    {f g : (x : A) → B x} → f ~ g → h ∘ f ~ h ∘ g
  left-whisker-comp h H x = ap h (H x)

  infixr 17 _·l_
  _·l_ = left-whisker-comp
```

### Right whiskering of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  where

  right-whisker-comp :
    {g h : {x : A} (y : B x) → C x y}
    (H : {x : A} → g {x} ~ h {x})
    (f : (x : A) → B x) → g ∘ f ~ h ∘ f
  right-whisker-comp H f x = H (f x)

  infixl 16 _·r_
  _·r_ = right-whisker-comp
```

### Double whiskering of homotopies

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  {C : (x : A) → B x → UU l3} {D : (x : A) → B x → UU l4}
  where

  double-whisker-comp :
    (left : {x : A} {y : B x} → C x y → D x y)
    {g h : {x : A} (y : B x) → C x y}
    (H : {x : A} → g {x} ~ h {x})
    (right : (x : A) → B x) → left ∘ g ∘ right ~ left ∘ h ∘ right
  double-whisker-comp left H right = left ·l H ·r right
```

## Properties

### The left and right whiskering operations commute

We have the coherence

```text
  (h ·l H) ·r h' ~ h ·l (H ·r h')
```

definitionally.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  {C : {x : A} → B x → UU l3} {D : {x : A} → B x → UU l4}
  {f g : {x : A} (y : B x) → C y}
  where

  coherence-double-whisker-comp :
    (h : {x : A} {y : B x} → C y → D y)
    (H : {x : A} → f {x} ~ g {x})
    (h' : (x : A) → B x) →
    (h ·l H) ·r h' ~ h ·l (H ·r h')
  coherence-double-whisker-comp h H h' = refl-htpy
```

### Unit laws and absorption laws for whiskering homotopies

The identity map is a _unit element_ for whiskerings from the function side, and
the reflexivity homotopy is an _absorbing element_ on the homotopy side for
whiskerings.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  left-unit-law-left-whisker-comp :
    {f f' : (x : A) → B x} (H : f ~ f') → id ·l H ~ H
  left-unit-law-left-whisker-comp H x = ap-id (H x)

  inv-left-unit-law-left-whisker-comp :
    {f f' : (x : A) → B x} (H : f ~ f') → H ~ id ·l H
  inv-left-unit-law-left-whisker-comp H =
    inv-htpy (left-unit-law-left-whisker-comp H)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  right-absorption-law-left-whisker-comp :
    {f : (x : A) → B x} (g : {x : A} → B x → C x) →
    g ·l refl-htpy {f = f} ~ refl-htpy
  right-absorption-law-left-whisker-comp g = refl-htpy

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  where

  left-absorption-law-right-whisker-comp :
    {g : {x : A} (y : B x) → C x y} (f : (x : A) → B x) →
    refl-htpy {f = g} ·r f ~ refl-htpy
  left-absorption-law-right-whisker-comp f = refl-htpy

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  right-unit-law-right-whisker-comp :
    {f f' : (x : A) → B x} (H : f ~ f') → H ·r id ~ H
  right-unit-law-right-whisker-comp H = refl-htpy
```

### Laws for whiskering an inverted homotopy

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f f' : (x : A) → B x} (g : {x : A} → B x → C x) (H : f ~ f')
  where

  left-whisker-inv-htpy : g ·l (inv-htpy H) ~ inv-htpy (g ·l H)
  left-whisker-inv-htpy x = ap-inv g (H x)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  {g g' : {x : A} (y : B x) → C x y} (H : {x : A} → g {x} ~ g' {x})
  (f : (x : A) → B x)
  where

  right-whisker-inv-htpy : inv-htpy H ·r f ~ inv-htpy (H ·r f)
  right-whisker-inv-htpy = refl-htpy
```

### Inverse laws for whiskered homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f f' : (x : A) → B x} (g : {x : A} → B x → C x) (H : f ~ f')
  where

  left-inv-htpy-left-whisker : g ·l (inv-htpy H) ∙h g ·l H ~ refl-htpy
  left-inv-htpy-left-whisker =
    ( ap-concat-htpy' (g ·l H) (left-whisker-inv-htpy g H)) ∙h
    ( left-inv-htpy (g ·l H))

  right-inv-htpy-left-whisker : g ·l H ∙h g ·l (inv-htpy H) ~ refl-htpy
  right-inv-htpy-left-whisker =
    ( ap-concat-htpy (g ·l H) (left-whisker-inv-htpy g H)) ∙h
    ( right-inv-htpy (g ·l H))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  {g g' : {x : A} (y : B x) → C x y} (H : {x : A} → g {x} ~ g' {x})
  (f : (x : A) → B x)
  where

  left-inv-htpy-right-whisker : (inv-htpy H) ·r f ∙h H ·r f ~ refl-htpy
  left-inv-htpy-right-whisker = left-inv-htpy (H ·r f)

  right-inv-htpy-right-whisker : H ·r f ∙h (inv-htpy H) ·r f ~ refl-htpy
  right-inv-htpy-right-whisker = right-inv-htpy (H ·r f)
```

### Distributivity of whiskering over concatenation of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  distributive-left-whisker-comp-concat :
    { f g h : (x : A) → B x} (k : {x : A} → B x → C x) →
    ( H : f ~ g) (K : g ~ h) →
    k ·l (H ∙h K) ~ (k ·l H) ∙h (k ·l K)
  distributive-left-whisker-comp-concat k H K a =
    ap-concat k (H a) (K a)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  (k : (x : A) → B x) {f g h : {x : A} (y : B x) → C x y}
  (H : {x : A} → f {x} ~ g {x}) (K : {x : A} → g {x} ~ h {x})
  where

  distributive-right-whisker-comp-concat :
    (H ∙h K) ·r k ~ (H ·r k) ∙h (K ·r k)
  distributive-right-whisker-comp-concat = refl-htpy
```

### Whiskering preserves function composition

In other words, whiskering is an action of functions on homotopies.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : A → UU l2} {C : A → UU l3} {D : A → UU l4}
  where

  inv-preserves-comp-left-whisker-comp :
    ( k : {x : A} → C x → D x) (h : {x : A} → B x → C x) {f g : (x : A) → B x}
    ( H : f ~ g) →
    (k ∘ h) ·l H ~ k ·l (h ·l H)
  inv-preserves-comp-left-whisker-comp k h H x = ap-comp k h (H x)

  preserves-comp-left-whisker-comp :
    ( k : {x : A} → C x → D x) (h : {x : A} → B x → C x) {f g : (x : A) → B x}
    ( H : f ~ g) →
    k ·l (h ·l H) ~ (k ∘ h) ·l H
  preserves-comp-left-whisker-comp k h H =
    inv-htpy (inv-preserves-comp-left-whisker-comp k h H)

module _
  { l1 l2 l3 l4 : Level}
  { A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  { D : (x : A) (y : B x) (z : C x y) → UU l4}
  { f g : {x : A} {y : B x} (z : C x y) → D x y z}
  ( h : {x : A} (y : B x) → C x y) (k : (x : A) → B x)
  ( H : {x : A} {y : B x} → f {x} {y} ~ g {x} {y})
  where

  preserves-comp-right-whisker-comp : (H ·r h) ·r k ~ H ·r (h ∘ k)
  preserves-comp-right-whisker-comp = refl-htpy
```

### A coherence for homotopies to the identity function

Consider a function `f : A → A` and let `H : f ~ id` be a homotopy to the
identity function. Then we have a homotopy

```text
  H ·r f ~ f ·l H.
```

```agda
module _
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  where

  coh-htpy-id : H ·r f ~ f ·l H
  coh-htpy-id x = is-injective-concat' (H x) (nat-htpy-id H (H x))

  inv-coh-htpy-id : f ·l H ~ H ·r f
  inv-coh-htpy-id = inv-htpy coh-htpy-id
```

## See also

- For interactions between whiskering and exponentiation, see
  [`foundation.composition-algebra`](foundation.composition-algebra.md).
