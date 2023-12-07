# Whiskering homotopies

```agda
module foundation-core.whiskering-homotopies where
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

## Definitions

### Left whiskering of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  htpy-left-whisk :
    (h : {x : A} → B x → C x)
    {f g : (x : A) → B x} → f ~ g → h ∘ f ~ h ∘ g
  htpy-left-whisk h H x = ap h (H x)

  infixr 17 _·l_
  _·l_ = htpy-left-whisk
```

### Right whiskering of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  where

  htpy-right-whisk :
    {g h : {x : A} (y : B x) → C x y}
    (H : {x : A} → g {x} ~ h {x})
    (f : (x : A) → B x) → g ∘ f ~ h ∘ f
  htpy-right-whisk H f x = H (f x)

  infixl 16 _·r_
  _·r_ = htpy-right-whisk
```

### Horizontal composition of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f f' : (x : A) → B x} {g g' : {x : A} → B x → C x}
  where

  htpy-comp-horizontal : f ~ f' → ({x : A} → g {x} ~ g' {x}) → g ∘ f ~ g' ∘ f'
  htpy-comp-horizontal F G = (g ·l F) ∙h (G ·r f')

  htpy-comp-horizontal' : f ~ f' → ({x : A} → g {x} ~ g' {x}) → g ∘ f ~ g' ∘ f'
  htpy-comp-horizontal' F G = (G ·r f) ∙h (g' ·l F)
```

## Properties

### Unit laws for whiskering homotopies

The identity map is the identity element for whiskerings from the function side,
and the reflexivity homotopy is the identity element for whiskerings from the
homotopy side.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  left-unit-law-left-whisk-htpy :
    {f f' : (x : A) → B x} → (H : f ~ f') → id ·l H ~ H
  left-unit-law-left-whisk-htpy H x = ap-id (H x)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  right-unit-law-left-whisk-htpy :
    {f : (x : A) → B x} (g : {x : A} → B x → C x) →
    g ·l refl-htpy {f = f} ~ refl-htpy
  right-unit-law-left-whisk-htpy g = refl-htpy

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  where

  left-unit-law-right-whisk-htpy :
    {g : {x : A} (y : B x) → C x y} (f : (x : A) → B x) →
    refl-htpy {f = g} ·r f ~ refl-htpy
  left-unit-law-right-whisk-htpy f = refl-htpy

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  right-unit-law-right-whisk-htpy :
    {f f' : (x : A) → B x} → (H : f ~ f') → H ·r id ~ H
  right-unit-law-right-whisk-htpy H = refl-htpy
```

### Laws for whiskering an inverted homotopy

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f f' : (x : A) → B x} (g : {x : A} → B x → C x) (H : f ~ f')
  where

  left-whisk-inv-htpy : g ·l (inv-htpy H) ~ inv-htpy (g ·l H)
  left-whisk-inv-htpy x = ap-inv g (H x)

  inv-htpy-left-whisk-inv-htpy : inv-htpy (g ·l H) ~ g ·l (inv-htpy H)
  inv-htpy-left-whisk-inv-htpy = inv-htpy left-whisk-inv-htpy

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  {g g' : {x : A} (y : B x) → C x y} (H : {x : A} → g {x} ~ g' {x})
  (f : (x : A) → B x)
  where

  right-whisk-inv-htpy : inv-htpy H ·r f ~ inv-htpy (H ·r f)
  right-whisk-inv-htpy = refl-htpy

  inv-htpy-right-whisk-inv-htpy : inv-htpy H ·r f ~ inv-htpy (H ·r f)
  inv-htpy-right-whisk-inv-htpy = inv-htpy right-whisk-inv-htpy
```

### Distributivity of whiskering over composition of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  distributive-left-whisk-concat-htpy :
    { f g h : (x : A) → B x} (k : {x : A} → B x → C x) →
    ( H : f ~ g) (K : g ~ h) →
    k ·l (H ∙h K) ~ (k ·l H) ∙h (k ·l K)
  distributive-left-whisk-concat-htpy k H K a =
    ap-concat k (H a) (K a)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  (k : (x : A) → B x) {f g h : {x : A} (y : B x) → C x y}
  (H : {x : A} → f {x} ~ g {x}) (K : {x : A} → g {x} ~ h {x})
  where

  distributive-right-whisk-concat-htpy :
    (H ∙h K) ·r k ~ (H ·r k) ∙h (K ·r k)
  distributive-right-whisk-concat-htpy = refl-htpy
```

### Associativity of whiskering and function composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : A → UU l2} {C : A → UU l3} {D : A → UU l4}
  where

  associative-left-whisk-comp :
    ( k : {x : A} → C x → D x) (h : {x : A} → B x → C x) {f g : (x : A) → B x}
    ( H : f ~ g) →
    k ·l (h ·l H) ~ (k ∘ h) ·l H
  associative-left-whisk-comp k h H x = inv (ap-comp k h (H x))

module _
  { l1 l2 l3 l4 : Level}
  { A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  { D : (x : A) (y : B x) (z : C x y) → UU l4}
  { f g : {x : A} {y : B x} (z : C x y) → D x y z}
  ( h : {x : A} (y : B x) → C x y) (k : (x : A) → B x)
  ( H : {x : A} {y : B x} → f {x} {y} ~ g {x} {y})
  where

  associative-right-whisk-comp : (H ·r h) ·r k ~ H ·r (h ∘ k)
  associative-right-whisk-comp = refl-htpy
```

### A coherence for homotopies to the identity function

```agda
module _
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  where

  coh-htpy-id : H ·r f ~ f ·l H
  coh-htpy-id x = is-injective-concat' (H x) (nat-htpy-id H (H x))

  inv-htpy-coh-htpy-id : f ·l H ~ H ·r f
  inv-htpy-coh-htpy-id = inv-htpy coh-htpy-id
```

### Whiskering whiskerings

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f g : (x : A) → B x}
  where

  ap-left-whisk-htpy :
    (h : {x : A} → B x → C x) {H H' : f ~ g} (α : H ~ H') → h ·l H ~ h ·l H'
  ap-left-whisk-htpy h α x = ap (ap h) (α x)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  {f g : {x : A} (y : B x) → C x y} {H H' : {x : A} → f {x} ~ g {x}}
  where

  ap-right-whisk-htpy :
    (α : {x : A} → H {x} ~ H' {x}) (h : (x : A) → B x) → H ·r h ~ H' ·r h
  ap-right-whisk-htpy α h = α ·r h
```

### Left and right whiskering commute definitionally

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : A → UU l2}
  {C : {x : A} → B x → UU l3} {D : {x : A} → B x → UU l4}
  {f g : {x : A} (y : B x) → C y}
  where

  coherence-left-right-whisk-htpy :
    (h : {x : A} {y : B x} → C y → D y)
    (H : {x : A} → f {x} ~ g {x})
    (h' : (x : A) → B x) →
    h ·l (H ·r h') ~ (h ·l H) ·r h'
  coherence-left-right-whisk-htpy h H h' = refl-htpy
```
