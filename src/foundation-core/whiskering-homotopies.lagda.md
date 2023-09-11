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

### Whiskering of homotopies

```agda
htpy-left-whisk :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (h : B → C) {f g : A → B} → f ~ g → (h ∘ f) ~ (h ∘ g)
htpy-left-whisk h H x = ap h (H x)

infixr 15 _·l_
_·l_ = htpy-left-whisk

htpy-right-whisk :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3}
  {g h : (y : B) → C y} (H : g ~ h) (f : A → B) → (g ∘ f) ~ (h ∘ f)
htpy-right-whisk H f x = H (f x)

infixl 15 _·r_
_·r_ = htpy-right-whisk
```

### Horizontal composition of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f f' : A → B} {g g' : B → C}
  where

  htpy-comp-horizontal : (f ~ f') → (g ~ g') → (g ∘ f) ~ (g' ∘ f')
  htpy-comp-horizontal F G = (g ·l F) ∙h (G ·r f')

  htpy-comp-horizontal' : (f ~ f') → (g ~ g') → (g ∘ f) ~ (g' ∘ f')
  htpy-comp-horizontal' F G = (G ·r f) ∙h (g' ·l F)
```

## Properties

### Laws for whiskering an inverted homotopy

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  left-whisk-inv-htpy :
    {f f' : A → B} (g : B → C) (H : f ~ f') →
    (g ·l (inv-htpy H)) ~ inv-htpy (g ·l H)
  left-whisk-inv-htpy g H x = ap-inv g (H x)

  inv-htpy-left-whisk-inv-htpy :
    {f f' : A → B} (g : B → C) (H : f ~ f') →
    inv-htpy (g ·l H) ~ (g ·l (inv-htpy H))
  inv-htpy-left-whisk-inv-htpy g H =
    inv-htpy (left-whisk-inv-htpy g H)

  right-whisk-inv-htpy :
    {g g' : B → C} (H : g ~ g') (f : A → B) →
    ((inv-htpy H) ·r f) ~ (inv-htpy (H ·r f))
  right-whisk-inv-htpy H f = refl-htpy

  inv-htpy-right-whisk-inv-htpy :
    {g g' : B → C} (H : g ~ g') (f : A → B) →
    ((inv-htpy H) ·r f) ~ (inv-htpy (H ·r f))
  inv-htpy-right-whisk-inv-htpy H f =
    inv-htpy (right-whisk-inv-htpy H f)
```

### Distributivity of whiskering over composition of homotopies

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  distributive-left-whisk-concat-htpy :
    { f g h : A → B} (k : B → C) →
    ( H : f ~ g) (K : g ~ h) →
    ( k ·l (H ∙h K)) ~ ((k ·l H) ∙h (k ·l K))
  distributive-left-whisk-concat-htpy k H K a =
    ap-concat k (H a) (K a)

  distributive-right-whisk-concat-htpy :
    ( k : A → B) {f g h : B → C} →
    ( H : f ~ g) (K : g ~ h) →
    ( (H ∙h K) ·r k) ~ ((H ·r k) ∙h (K ·r k))
  distributive-right-whisk-concat-htpy k H K = refl-htpy
```

### Associativity of whiskering and function composition

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  associative-left-whisk-comp :
    ( k : C → D) (h : B → C) {f g : A → B} →
    ( H : f ~ g) →
    ( k ·l (h ·l H)) ~ ((k ∘ h) ·l H)
  associative-left-whisk-comp k h H x = inv (ap-comp k h (H x))

  associative-right-whisk-comp :
    { f g : C → D} (h : B → C) (k : A → B) →
    ( H : f ~ g) →
    ( (H ·r h) ·r k) ~ (H ·r (h ∘ k))
  associative-right-whisk-comp h k H = refl-htpy
```

### A coherence for homotopies to the identity function

```agda
module _
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  where

  coh-htpy-id : (H ·r f) ~ (f ·l H)
  coh-htpy-id x = is-injective-concat' (H x) (nat-htpy-id H (H x))

  inv-htpy-coh-htpy-id : (f ·l H) ~ (H ·r f)
  inv-htpy-coh-htpy-id = inv-htpy coh-htpy-id
```
