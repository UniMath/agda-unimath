# Extensions of families of elements

```agda
module foundation.extensions-families-of-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.lifts-families-of-elements
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Consider a family of elements `a : I → A`, a type family `B` over `A` and a
[lift](foundation.lifts-families-of-elements.md)

```text
  b : (i : I) → B (a i)
```

of the family of elements `a`. An
{{#concept "extension" Disambiguation="family of elements"}} of `b` to `A`
consists of a family of elements `f : (x : A) → B x` equipped with a
[homotopy](foundation-core.homotopies.md) `f ∘ a ~ b`.

More generally, given a family of elements `a : (i : I) → A i`, a type family
`B` over `A`, and a dependent lift

```text
  b : (i : I) → B i (a i)
```

of the family of elements `A`, a
{{#concet "dependent extension" Disambiguation"family of elements"}} of `b` to
`A` consists of a family of elements

```text
  f : (i : I) (x : A i) → B i x
```

equipped with a homotopy `(i : I) → f i (a i) ＝ b i`.

## Definitions

### Evaluating families of elements at lifts of families of elements

Any family of elements `a : (i : I) → A i` induces an evaluation map

```text
  ((i : I) (x : A i) → B i x) → ((i : I) → B i (a i))
```

defined by `b ↦ (λ i → b i (a i))`.

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (a : (i : I) → A i)
  {B : (i : I) → A i → UU l3}
  where

  ev-dependent-lift-family-of-elements :
    ((i : I) (x : A i) → B i x) → dependent-lift-family-of-elements a B
  ev-dependent-lift-family-of-elements b i = b i (a i)

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} (a : I → A) {B : A → UU l3}
  where

  ev-lift-family-of-elements :
    ((x : A) → B x) → lift-family-of-elements a B
  ev-lift-family-of-elements b i = b (a i)
```

### Evaluating families of elements at double lifts of families of elements

Any family of elements `b : (i : I) → B i (a i)` dependent over a family of
elements `a : (i : I) → A i` induces an evaluation map

```text
  ((i : I) (x : A i) (y : B i x) → C i x y) → ((i : I) → C i (a i) (b i))
```

given by `c ↦ (λ i → c i (a i) (b i))`.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {a : (i : I) → A i}
  {B : (i : I) → A i → UU l3} (b : dependent-lift-family-of-elements a B)
  {C : (i : I) (x : A i) → B i x → UU l4}
  where

  ev-dependent-double-lift-family-of-elements :
    ((i : I) (x : A i) (y : B i x) → C i x y) →
    dependent-double-lift-family-of-elements b C
  ev-dependent-double-lift-family-of-elements h i = h i (a i) (b i)

module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} {a : I → A}
  {B : A → UU l3} (b : lift-family-of-elements a B)
  {C : (x : A) → B x → UU l4}
  where

  ev-double-lift-family-of-elements :
    ((x : A) (y : B x) → C x y) → double-lift-family-of-elements b C
  ev-double-lift-family-of-elements h i = h (a i) (b i)
```

### Dependent extensions of dependent lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (a : (i : I) → A i)
  (B : (i : I) → A i → UU l3) (b : dependent-lift-family-of-elements a B)
  where

  is-extension-dependent-lift-family-of-elements :
    (f : (i : I) (x : A i) → B i x) → UU (l1 ⊔ l3)
  is-extension-dependent-lift-family-of-elements f =
    ev-dependent-lift-family-of-elements a f ~ b

  extension-dependent-lift-family-of-elements : UU (l1 ⊔ l2 ⊔ l3)
  extension-dependent-lift-family-of-elements =
    Σ ((i : I) (x : A i) → B i x) is-extension-dependent-lift-family-of-elements

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {a : (i : I) → A i}
  {B : (i : I) → A i → UU l3} {b : dependent-lift-family-of-elements a B}
  (f : extension-dependent-lift-family-of-elements a B b)
  where

  family-of-elements-extension-dependent-lift-family-of-elements :
    (i : I) (x : A i) → B i x
  family-of-elements-extension-dependent-lift-family-of-elements = pr1 f

  is-extension-extension-dependent-lift-family-of-elements :
    is-extension-dependent-lift-family-of-elements a B b
      ( family-of-elements-extension-dependent-lift-family-of-elements)
  is-extension-extension-dependent-lift-family-of-elements = pr2 f
```

### Extensions of lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} (a : I → A)
  (B : A → UU l3) (b : lift-family-of-elements a B)
  where

  is-extension-lift-family-of-elements : (f : (x : A) → B x) → UU (l1 ⊔ l3)
  is-extension-lift-family-of-elements f = ev-lift-family-of-elements a f ~ b

  extension-lift-family-of-elements : UU (l1 ⊔ l2 ⊔ l3)
  extension-lift-family-of-elements =
    Σ ((x : A) → B x) is-extension-lift-family-of-elements

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} {a : I → A}
  {B : A → UU l3} {b : lift-family-of-elements a B}
  (f : extension-lift-family-of-elements a B b)
  where

  family-of-elements-extension-lift-family-of-elements : (x : A) → B x
  family-of-elements-extension-lift-family-of-elements = pr1 f

  is-extension-extension-lift-family-of-elements :
    is-extension-lift-family-of-elements a B b
      ( family-of-elements-extension-lift-family-of-elements)
  is-extension-extension-lift-family-of-elements = pr2 f
```

### Dependent extensions of double lifts of families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {a : (i : I) → A i}
  {B : (i : I) → A i → UU l3} (b : dependent-lift-family-of-elements a B)
  (C : (i : I) (x : A i) (y : B i x) → UU l4)
  (c : dependent-double-lift-family-of-elements b C)
  where

  is-extension-dependent-double-lift-family-of-elements :
    (f : (i : I) (x : A i) (y : B i x) → C i x y) → UU (l1 ⊔ l4)
  is-extension-dependent-double-lift-family-of-elements f =
    ev-dependent-double-lift-family-of-elements b f ~ c

  extension-dependent-double-lift-family-of-elements : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  extension-dependent-double-lift-family-of-elements =
    Σ ( (i : I) (x : A i) (y : B i x) → C i x y)
      ( is-extension-dependent-double-lift-family-of-elements)

module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {a : (i : I) → A i}
  {B : (i : I) → A i → UU l3} {b : dependent-lift-family-of-elements a B}
  {C : (i : I) (x : A i) (y : B i x) → UU l4}
  {c : dependent-double-lift-family-of-elements b C}
  (f : extension-dependent-double-lift-family-of-elements b C c)
  where

  family-of-elements-extension-dependent-double-lift-family-of-elements :
    (i : I) (x : A i) (y : B i x) → C i x y
  family-of-elements-extension-dependent-double-lift-family-of-elements =
    pr1 f

  is-extension-extension-dependent-double-lift-family-of-elements :
    is-extension-dependent-double-lift-family-of-elements b C c
      ( family-of-elements-extension-dependent-double-lift-family-of-elements)
  is-extension-extension-dependent-double-lift-family-of-elements = pr2 f
```

### Extensions of double lifts of families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} {a : I → A}
  {B : A → UU l3} (b : lift-family-of-elements a B)
  (C : (x : A) (y : B x) → UU l4) (c : double-lift-family-of-elements b C)
  where

  is-extension-double-lift-family-of-elements :
    (f : (x : A) (y : B x) → C x y) → UU (l1 ⊔ l4)
  is-extension-double-lift-family-of-elements f =
    ev-double-lift-family-of-elements b f ~ c

  extension-double-lift-family-of-elements : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  extension-double-lift-family-of-elements =
    Σ ((x : A) (y : B x) → C x y) is-extension-double-lift-family-of-elements

module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} {a : I → A}
  {B : A → UU l3} {b : lift-family-of-elements a B}
  {C : (x : A) (y : B x) → UU l4} {c : double-lift-family-of-elements b C}
  (f : extension-double-lift-family-of-elements b C c)
  where

  family-of-elements-extension-double-lift-family-of-elements :
    (x : A) (y : B x) → C x y
  family-of-elements-extension-double-lift-family-of-elements = pr1 f

  is-extension-extension-double-lift-family-of-elements :
    is-extension-double-lift-family-of-elements b C c
      ( family-of-elements-extension-double-lift-family-of-elements)
  is-extension-extension-double-lift-family-of-elements = pr2 f
```

### Identity extensions of dependent lifts of families of elements

```agda
module _
  {l1 l2 : Level} {I : UU l1} {A : I → UU l2} (a : (i : I) → A i)
  where

  id-extension-dependent-lift-family-of-elements :
    extension-dependent-lift-family-of-elements a (λ i _ → A i) a
  pr1 id-extension-dependent-lift-family-of-elements i = id
  pr2 id-extension-dependent-lift-family-of-elements = refl-htpy
```

### Identity extensions of lifts of families of elements

```agda
module _
  {l1 l2 : Level} {I : UU l1} {A : UU l2} (a : I → A)
  where

  id-extension-lift-family-of-elements :
    extension-lift-family-of-elements a (λ _ → A) a
  pr1 id-extension-lift-family-of-elements = id
  pr2 id-extension-lift-family-of-elements = refl-htpy
```

### Identity extensions of dependent double lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {a : (i : I) → A i}
  {B : (i : I) → A i → UU l3} (b : dependent-lift-family-of-elements a B)
  where

  id-extension-dependent-double-lift-family-of-elements :
    extension-dependent-double-lift-family-of-elements b (λ i x y → B i x) b
  pr1 id-extension-dependent-double-lift-family-of-elements i x = id
  pr2 id-extension-dependent-double-lift-family-of-elements = refl-htpy
```

### Identity extensions of double lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} {a : I → A}
  {B : A → UU l3} (b : lift-family-of-elements a B)
  where

  id-extension-double-lift-family-of-elements :
    extension-double-lift-family-of-elements b (λ x (y : B x) → B x) b
  pr1 id-extension-double-lift-family-of-elements x = id
  pr2 id-extension-double-lift-family-of-elements = refl-htpy
```

### Composition of extensions of dependent lifts of families of elements

Consider three type families `A`, `B`, and `C` over a type `I` equipped with
sections

```text
  a : (i : I) → A i
  b : (i : I) → B i
  c : (i : I) → C i.
```

Furthermore, suppose that `g` is an extension of `c` along `b`, and suppose that
`f` is an extension of `b` along `a`. In other words, `g` consists of a family
of maps

```text
  g : (i : I) → B i → C i
```

equipped with a homotopy witnessing that `g i (b i) ＝ c i` for all `i : I`, and
`f` consists of a family of maps

```text
  f : (i : I) → A i → B i
```

equipped with a homotopy witnessing that `f i (a i) ＝ b i` for all `i : I`.
Then we can compose `g` and `f` fiberwise, resulting in a family of maps

```text
  λ i → g i ∘ f i : (i : I) → A i → C i
```

equipped with a homotopy witnessing that `g i (f i (a i)) ＝ c i` for all
`i : I`. In other words, extensions of `c` along `b` can be composed with
extensions of `b` along `a` to obtain extensions of `c` along `a`.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {a : (i : I) → A i}
  {B : I → UU l3} {b : (i : I) → B i}
  {C : I → UU l4} {c : (i : I) → C i}
  (g : extension-dependent-lift-family-of-elements b (λ i _ → C i) c)
  (f : extension-dependent-lift-family-of-elements a (λ i _ → B i) b)
  where

  family-of-elements-comp-extension-dependent-lift-family-of-elements :
    (i : I) → A i → C i
  family-of-elements-comp-extension-dependent-lift-family-of-elements i =
    family-of-elements-extension-dependent-lift-family-of-elements g i ∘
    family-of-elements-extension-dependent-lift-family-of-elements f i

  is-extension-comp-extension-dependent-lift-family-of-elements :
    is-extension-dependent-lift-family-of-elements a
      ( λ i _ → C i)
      ( c)
      ( family-of-elements-comp-extension-dependent-lift-family-of-elements)
  is-extension-comp-extension-dependent-lift-family-of-elements i =
    ( ap
      ( family-of-elements-extension-dependent-lift-family-of-elements g i)
      ( is-extension-extension-dependent-lift-family-of-elements f i)) ∙
    ( is-extension-extension-dependent-lift-family-of-elements g i)

  comp-extension-dependent-lift-family-of-elements :
    extension-dependent-lift-family-of-elements a (λ i _ → C i) c
  pr1 comp-extension-dependent-lift-family-of-elements =
    family-of-elements-comp-extension-dependent-lift-family-of-elements
  pr2 comp-extension-dependent-lift-family-of-elements =
    is-extension-comp-extension-dependent-lift-family-of-elements
```

### Composition of extensions of lifts of families of elements

Consider three types `A`, `B`, and `C` equipped with maps

```text
  a : I → A
  b : I → B
  c : I → C.
```

Furthermore, suppose that `g` is an extension of `c` along `b`, and suppose that
`f` is an extension of `b` along `a`. In other words, we assume a commuting
diagram

```text
        I
      / | \
    a/  |  \c
    /   |b  \
   V    V    V
  A --> B --> C
     f     g
```

The composite `g ∘ f` is then an extension of `c` along `a.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : UU l2} {a : I → A}
  {B : UU l3} {b : I → B}
  {C : UU l4} {c : I → C}
  (g : extension-lift-family-of-elements b (λ _ → C) c)
  (f : extension-lift-family-of-elements a (λ _ → B) b)
  where

  map-comp-extension-lift-family-of-elements : A → C
  map-comp-extension-lift-family-of-elements =
    family-of-elements-extension-lift-family-of-elements g ∘
    family-of-elements-extension-lift-family-of-elements f

  is-extension-comp-extension-lift-family-of-elements :
    is-extension-lift-family-of-elements a
      ( λ _ → C)
      ( c)
      ( map-comp-extension-lift-family-of-elements)
  is-extension-comp-extension-lift-family-of-elements x =
    ( ap
      ( family-of-elements-extension-lift-family-of-elements g)
      ( is-extension-extension-lift-family-of-elements f x)) ∙
    ( is-extension-extension-lift-family-of-elements g x)

  comp-extension-lift-family-of-elements :
    extension-lift-family-of-elements a (λ _ → C) c
  pr1 comp-extension-lift-family-of-elements =
    map-comp-extension-lift-family-of-elements
  pr2 comp-extension-lift-family-of-elements =
    is-extension-comp-extension-lift-family-of-elements
```

### Composition of extensions of dependent double lifts of families of elements

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {a : (i : I) → A i}
  {B : (i : I) → A i → UU l3} {b : dependent-lift-family-of-elements a B}
  {C : (i : I) → A i → UU l4} {c : dependent-lift-family-of-elements a C}
  {D : (i : I) → A i → UU l5} {d : dependent-lift-family-of-elements a D}
  (g :
    extension-dependent-double-lift-family-of-elements c
      ( λ i x (_ : C i x) → D i x)
      ( d))
  (f :
    extension-dependent-double-lift-family-of-elements b
      ( λ i x (_ : B i x) → C i x)
      ( c))
  where

  family-of-elements-comp-extension-dependent-double-lift-family-of-elements :
    (i : I) (x : A i) → B i x → D i x
  family-of-elements-comp-extension-dependent-double-lift-family-of-elements
    i x =
    family-of-elements-extension-dependent-double-lift-family-of-elements
      g i x ∘
    family-of-elements-extension-dependent-double-lift-family-of-elements
      f i x

  is-extension-comp-extension-dependent-double-lift-family-of-elements :
    is-extension-dependent-double-lift-family-of-elements b
      ( λ i x _ → D i x)
      ( d)
      ( family-of-elements-comp-extension-dependent-double-lift-family-of-elements)
  is-extension-comp-extension-dependent-double-lift-family-of-elements i =
    ( ap
      ( family-of-elements-extension-dependent-double-lift-family-of-elements
        g i (a i))
      ( is-extension-extension-dependent-double-lift-family-of-elements f i)) ∙
    ( is-extension-extension-dependent-double-lift-family-of-elements g i)

  comp-extension-dependent-double-lift-family-of-elements :
    extension-dependent-double-lift-family-of-elements b
      ( λ i x (_ : B i x) → D i x)
      ( d)
  pr1 comp-extension-dependent-double-lift-family-of-elements =
    family-of-elements-comp-extension-dependent-double-lift-family-of-elements
  pr2 comp-extension-dependent-double-lift-family-of-elements =
    is-extension-comp-extension-dependent-double-lift-family-of-elements
```

### Composition of extensions of double lifts of families of elements

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1} {A : UU l2} {a : I → A}
  {B : A → UU l3} {b : lift-family-of-elements a B}
  {C : A → UU l4} {c : lift-family-of-elements a C}
  {D : A → UU l5} {d : lift-family-of-elements a D}
  (g : extension-double-lift-family-of-elements c (λ x (_ : C x) → D x) d)
  (f : extension-double-lift-family-of-elements b (λ x (_ : B x) → C x) c)
  where

  family-of-elements-comp-extension-double-lift-family-of-elements :
    (x : A) → B x → D x
  family-of-elements-comp-extension-double-lift-family-of-elements x =
    family-of-elements-extension-double-lift-family-of-elements g x ∘
    family-of-elements-extension-double-lift-family-of-elements f x

  is-extension-comp-extension-double-lift-family-of-elements :
    is-extension-double-lift-family-of-elements b
      ( λ x _ → D x)
      ( d)
      ( family-of-elements-comp-extension-double-lift-family-of-elements)
  is-extension-comp-extension-double-lift-family-of-elements i =
    ( ap
      ( family-of-elements-extension-double-lift-family-of-elements g (a i))
      ( is-extension-extension-double-lift-family-of-elements f i)) ∙
    ( is-extension-extension-double-lift-family-of-elements g i)

  comp-extension-double-lift-family-of-elements :
    extension-double-lift-family-of-elements b (λ x (_ : B x) → D x) d
  pr1 comp-extension-double-lift-family-of-elements =
    family-of-elements-comp-extension-double-lift-family-of-elements
  pr2 comp-extension-double-lift-family-of-elements =
    is-extension-comp-extension-double-lift-family-of-elements
```
