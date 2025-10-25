# Extensions of double lifts of families of elements

```agda
module
  orthogonal-factorization-systems.extensions-double-lifts-families-of-elements
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types

open import orthogonal-factorization-systems.double-lifts-families-of-elements
open import orthogonal-factorization-systems.lifts-families-of-elements
```

</details>

## Idea

Consider a
[dependent lift](orthogonal-factorization-systems.lifts-families-of-elements.md)
`b : (i : I) → B i (a i)` of a family of elements `a : I → A`, a type family `C`
over `B` and a
[double lift](orthogonal-factorization-systems.double-lifts-families-of-elements.md)

```text
  c : (i : I) → C i (a i) (b i)
```

of the lift `b` of `a`. An
{{#concept "extension" Disambiguation="dependent double family of elements" Agda=extension-dependent-double-lift-family-of-elements}}
of `b` to `A` consists of a family of elements
`f : (i : I) (x : A i) (y : B i x) → C i x y` equipped with a
[homotopy](foundation-core.homotopies.md) witnessing that the
[identification](foundation-core.identity-types.md) `f i (a i) (b i) ＝ c i`
holds for every `i : I`.

Extensions of dependent double lifts play a role in the
[universal property of the family of fibers of a map](foundation.universal-property-family-of-fibers-of-maps.md)

## Definitions

### Evaluating families of elements at dependent double lifts of families of elements

Any family of elements `b : (i : I) → B i (a i)` dependent over a family of
elements `a : (i : I) → A i` induces an evaluation map

```text
  ((i : I) (x : A i) (y : B i x) → C i x y) → ((i : I) → C i (a i) (b i))
```

given by `c ↦ (λ i → c i (a i) (b i))`.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : (i : I) → A i → UU l3}
  {C : (i : I) (x : A i) → B i x → UU l4}
  {a : (i : I) → A i} (b : dependent-lift-family-of-elements B a)
  where

  ev-dependent-double-lift-family-of-elements :
    ((i : I) (x : A i) (y : B i x) → C i x y) →
    dependent-double-lift-family-of-elements C b
  ev-dependent-double-lift-family-of-elements h i = h i (a i) (b i)
```

### Evaluating families of elements at double lifts of families of elements

Any family of elements `b : (i : I) → B (a i)` dependent over a family of
elements `a : I → A` induces an evaluation map

```text
  ((x : A) (y : B x) → C x y) → ((i : I) → C (a i) (b i))
```

given by `c ↦ (λ i → c (a i) (b i))`.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} {B : A → UU l3}
  {C : (x : A) → B x → UU l4}
  {a : I → A} (b : lift-family-of-elements B a)
  where

  ev-double-lift-family-of-elements :
    ((x : A) (y : B x) → C x y) → double-lift-family-of-elements C b
  ev-double-lift-family-of-elements h i = h (a i) (b i)
```

### Dependent extensions of double lifts of families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : (i : I) → A i → UU l3}
  (C : (i : I) (x : A i) (y : B i x) → UU l4)
  {a : (i : I) → A i} (b : dependent-lift-family-of-elements B a)
  (c : dependent-double-lift-family-of-elements C b)
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
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : (i : I) → A i → UU l3}
  {C : (i : I) (x : A i) (y : B i x) → UU l4}
  {a : (i : I) → A i} {b : dependent-lift-family-of-elements B a}
  {c : dependent-double-lift-family-of-elements C b}
  (f : extension-dependent-double-lift-family-of-elements C b c)
  where

  family-of-elements-extension-dependent-double-lift-family-of-elements :
    (i : I) (x : A i) (y : B i x) → C i x y
  family-of-elements-extension-dependent-double-lift-family-of-elements =
    pr1 f

  is-extension-extension-dependent-double-lift-family-of-elements :
    is-extension-dependent-double-lift-family-of-elements C b c
      ( family-of-elements-extension-dependent-double-lift-family-of-elements)
  is-extension-extension-dependent-double-lift-family-of-elements = pr2 f
```

### Extensions of double lifts of families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} {B : A → UU l3}
  (C : (x : A) (y : B x) → UU l4)
  {a : I → A} (b : lift-family-of-elements B a)
  (c : double-lift-family-of-elements C b)
  where

  is-extension-double-lift-family-of-elements :
    (f : (x : A) (y : B x) → C x y) → UU (l1 ⊔ l4)
  is-extension-double-lift-family-of-elements f =
    ev-double-lift-family-of-elements b f ~ c

  extension-double-lift-family-of-elements : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  extension-double-lift-family-of-elements =
    Σ ((x : A) (y : B x) → C x y) is-extension-double-lift-family-of-elements

module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} {B : A → UU l3}
  {C : (x : A) (y : B x) → UU l4}
  {a : I → A} {b : lift-family-of-elements B a}
  {c : double-lift-family-of-elements C b}
  (f : extension-double-lift-family-of-elements C b c)
  where

  family-of-elements-extension-double-lift-family-of-elements :
    (x : A) (y : B x) → C x y
  family-of-elements-extension-double-lift-family-of-elements = pr1 f

  is-extension-extension-double-lift-family-of-elements :
    is-extension-double-lift-family-of-elements C b c
      ( family-of-elements-extension-double-lift-family-of-elements)
  is-extension-extension-double-lift-family-of-elements = pr2 f
```

### Identity extensions of dependent double lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : (i : I) → A i → UU l3}
  {a : (i : I) → A i} (b : dependent-lift-family-of-elements B a)
  where

  id-extension-dependent-double-lift-family-of-elements :
    extension-dependent-double-lift-family-of-elements (λ i x y → B i x) b b
  pr1 id-extension-dependent-double-lift-family-of-elements i x = id
  pr2 id-extension-dependent-double-lift-family-of-elements = refl-htpy
```

### Identity extensions of double lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} {B : A → UU l3}
  {a : I → A} (b : lift-family-of-elements B a)
  where

  id-extension-double-lift-family-of-elements :
    extension-double-lift-family-of-elements (λ x (y : B x) → B x) b b
  pr1 id-extension-double-lift-family-of-elements x = id
  pr2 id-extension-double-lift-family-of-elements = refl-htpy
```

### Composition of extensions of dependent double lifts of families of elements

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : (i : I) → A i → UU l3} {C : (i : I) → A i → UU l4}
  {D : (i : I) → A i → UU l5}
  {a : (i : I) → A i}
  {b : dependent-lift-family-of-elements B a}
  {c : dependent-lift-family-of-elements C a}
  {d : dependent-lift-family-of-elements D a}
  (g :
    extension-dependent-double-lift-family-of-elements
      ( λ i x (_ : C i x) → D i x)
      ( c)
      ( d))
  (f :
    extension-dependent-double-lift-family-of-elements
      ( λ i x (_ : B i x) → C i x)
      ( b)
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
    is-extension-dependent-double-lift-family-of-elements
      ( λ i x _ → D i x)
      ( b)
      ( d)
      ( family-of-elements-comp-extension-dependent-double-lift-family-of-elements)
  is-extension-comp-extension-dependent-double-lift-family-of-elements i =
    ( ap
      ( family-of-elements-extension-dependent-double-lift-family-of-elements
        g i (a i))
      ( is-extension-extension-dependent-double-lift-family-of-elements f i)) ∙
    ( is-extension-extension-dependent-double-lift-family-of-elements g i)

  comp-extension-dependent-double-lift-family-of-elements :
    extension-dependent-double-lift-family-of-elements
      ( λ i x (_ : B i x) → D i x)
      ( b)
      ( d)
  pr1 comp-extension-dependent-double-lift-family-of-elements =
    family-of-elements-comp-extension-dependent-double-lift-family-of-elements
  pr2 comp-extension-dependent-double-lift-family-of-elements =
    is-extension-comp-extension-dependent-double-lift-family-of-elements
```

### Composition of extensions of double lifts of families of elements

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1} {A : UU l2} {B : A → UU l3}
  {C : A → UU l4} {D : A → UU l5}
  {a : I → A} {b : lift-family-of-elements B a}
  {c : lift-family-of-elements C a} {d : lift-family-of-elements D a}
  (g : extension-double-lift-family-of-elements (λ x (_ : C x) → D x) c d)
  (f : extension-double-lift-family-of-elements (λ x (_ : B x) → C x) b c)
  where

  family-of-elements-comp-extension-double-lift-family-of-elements :
    (x : A) → B x → D x
  family-of-elements-comp-extension-double-lift-family-of-elements x =
    family-of-elements-extension-double-lift-family-of-elements g x ∘
    family-of-elements-extension-double-lift-family-of-elements f x

  is-extension-comp-extension-double-lift-family-of-elements :
    is-extension-double-lift-family-of-elements
      ( λ x _ → D x)
      ( b)
      ( d)
      ( family-of-elements-comp-extension-double-lift-family-of-elements)
  is-extension-comp-extension-double-lift-family-of-elements i =
    ( ap
      ( family-of-elements-extension-double-lift-family-of-elements g (a i))
      ( is-extension-extension-double-lift-family-of-elements f i)) ∙
    ( is-extension-extension-double-lift-family-of-elements g i)

  comp-extension-double-lift-family-of-elements :
    extension-double-lift-family-of-elements (λ x (_ : B x) → D x) b d
  pr1 comp-extension-double-lift-family-of-elements =
    family-of-elements-comp-extension-double-lift-family-of-elements
  pr2 comp-extension-double-lift-family-of-elements =
    is-extension-comp-extension-double-lift-family-of-elements
```

## See also

- [Extensions of lifts of families of elements](orthogonal-factorization-systems.extensions-lifts-families-of-elements.md)
- [Extensions of maps](orthogonal-factorization-systems.extensions-maps.md)
- [The universal property of the family of fibers of a map](foundation.universal-property-family-of-fibers-of-maps.md)
