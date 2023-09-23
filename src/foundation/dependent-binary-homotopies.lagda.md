# Dependent binary homotopies

```agda
module foundation.dependent-binary-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopies
open import foundation.universe-levels

open import foundation-core.dependent-identifications
```

</details>

## Idea

Consider a [binary homotopy](foundation-core.homotopies.md) `H : f ~ g` between
two functions `f g : (x : A) (y : B x) → C x y`. Furthermore, consider a type
family `D : (x : A) (y : B x) (z : C x y) → 𝒰` and two functions

```text
  f' : (x : A) (y : B x) → D x y (f x y)
  g' : (x : A) (y : B x) → D x y (g x y)
```

A **dependent binary homotopy** from `f'` to `g'` over `H` is a family of
[dependent identifications](foundation-core.dependent-identifications.md) from
`f' x y` to `g' x y` over `H x y`.

## Definitions

### Dependent homotopies

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  (D : (x : A) (y : B x) (z : C x y) → UU l4)
  {f g : (x : A) (y : B x) → C x y} (H : binary-htpy f g)
  where

  dependent-binary-homotopy :
    ((x : A) (y : B x) → D x y (f x y)) →
    ((x : A) (y : B x) → D x y (g x y)) → UU (l1 ⊔ l2 ⊔ l4)
  dependent-binary-homotopy f' g' =
    (x : A) (y : B x) →
    dependent-identification (D x y) (H x y) (f' x y) (g' x y)
```

### The reflexive dependent binary homotopy

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  (D : (x : A) (y : B x) (z : C x y) → UU l4)
  {f : (x : A) (y : B x) → C x y}
  where

  refl-dependent-binary-homotopy :
    {f' : (x : A) (y : B x) → D x y (f x y)} →
    dependent-binary-homotopy D (refl-binary-htpy f) f' f'
  refl-dependent-binary-homotopy {f'} = refl-binary-htpy f'
```
