# Dependent homotopies

```agda
module foundation.dependent-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.homotopies
```

</details>

## Idea

Consider a [homotopy](foundation-core.homotopies.md) `H : f ~ g` between two
functions `f g : (x : A) → B x`. Furthermore, consider a type family
`C : (x : A) → B x → 𝒰` and two functions

```text
  f' : (x : A) → C x (f x)
  g' : (x : A) → C x (g x)
```

A {{#concept "dependent homotopy" Agda=dependent-homotopy}} from `f'` to `g'`
over `H` is a family of
[dependent identifications](foundation-core.dependent-identifications.md) from
`f' x` to `g' x` over `H x`.

## Definitions

### Dependent homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  {f g : (x : A) → B x} (H : f ~ g)
  where

  dependent-homotopy :
    ((x : A) → C x (f x)) → ((x : A) → C x (g x)) → UU (l1 ⊔ l3)
  dependent-homotopy f' g' =
    (x : A) → dependent-identification (C x) (H x) (f' x) (g' x)

  dependent-homotopy' :
    ((x : A) → C x (f x)) → ((x : A) → C x (g x)) → UU (l1 ⊔ l3)
  dependent-homotopy' f' g' =
    (x : A) → dependent-identification' (C x) (H x) (f' x) (g' x)
```

### The reflexive dependent homotopy

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  {f : (x : A) → B x}
  where

  refl-dependent-homotopy :
    {f' : (x : A) → C x (f x)} → dependent-homotopy C refl-htpy f' f'
  refl-dependent-homotopy x = refl-dependent-identification (C x)

  refl-dependent-homotopy' :
    {f' : (x : A) → C x (f x)} → dependent-homotopy' C refl-htpy f' f'
  refl-dependent-homotopy' x = refl-dependent-identification' (C x)
```

### Iterated dependent homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  {f g : (x : A) → B x} {H K : f ~ g} (L : H ~ K)
  where

  dependent-homotopy² :
    {f' : (x : A) → C x (f x)} {g' : (x : A) → C x (g x)} →
    dependent-homotopy C H f' g' →
    dependent-homotopy C K f' g' → UU (l1 ⊔ l3)
  dependent-homotopy² {f'} {g'} H' K' =
    (x : A) → dependent-identification² (C x) (L x) (H' x) (K' x)
```
