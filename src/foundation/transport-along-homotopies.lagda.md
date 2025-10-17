# Transport along homotopies

```agda
module foundation.transport-along-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.homotopy-induction
open import foundation.transport-along-higher-identifications
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

If `C : (x : A) → B x → 𝒰` is a type family, and `H : f ~ g` is a homotopy
between functions `f g : (x : A) → B x`, then there is a natural transport
operation that transports an element `z : C x (f x)` along the homotopy `H` to
an element of type `C x (g x)`.

## Definitions

### Transporting along homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  {f g : (x : A) → B x}
  where

  tr-htpy :
    (f ~ g) → ((x : A) → C x (f x)) → ((x : A) → C x (g x))
  tr-htpy H f' x = tr (C x) (H x) (f' x)

  inv-tr-htpy :
    (f ~ g) → ((x : A) → C x (g x)) → ((x : A) → C x (f x))
  inv-tr-htpy H f' x = inv-tr (C x) (H x) (f' x)

  tr-htpy² :
    {H K : f ~ g} (L : H ~ K) (f' : (x : A) → C x (f x)) →
    tr-htpy H f' ~ tr-htpy K f'
  tr-htpy² L f' x = tr² (C x) (L x) (f' x)
```

## Properties

### Transport along a homotopy `H` is homotopic to transport along the identification `eq-htpy H`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  where

  statement-compute-tr-htpy :
    {f g : (x : A) → B x} (H : f ~ g) → UU (l1 ⊔ l3)
  statement-compute-tr-htpy H =
    tr (λ u → (x : A) → C x (u x)) (eq-htpy H) ~ tr-htpy C H

  base-case-compute-tr-htpy :
    {f : (x : A) → B x} → statement-compute-tr-htpy (refl-htpy' f)
  base-case-compute-tr-htpy =
    htpy-eq (ap (tr (λ u → (x : A) → C x (u x))) (eq-htpy-refl-htpy _))

  abstract
    compute-tr-htpy :
      {f g : (x : A) → B x} (H : f ~ g) → statement-compute-tr-htpy H
    compute-tr-htpy {f} =
      ind-htpy f
        ( λ _ → statement-compute-tr-htpy)
        ( base-case-compute-tr-htpy)

    compute-tr-htpy-refl-htpy :
      {f : (x : A) → B x} →
      compute-tr-htpy (refl-htpy' f) ＝ base-case-compute-tr-htpy
    compute-tr-htpy-refl-htpy {f} =
      compute-ind-htpy f
        ( λ _ → statement-compute-tr-htpy)
        ( base-case-compute-tr-htpy)
```

### Inverse transport along a homotopy `H` is homotopic to inverse transport along the identification `eq-htpy H`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  where

  statement-compute-inv-tr-htpy :
    {f g : (x : A) → B x} (H : f ~ g) → UU (l1 ⊔ l3)
  statement-compute-inv-tr-htpy H =
    inv-tr (λ u → (x : A) → C x (u x)) (eq-htpy H) ~ inv-tr-htpy C H

  base-case-compute-inv-tr-htpy :
    {f : (x : A) → B x} → statement-compute-inv-tr-htpy (refl-htpy' f)
  base-case-compute-inv-tr-htpy =
    htpy-eq (ap (inv-tr (λ u → (x : A) → C x (u x))) (eq-htpy-refl-htpy _))

  abstract
    compute-inv-tr-htpy :
      {f g : (x : A) → B x} (H : f ~ g) → statement-compute-inv-tr-htpy H
    compute-inv-tr-htpy {f} =
      ind-htpy f
        ( λ _ → statement-compute-inv-tr-htpy)
        ( base-case-compute-inv-tr-htpy)

    compute-inv-tr-htpy-refl-htpy :
      {f : (x : A) → B x} →
      compute-inv-tr-htpy (refl-htpy' f) ＝ base-case-compute-inv-tr-htpy
    compute-inv-tr-htpy-refl-htpy {f} =
      compute-ind-htpy f
        ( λ _ → statement-compute-inv-tr-htpy)
        ( base-case-compute-inv-tr-htpy)
```
