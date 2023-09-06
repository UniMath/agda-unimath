# Transport along homotopies

```agda
module foundation.transport-along-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.homotopies
open import foundation-core.transport
```

</details>

## Idea

If `C : (x : A) → B x → 𝒰` is a type family, and `H : f ~ g` is a homotopy between functions `f g : (x : A) → B x`, then there is a natural transport operation that transports an element `z : C x (f x)` along the homotopy `H` to an element of type `C x (g x)`.

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

  tr-htpy² :
    {H K : f ~ g} (L : H ~ K) (f' : (x : A) → C x (f x)) →
    tr-htpy H f' ~ tr-htpy K f'
  tr-htpy² L f' x = tr² (C x) (L x) (f' x)
```

