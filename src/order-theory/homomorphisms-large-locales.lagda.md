# Homomorphisms of large locales

```agda
module order-theory.homomorphisms-large-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import order-theory.homomorphisms-large-frames
open import order-theory.large-locales
```

</details>

## Idea

A **homomorphism of large locales** from `K` to `L` is a
[frame homomorphism](order-theory.homomorphisms-large-frames.md) from `L` to
`K`.

## Definition

```agda
module _
  {αK αL : Level → Level} {βK βL : Level → Level → Level} {γ : Level}
  (K : Large-Locale αK βK γ) (L : Large-Locale αL βL γ)
  where

  hom-Large-Locale : UUω
  hom-Large-Locale = hom-Large-Frame L K

  module _
    (f : hom-Large-Locale)
    where

    map-hom-Large-Locale :
      {l1 : Level} → type-Large-Locale L l1 → type-Large-Locale K l1
    map-hom-Large-Locale = map-hom-Large-Frame L K f

    preserves-order-hom-Large-Locale :
      {l1 l2 : Level}
      (x : type-Large-Locale L l1) (y : type-Large-Locale L l2) →
      leq-Large-Locale L x y →
      leq-Large-Locale K (map-hom-Large-Locale x) (map-hom-Large-Locale y)
    preserves-order-hom-Large-Locale = preserves-order-hom-Large-Frame L K f

    preserves-meets-hom-Large-Locale :
      {l1 l2 : Level}
      (x : type-Large-Locale L l1) (y : type-Large-Locale L l2) →
      map-hom-Large-Locale (meet-Large-Locale L x y) ＝
      meet-Large-Locale K (map-hom-Large-Locale x) (map-hom-Large-Locale y)
    preserves-meets-hom-Large-Locale = preserves-meets-hom-Large-Frame L K f

    preserves-top-hom-Large-Locale :
      map-hom-Large-Locale (top-Large-Locale L) ＝ top-Large-Locale K
    preserves-top-hom-Large-Locale = preserves-top-hom-Large-Frame L K f

    preserves-sup-hom-Large-Locale :
      {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Locale L l2) →
      map-hom-Large-Locale (sup-Large-Locale L x) ＝
      sup-Large-Locale K (λ i → map-hom-Large-Locale (x i))
    preserves-sup-hom-Large-Locale = preserves-sup-hom-Large-Frame f
```
