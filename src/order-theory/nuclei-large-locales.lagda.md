# Nuclei on large locales

```agda
module order-theory.nuclei-large-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.functions
open import foundation.identity-types
open import foundation.universe-levels

open import order-theory.homomorphisms-large-meet-semilattices
open import order-theory.large-locales
```

</details>

## Idea

A **nucleus** on a [large locale](order-theory.large-locales.md) `L` is an order
preserving map `j : hom-Large-Poset id L L` such that

- `j` preserves the top element
- `j(j(x)) ＝ j(x)`.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Locale α β)
  where

  record
    nucleus-Large-Locale : UUω
    where
    field
      hom-nucleus-Large-Locale :
        hom-Large-Meet-Semilattice
          ( large-meet-semilattice-Large-Locale L)
          ( large-meet-semilattice-Large-Locale L)
      is-idempotent-nucleus-Large-Locale :
        {l1 : Level} (x : type-Large-Locale L l1) →
        map-hom-Large-Meet-Semilattice
          ( large-meet-semilattice-Large-Locale L)
          ( large-meet-semilattice-Large-Locale L)
          ( hom-nucleus-Large-Locale)
          ( map-hom-Large-Meet-Semilattice
            ( large-meet-semilattice-Large-Locale L)
            ( large-meet-semilattice-Large-Locale L)
            ( hom-nucleus-Large-Locale)
            ( x)) ＝
        map-hom-Large-Meet-Semilattice
          ( large-meet-semilattice-Large-Locale L)
          ( large-meet-semilattice-Large-Locale L)
          ( hom-nucleus-Large-Locale)
          ( x)
```
