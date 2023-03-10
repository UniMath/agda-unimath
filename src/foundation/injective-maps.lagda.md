# Injective maps

```agda
module foundation.injective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.injective-maps public

open import foundation-core.empty-types
open import foundation-core.universe-levels
```

</details>

## Idea

A map `f : A → B` is injective if `Id (f x) (f y)` implies `Id x y`.

## Warning

The notion of injective map is, however, not homotopically coherent. It is fine to use injectivity for maps between sets, but for maps between general types it is recommended to use the notion of embedding.

## Examples

### Any map out of an empty type is injective

```agda
is-injective-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-empty A → is-injective f
is-injective-is-empty f is-empty-A {x} = ex-falso (is-empty-A x)
```
