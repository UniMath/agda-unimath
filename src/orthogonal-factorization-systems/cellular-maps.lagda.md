# Cellular maps

```agda
module orthogonal-factorization-systems.cellular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-maps
open import foundation.truncation-levels
open import foundation.universe-levels

open import orthogonal-factorization-systems.mere-lifting-properties
```

</details>

## Idea

A map `f : A → B` is said to be **`k`-cellular** if it satisfies the left
[mere lifting property](orthogonal-factorization-systems.mere-lifting-properties.md)
with respect to [`k`-connected maps](foundation.connected-maps.md). In other
words, a map `f` is `k`-cellular if the
[pullback-hom](orthogonal-factorization-systems.pullback-hom.md)

```text
  ⟨ f , g ⟩
```

with any `k`-connected map `g` is [surjective](foundation.surjective-maps.md).
The terminology `k`-cellular comes from the fact that the `k`-connected maps are
precisely the maps that satisfy the right mere lifting property with respect to
the [spheres](synthetic-homotopy-theory.spheres.md)

```text
  Sⁱ → unit
```

for all `-1 ≤ i ≤ k`. In this sense, `k`-cellular maps are "built out of
spheres". Alternatively, `k`-cellular maps might also be called **`k`-projective
maps**. This emphasizes the condition that `k`-projective maps lift against
`k`-connected maps.

In the topos of spaces, the `k`-cellular maps are the left class of an
_external_ weak factorization system on spaces of which the right class is the
class of `k`-connected maps, but there is no such weak factorization system
definable internally.

## Definitions

### The predicate of being a `k`-cellular map

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-cellular-map : UUω
  is-cellular-map =
    {l3 l4 : Level} {X : UU l3} {Y : UU l4} (g : X → Y) →
    is-connected-map k g → mere-diagonal-lift f g
```
