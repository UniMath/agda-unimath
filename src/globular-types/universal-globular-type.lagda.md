# The universal globular type

```agda
{-# OPTIONS --guardedness #-}

open import foundation.function-extensionality-axiom

module
  globular-types.universal-globular-type
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.spans
open import foundation.universe-levels

open import globular-types.dependent-globular-types funext
open import globular-types.exponentials-globular-types funext
open import globular-types.globular-maps funext
open import globular-types.globular-types
```

</details>

## Idea

The {{#concept "universal globular type"}} `𝒢 l` at
[universe level](foundation.universe-levels.md) `l` has the universe `UU l` as
its type of `0`-cells, and uses iterated binary relations for its globular
structure.

Specifically, the universal globular type is a translation from category theory
into type theory of the Hofmann–Streicher universe {{#cite Awodey22}} of
presheaves on the globular category `Γ`

```text
      s₀       s₁       s₂
    ----->   ----->   ----->
  0 -----> 1 -----> 2 -----> ⋯.
      t₀       t₁       t₂
```

The Hofmann–Streicher universe of presheaves on a category `𝒞` is the presheaf

```text
     𝒰_𝒞 I := Presheaf 𝒞/I
  El_𝒞 I A := A *,
```

where `*` is the terminal object of `𝒞/I`, i.e., the identity morphism on `I`.

We compute a few instances of the slice category `Γ/I`:

- The slice category `Γ/0` is the terminal category.
- The slice category `Γ/1` is the representing cospan

  ```text
         s₀       t₀
    s₀ -----> 1 <----- t₀
  ```

  The functors `s₀ t₀ : Γ/0 → Γ/1` are given by `* ↦ s₀` and `* ↦ t₀`,
  respectively.

- The slice category `Γ/2` is the free category on the graph

  ```text
    s₁s₀             t₁s₀
     |                 |
     |                 |
     ∨                 ∨
    s₁ -----> 1 <----- t₁
     ∧                 ∧
     |                 |
     |                 |
    s₁t₀             t₁t₀
  ```

  and so on. The functors `s₁ t₁ : Γ/1 → Γ/2` are given by

  ```text
    s₀ ↦ s₁s₀                   s₀ ↦ t₁s₀
     1 ↦ s₁           and        1 ↦ t₁
    t₀ ↦ s₁t₀                   t₀ ↦ t₁t₀
  ```

  respectively.

More specifically, the slice category `Γ/n` is isomorphic to the iterated
suspension `Σⁿ1` of the terminal category.

This means that:

- The type `0`-cells of the universal globular type is the universe of types
  `UU l`.
- The type of `1`-cells from `X` to `Y` of the universal globular type is the
  type of spans from `X` to `Y`.
- The type of `2`-cells between any two spans `R` and `S` from `X` to `Y` is the
  type of families of spans from `R x y` to `S x y` indexed by `x : X` and
  `y : Y`, and so on.

In other words, the universal globular type `𝒰` has the universe of types as its
type of `0`-cells, and for any two types `X` and `Y`, the globular type of
`1`-cells is the double
[exponent](globular-types.exponentials-globular-types.md) `(𝒰^Y)^X` of globular
types.

Unfortunately, the termination checking algorithm isn't able to establish that
this definition is terminating. Nevertheless, when termination checking is
turned off for this definition, the types of the `n`-cells come out correctly
for low values of `n`.

## Definitions

### The universal globular type

```agda
0-cell-universal-Globular-Type : (l1 l2 : Level) → UU (lsuc l1)
0-cell-universal-Globular-Type l1 l2 = UU l1

{-# TERMINATING #-}

universal-Globular-Type :
  (l1 l2 : Level) → Globular-Type (lsuc l1) (l1 ⊔ lsuc l2)
0-cell-Globular-Type (universal-Globular-Type l1 l2) =
  0-cell-universal-Globular-Type l1 l2
1-cell-globular-type-Globular-Type (universal-Globular-Type l1 l2) X Y =
  exponential-Globular-Type X
    ( exponential-Globular-Type Y (universal-Globular-Type l2 l2))

1-cell-universal-Globular-Type :
  {l1 l2 : Level} (X Y : UU l1) → UU (l1 ⊔ lsuc l2)
1-cell-universal-Globular-Type {l1} {l2} =
  1-cell-Globular-Type (universal-Globular-Type l1 l2)

2-cell-universal-Globular-Type :
  {l1 l2 : Level} {X Y : UU l1} (R S : X → Y → UU l2) → UU (l1 ⊔ lsuc l2)
2-cell-universal-Globular-Type {l1} {l2} {X} {Y} =
  2-cell-Globular-Type (universal-Globular-Type l1 l2)

3-cell-universal-Globular-Type :
  {l1 l2 : Level} {X Y : UU l1} {R S : X → Y → UU l2}
  (A B : (x : X) (y : Y) → R x y → S x y → UU l2) → UU (l1 ⊔ lsuc l2)
3-cell-universal-Globular-Type {l1} {l2} =
  3-cell-Globular-Type (universal-Globular-Type l1 l2)
```

### Dependent globular types

#### Morphisms into the universal globular type induce dependent globular types

```agda
0-cell-dependent-globular-type-hom-universal-Globular-Type :
  {l1 l2 l3 l4 : Level} (G : Globular-Type l1 l2)
  (h : globular-map G (universal-Globular-Type l3 l4)) →
  0-cell-Globular-Type G → UU l3
0-cell-dependent-globular-type-hom-universal-Globular-Type G h =
  0-cell-globular-map h

dependent-globular-type-hom-universal-Globular-Type :
  {l1 l2 l3 l4 : Level} (G : Globular-Type l1 l2)
  (h : globular-map G (universal-Globular-Type l3 l4)) →
  Dependent-Globular-Type l3 l4 G
0-cell-Dependent-Globular-Type
  ( dependent-globular-type-hom-universal-Globular-Type G h) =
  0-cell-dependent-globular-type-hom-universal-Globular-Type G h
1-cell-dependent-globular-type-Dependent-Globular-Type
  ( dependent-globular-type-hom-universal-Globular-Type G h)
  {x} {x'} y y' =
  dependent-globular-type-hom-universal-Globular-Type
    ( 1-cell-globular-type-Globular-Type G x x')
    ( ev-hom-exponential-Globular-Type
      ( ev-hom-exponential-Globular-Type
        ( 1-cell-globular-map-globular-map h {x} {x'})
        ( y))
      ( y'))
```

#### Dependent globular types induce morphisms into the universal globular type

```agda
{-# TERMINATING #-}

characteristic-globular-map-Dependent-Globular-Type :
  {l1 l2 l3 l4 : Level} {G : Globular-Type l1 l2}
  (H : Dependent-Globular-Type l3 l4 G) →
  globular-map G (universal-Globular-Type l3 l4)
0-cell-globular-map
  ( characteristic-globular-map-Dependent-Globular-Type {G = G} H) =
  0-cell-Dependent-Globular-Type H
1-cell-globular-map-globular-map
  ( characteristic-globular-map-Dependent-Globular-Type {G = G} H) {x} {x'} =
  bind-family-globular-maps
    ( λ y →
      bind-family-globular-maps
        ( λ y' →
          characteristic-globular-map-Dependent-Globular-Type
            ( 1-cell-dependent-globular-type-Dependent-Globular-Type H y y')))
```

## References

{{#bibliography}}
