# The universal globular type

```agda
{-# OPTIONS --guardedness #-}

module structured-types.universal-globular-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.spans
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

The {{#concpept "universal globular type"}} `𝒢 l` at [universe level](foundation.universe-levels.md) `l` has the universe `UU l` as its type of `0`-cells, and uses iterated binary relations for its globular structure.

Specifically, the universal globular type is a translation from category theory into type theory of the Hofmann-Streicher universe {{#cite Awodey22}} of presheaves on the globular category `Γ`

```text
      s₀       s₁       s₂
    ----->   ----->   ----->
  0 -----> 1 -----> 2 -----> ⋯.
      t₀       t₁       t₂
```

The Hofmann-Streicher universe of presheaves on a category `𝒞` is the presheaf

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

  The functors `s₀ t₀ : Γ/0 → Γ/1` are given by `* ↦ s₀` and `* ↦ t₀`, respectively.

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
  
This means that:

- The type `0`-cells of the universal globular type is the universe of types `UU l`.
- The type of `1`-cells from `X` to `Y` of the universal globular type is the type of spans from `X` to `Y`.
- The type of `2`-cells 

## Definitions

### Iterated binary relations

```agda
record
  iterated-binary-relation
    {l1 : Level} (l2 : Level) (X Y : UU l1) : UU (l1 ⊔ lsuc l2)
  where
  coinductive
  field
    rel-iterated-binary-relation : (x : X) (y : Y) → UU l2
    iterated-binary-relation-rel-iterated-binary-relation :
      (x x' : X) (y y' : Y) →
      iterated-binary-relation l2
        ( rel-iterated-binary-relation x y)
        ( rel-iterated-binary-relation x' y')

open iterated-binary-relation public
```

### The universal globular type

```agda
0-cell-universal-Globular-Type : (l1 l2 : Level) → UU (lsuc l1)
0-cell-universal-Globular-Type l1 l2 = UU l1

globular-structure-universal-Globular-Type :
  (l1 l2 : Level) →
  globular-structure (l1 ⊔ lsuc l2) (0-cell-universal-Globular-Type l1 l2)
1-cell-globular-structure
  ( globular-structure-universal-Globular-Type l1 l2) X Y =
  X → Y → UU l2
globular-structure-1-cell-globular-structure
  ( globular-structure-universal-Globular-Type l1 l2) X Y =
  {!globular-structure-universal-Globular-Type ? ?!}

universal-Globular-Type : (l1 l2 : Level) → Globular-Type (lsuc l1) {!!}
pr1 (universal-Globular-Type l1 l2) = 0-cell-universal-Globular-Type l1 l2
pr2 (universal-Globular-Type l1 l2) = {!!}
  
```

## References

{{#bibliography}}
