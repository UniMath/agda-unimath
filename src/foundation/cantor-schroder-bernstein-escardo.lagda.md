# The Cantor–Schröder–Bernstein–Escardó theorem

```agda
module foundation.cantor-schroder-bernstein-escardo where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.injective-maps
open import foundation.law-of-excluded-middle
open import foundation.perfect-images
open import foundation.split-surjective-maps
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.sets
```

</details>

## Idea

The classical Cantor–Schröder–Bernstein theorem asserts that from any pair of
[injective maps](foundation-core.injective-maps.md) `f : A → B` and `g : B → A`
we can construct a bijection between `A` and `B`. In a recent generalization,
Escardó proved that a Cantor–Schröder–Bernstein theorem also holds for
∞-groupoids. His generalization asserts that given two types that
[embed](foundation-core.embeddings.md) into each other, then the types are
[equivalent](foundation-core.equivalences.md). {{#cite Esc21}}

The Cantor–Schröder–Bernstein theorem is the
[25th](literature.100-theorems.md#25) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Statement

```agda
type-Cantor-Schröder-Bernstein-Escardó : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
type-Cantor-Schröder-Bernstein-Escardó l1 l2 =
  {X : UU l1} {Y : UU l2} → (X ↪ Y) → (Y ↪ X) → X ≃ Y
```

## Proof

### The law of excluded middle implies Cantor-Schröder-Bernstein-Escardó

```agda
module _
  {l1 l2 : Level} (lem : LEM (l1 ⊔ l2))
  where

  module _
    {X : UU l1} {Y : UU l2} (f : X ↪ Y) (g : Y ↪ X)
    where

    map-Cantor-Schröder-Bernstein-Escardó' :
      (x : X) → is-decidable (is-perfect-image (map-emb f) (map-emb g) x) → Y
    map-Cantor-Schröder-Bernstein-Escardó' x (inl y) =
      inverse-of-perfect-image x y
    map-Cantor-Schröder-Bernstein-Escardó' x (inr y) =
      map-emb f x

    map-Cantor-Schröder-Bernstein-Escardó :
      X → Y
    map-Cantor-Schröder-Bernstein-Escardó x =
      map-Cantor-Schröder-Bernstein-Escardó' x
        ( is-decidable-is-perfect-image-is-emb (is-emb-map-emb g) lem x)

    is-injective-map-Cantor-Schröder-Bernstein-Escardó :
      is-injective map-Cantor-Schröder-Bernstein-Escardó
    is-injective-map-Cantor-Schröder-Bernstein-Escardó {x} {x'} =
      l (is-decidable-is-perfect-image-is-emb (is-emb-map-emb g) lem x)
      (is-decidable-is-perfect-image-is-emb (is-emb-map-emb g) lem x')
      where
      l :
        (d : is-decidable (is-perfect-image (map-emb f) (map-emb g) x))
        (d' : is-decidable (is-perfect-image (map-emb f) (map-emb g) x')) →
        ( map-Cantor-Schröder-Bernstein-Escardó' x d) ＝
        ( map-Cantor-Schröder-Bernstein-Escardó' x' d') →
        x ＝ x'
      l (inl ρ) (inl ρ') p =
        inv (is-section-inverse-of-perfect-image x ρ) ∙
          (ap (map-emb g) p ∙ is-section-inverse-of-perfect-image x' ρ')
      l (inl ρ) (inr nρ') p =
        ex-falso (perfect-image-has-distinct-image x' x nρ' ρ (inv p))
      l (inr nρ) (inl ρ') p =
        ex-falso (perfect-image-has-distinct-image x x' nρ ρ' p)
      l (inr nρ) (inr nρ') p =
        is-injective-is-emb (is-emb-map-emb f) p

    is-split-surjective-map-Cantor-Schröder-Bernstein-Escardó :
      is-split-surjective map-Cantor-Schröder-Bernstein-Escardó
    is-split-surjective-map-Cantor-Schröder-Bernstein-Escardó y =
      pair x p
      where
      a :
        is-decidable
          ( is-perfect-image (map-emb f) (map-emb g) (map-emb g y)) →
        Σ ( X)
          ( λ x →
            ( (d : is-decidable (is-perfect-image (map-emb f) (map-emb g) x)) →
              map-Cantor-Schröder-Bernstein-Escardó' x d ＝ y))
      a (inl γ) =
        pair (map-emb g y) ψ
        where
        ψ :
          ( d :
            is-decidable
              ( is-perfect-image (map-emb f) (map-emb g) (map-emb g y))) →
          map-Cantor-Schröder-Bernstein-Escardó' (map-emb g y) d ＝ y
        ψ (inl v') =
          is-retraction-inverse-of-perfect-image
            { is-emb-g = is-emb-map-emb g}
            ( y)
            ( v')
        ψ (inr v) = ex-falso (v γ)
      a (inr γ) =
        pair x ψ
        where
        w :
          Σ ( fiber (map-emb f) y)
            ( λ s → ¬ (is-perfect-image (map-emb f) (map-emb g) (pr1 s)))
        w =
          not-perfect-image-has-not-perfect-fiber
            ( is-emb-map-emb f)
            ( is-emb-map-emb g)
            ( lem)
            ( y)
            ( γ)
        x : X
        x = pr1 (pr1 w)
        p : map-emb f x ＝ y
        p = pr2 (pr1 w)
        ψ :
          ( d : is-decidable (is-perfect-image (map-emb f) (map-emb g) x)) →
          map-Cantor-Schröder-Bernstein-Escardó' x d ＝ y
        ψ (inl v) = ex-falso ((pr2 w) v)
        ψ (inr v) = p
      b :
        Σ ( X)
          ( λ x →
            ( (d : is-decidable (is-perfect-image (map-emb f) (map-emb g) x)) →
              map-Cantor-Schröder-Bernstein-Escardó' x d ＝ y))
      b =
        a ( is-decidable-is-perfect-image-is-emb
            ( is-emb-map-emb g)
            ( lem)
            ( map-emb g y))
      x : X
      x = pr1 b
      p : map-Cantor-Schröder-Bernstein-Escardó x ＝ y
      p = pr2 b (is-decidable-is-perfect-image-is-emb (is-emb-map-emb g) lem x)

    is-equiv-map-Cantor-Schröder-Bernstein-Escardó :
      is-equiv map-Cantor-Schröder-Bernstein-Escardó
    is-equiv-map-Cantor-Schröder-Bernstein-Escardó =
      is-equiv-is-split-surjective-is-injective
        map-Cantor-Schröder-Bernstein-Escardó
        is-injective-map-Cantor-Schröder-Bernstein-Escardó
        is-split-surjective-map-Cantor-Schröder-Bernstein-Escardó

  Cantor-Schröder-Bernstein-Escardó :
    type-Cantor-Schröder-Bernstein-Escardó l1 l2
  pr1 (Cantor-Schröder-Bernstein-Escardó f g) =
    map-Cantor-Schröder-Bernstein-Escardó f g
  pr2 (Cantor-Schröder-Bernstein-Escardó f g) =
    is-equiv-map-Cantor-Schröder-Bernstein-Escardó f g
```

## Corollaries

### The Cantor–Schröder–Bernstein theorem

```agda
Cantor-Schröder-Bernstein :
  {l1 l2 : Level} (lem : LEM (l1 ⊔ l2))
  (A : Set l1) (B : Set l2) →
  injection (type-Set A) (type-Set B) →
  injection (type-Set B) (type-Set A) →
  (type-Set A) ≃ (type-Set B)
Cantor-Schröder-Bernstein lem A B f g =
  Cantor-Schröder-Bernstein-Escardó lem (emb-injection B f) (emb-injection A g)
```

## References

- Escardó's formalizations regarding this theorem can be found at
  <https://www.cs.bham.ac.uk/~mhe/TypeTopology/CantorSchroederBernstein.index.html>.
  {{#cite TypeTopology}}

{{#bibliography}}

## See also

The Cantor–Schröder–Bernstein–Escardó theorem holds constructively for many
notions of finite type, including

- [Finite types](univalent-combinatorics.finite-types.md) (unformalized)
- [Subfinite types](univalent-combinatorics.subfinite-types.md)
- [Kuratowski finite sets](univalent-combinatorics.kuratowski-finite-sets.md)
- [Subfinitely enumerable types](univalent-combinatorics.subfinitely-enumerable-types.md)
- [Dedekind finite types](univalent-combinatorics.dedekind-finite-types.md)
