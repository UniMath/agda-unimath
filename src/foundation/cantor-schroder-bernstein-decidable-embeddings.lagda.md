# The Cantor–Schröder–Bernstein theorem for decidable embeddings

```agda
module foundation.cantor-schroder-bernstein-decidable-embeddings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-embeddings
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation-dense-equality-maps
open import foundation.function-types
open import foundation.injective-maps
open import foundation.perfect-images
open import foundation.sections
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.negation

open import logic.double-negation-eliminating-maps
open import logic.double-negation-stable-embeddings
```

</details>

## Idea

Assuming the
[weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md),
then if two types mutually embed via
[decidable embeddings](foundation.decidable-embeddings.md), `A ↪ᵈ B` and
`B ↪ᵈ A`, then `A` and `B` are [equivalent](foundation-core.equivalences.md)
types.

Classically, the Cantor–Schröder–Bernstein theorem asserts that from any pair of
[injective maps](foundation-core.injective-maps.md) between sets `f : A → B` and
`g : B → A` we can construct a bijection between `A` and `B`. In a recent
generalization, Escardó proved that a Cantor–Schröder–Bernstein theorem also
holds for ∞-groupoids {{#cite Esc21}}. His generalization asserts that given two
types that [embed](foundation-core.embeddings.md) into each other, then the
types are [equivalent](foundation-core.equivalences.md).

In this file we give a fine-grained analysis of the construction used in the
proof of this
[Cantor–Schröder–Bernstein-Escardó theorem](foundation.cantor-schroder-bernstein-escardo.md),
and use this deconstruction to give a generalization of the theorem for
[decidable embeddings](foundation.decidable-embeddings.md).

## Construction

Given a pair of mutual maps `f : A → B` and `g : B → A` such that

1. the maps `f` and `g` satisfy double negation elimination on their fibers
2. `f` has double negation dense equality
3. `g` is injective
4. the perfect image of `g` relative to `f` is decidable

Then `B` is a retract of `A`. If `f` moreover is injective, then this retract is
an equivalence.

This can be understood as an entirely constructive formulation of the
Cantor–Schröder–Bernstein theorem.

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (G' : is-injective g)
  (G : is-double-negation-eliminating-map g)
  (F : is-double-negation-eliminating-map f)
  where

  map-construction-Cantor-Schröder-Bernstein' :
    (x : A) → is-decidable (is-perfect-image f g x) → B
  map-construction-Cantor-Schröder-Bernstein'
    x (inl γ) =
    inverse-of-perfect-image x γ
  map-construction-Cantor-Schröder-Bernstein'
    x (inr nγ) =
    f x

  compute-map-construction-Cantor-Schröder-Bernstein' :
    (y : B) →
    (γ : is-perfect-image f g (g y)) →
    (d : is-decidable (is-perfect-image f g (g y))) →
    map-construction-Cantor-Schröder-Bernstein'
      ( g y) d ＝
    y
  compute-map-construction-Cantor-Schröder-Bernstein'
    y γ (inl v') =
    is-retraction-inverse-of-perfect-image G' y v'
  compute-map-construction-Cantor-Schröder-Bernstein'
    y γ (inr v) =
    ex-falso (v γ)

  compute-map-construction-on-not-perfect-image-Cantor-Schröder-Bernstein :
    (F' : has-double-negation-dense-equality-map f) →
    (y : B) →
    (nγ : ¬ (is-perfect-image f g (g y))) →
    (d :
      is-decidable
        ( is-perfect-image f g
          ( element-has-nonperfect-fiber-is-not-perfect-image
              G G' F F' y nγ))) →
    map-construction-Cantor-Schröder-Bernstein'
      ( element-has-nonperfect-fiber-is-not-perfect-image G G' F F' y nγ)
      ( d) ＝
    y
  compute-map-construction-on-not-perfect-image-Cantor-Schröder-Bernstein
    F' y nγ (inl v) =
    ex-falso
      ( is-not-perfect-image-has-nonperfect-fiber-is-not-perfect-image
          G G' F F' y nγ v)
  compute-map-construction-on-not-perfect-image-Cantor-Schröder-Bernstein
    F' y nγ (inr _) =
    is-in-fiber-element-has-nonperfect-fiber-is-not-perfect-image
      G G' F F' y nγ

  map-section-construction-Cantor-Schröder-Bernstein' :
    (F' : has-double-negation-dense-equality-map f) →
    (y : B) → is-decidable (is-perfect-image f g (g y)) → A
  map-section-construction-Cantor-Schröder-Bernstein'
    F' y (inl _) = g y
  map-section-construction-Cantor-Schröder-Bernstein'
    F' y (inr nγ) =
    element-has-nonperfect-fiber-is-not-perfect-image G G' F F' y nγ

  is-section-map-section-construction-Cantor-Schröder-Bernstein' :
    (F' : has-double-negation-dense-equality-map f) →
    (y : B)
    (d : is-decidable (is-perfect-image f g (g y))) →
    (d' :
      is-decidable
        ( is-perfect-image f g
          ( map-section-construction-Cantor-Schröder-Bernstein'
              F' y d))) →
    map-construction-Cantor-Schröder-Bernstein'
      ( map-section-construction-Cantor-Schröder-Bernstein'
          F' y d)
      ( d') ＝
    y
  is-section-map-section-construction-Cantor-Schröder-Bernstein'
    F' y (inl γ) =
    compute-map-construction-Cantor-Schröder-Bernstein'
      y γ
  is-section-map-section-construction-Cantor-Schröder-Bernstein'
    F' y (inr nγ) =
    compute-map-construction-on-not-perfect-image-Cantor-Schröder-Bernstein
      F' y nγ

  map-construction-Cantor-Schröder-Bernstein :
    (D : (x : A) → is-decidable (is-perfect-image f g x)) → A → B
  map-construction-Cantor-Schröder-Bernstein D x =
    map-construction-Cantor-Schröder-Bernstein' x (D x)

  map-section-construction-Cantor-Schröder-Bernstein :
    (F' : has-double-negation-dense-equality-map f) →
    (D : (y : B) → is-decidable (is-perfect-image f g (g y))) → B → A
  map-section-construction-Cantor-Schröder-Bernstein F' D y =
    map-section-construction-Cantor-Schröder-Bernstein'
      ( F')
      ( y)
      ( D y)

  is-section-map-section-construction-Cantor-Schröder-Bernstein :
    (F' : has-double-negation-dense-equality-map f) →
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    is-section
      ( map-construction-Cantor-Schröder-Bernstein D)
      ( map-section-construction-Cantor-Schröder-Bernstein F' (D ∘ g))
  is-section-map-section-construction-Cantor-Schröder-Bernstein F' D y =
    is-section-map-section-construction-Cantor-Schröder-Bernstein'
      ( F')
      ( y)
      ( D (g y))
      ( D ( map-section-construction-Cantor-Schröder-Bernstein
              F' (D ∘ g) y))

  section-construction-Cantor-Schröder-Bernstein :
    (F' : has-double-negation-dense-equality-map f) →
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    section (map-construction-Cantor-Schröder-Bernstein D)
  section-construction-Cantor-Schröder-Bernstein F' D =
    map-section-construction-Cantor-Schröder-Bernstein F' (D ∘ g) ,
    is-section-map-section-construction-Cantor-Schröder-Bernstein F' D
```

Injectivity of the constructed map.

```agda
  is-injective-map-construction-Cantor-Schröder-Bernstein' :
    (F' : is-injective f) →
    {x x' : A}
    (d : is-decidable (is-perfect-image f g x))
    (d' : is-decidable (is-perfect-image f g x')) →
    ( map-construction-Cantor-Schröder-Bernstein'
      ( x)
      ( d)) ＝
    ( map-construction-Cantor-Schröder-Bernstein'
      ( x')
      ( d')) →
    x ＝ x'
  is-injective-map-construction-Cantor-Schröder-Bernstein'
    F' { x} {x'} (inl ρ) (inl ρ') p =
    ( inv (is-section-inverse-of-perfect-image x ρ)) ∙
    ( ap g p ∙
      is-section-inverse-of-perfect-image x' ρ')
  is-injective-map-construction-Cantor-Schröder-Bernstein'
    F' {x} {x'} (inl ρ) (inr nρ') p =
    ex-falso (perfect-image-has-distinct-image x' x nρ' ρ (inv p))
  is-injective-map-construction-Cantor-Schröder-Bernstein'
    F' { x} {x'} (inr nρ) (inl ρ') p =
    ex-falso (perfect-image-has-distinct-image x x' nρ ρ' p)
  is-injective-map-construction-Cantor-Schröder-Bernstein'
    F' {lx} {x'} (inr nρ) (inr nρ') p = F' p
```

Piecing it all together.

```agda
  is-equiv-map-construction-Cantor-Schröder-Bernstein :
    (F' : has-double-negation-dense-equality-map f) →
    (F'' : is-injective f) →
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    is-equiv (map-construction-Cantor-Schröder-Bernstein D)
  is-equiv-map-construction-Cantor-Schröder-Bernstein
    F' F'' D =
    is-equiv-is-injective
      ( section-construction-Cantor-Schröder-Bernstein F' D)
      ( λ {x} {x'} →
        is-injective-map-construction-Cantor-Schröder-Bernstein'
          ( F'')
          ( D x)
          ( D x'))

  equiv-construction-Cantor-Schröder-Bernstein :
    (F' : has-double-negation-dense-equality-map f) →
    (F'' : is-injective f) →
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    A ≃ B
  equiv-construction-Cantor-Schröder-Bernstein F' F'' D =
    ( map-construction-Cantor-Schröder-Bernstein D ,
      is-equiv-map-construction-Cantor-Schröder-Bernstein F' F'' D)
```

## Theorem

It follows from the weak limited principle of omniscience that, for every pair
of mutual decidable embeddings `f : A ↪ B` and `g : B ↪ A`, it is decidable
for every element `x : A` whether `x` is a perfect image of `g` relative to `f`.

Applying this fact to the Cantor-Schröder-Bernstein construction, we conclude
that every pair of types that mutually embed into one another via decidable
embeddings are equivalent.

```agda
Cantor-Schröder-Bernstein-WLPO' :
  {l1 l2 : Level} → level-WLPO (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
  is-decidable-emb g → is-decidable-emb f →
  A ≃ B
Cantor-Schröder-Bernstein-WLPO' wlpo G F =
  equiv-construction-Cantor-Schröder-Bernstein
    ( is-injective-is-decidable-emb G)
    ( is-double-negation-eliminating-map-is-decidable-emb G)
    ( is-double-negation-eliminating-map-is-decidable-emb F)
    ( has-double-negation-dense-equality-map-is-emb (is-emb-is-decidable-emb F))
    ( is-injective-is-decidable-emb F)
    ( is-decidable-is-perfect-image-WLPO wlpo
      ( G)
      ( is-decidable-map-is-decidable-emb F)
      ( has-double-negation-dense-equality-map-is-emb
        ( is-emb-is-decidable-emb F)))

Cantor-Schröder-Bernstein-WLPO :
  {l1 l2 : Level} → level-WLPO (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} → (A ↪ᵈ B) → (B ↪ᵈ A) → A ≃ B
Cantor-Schröder-Bernstein-WLPO wlpo (f , F) (g , G) =
  Cantor-Schröder-Bernstein-WLPO' wlpo G F
```

## References

- Escardó's formalizations of this theorem can be found at
  <https://www.cs.bham.ac.uk/~mhe/TypeTopology/CantorSchroederBernstein.index.html>.
  {{#cite TypeTopology}}

{{#bibliography}}

## See also

The Cantor–Schröder–Bernstein theorem holds constructively for many notions of
finite type, including

- [Dedekind finite types](univalent-combinatorics.dedekind-finite-types.md)
- [Finite types](univalent-combinatorics.finite-types.md) (unformalized)
- [Finitely enumerable types](univalent-combinatorics.finitely-enumerable-types.md)
- [Kuratowski finite sets](univalent-combinatorics.kuratowski-finite-sets.md)
- [Subfinite types](univalent-combinatorics.subfinite-types.md)
- [Subfinitely enumerable types](univalent-combinatorics.subfinitely-enumerable-types.md)

See also the twin formalization in TypeTopology at
[`CantorSchroederBernstein.CSB-WLPO`](https://martinescardo.github.io/TypeTopology/CantorSchroederBernstein.CSB-WLPO.html).
There it is verified that the construction does not depend on any other axioms
than WLPO.

## External links

The Cantor–Schröder–Bernstein theorem is the 25th theorem on
[Freek Wiedijk's](http://www.cs.ru.nl/F.Wiedijk/) list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.
