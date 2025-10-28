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
open import foundation.double-negation-images
open import foundation.function-types
open import foundation.injective-maps
open import foundation.perfect-images
open import foundation.retracts-of-types
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

The
{{#concept "Cantor–Schröder–Bernstein theorem" Disambiguation="for decidable embeddings" Agda=Cantor-Schröder-Bernstein-WLPO}}
for [decidable embeddings](foundation.decidable-embeddings.md) states that,
assuming the
[weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
(WLPO), then if two types `A` and `B` mutually embed via
[embeddings](foundation-core.embeddings.md) whose
[fibers](foundation.fibers-of-maps.md) are
[decidable](foundation.decidable-types.md), then `A` and `B` are
[equivalent](foundation-core.equivalences.md) types.

Classically, i.e., under the assumption of the
[law of excluded middle](foundation.law-of-excluded-middle.md), the
Cantor–Schröder–Bernstein theorem asserts that from any pair of
[injective maps](foundation-core.injective-maps.md) between
[sets](foundation-core.sets.md) `f : A → B` and `g : B → A` we can construct a
bijection between `A` and `B`. In a recent generalization, Martín Escardó proved
that the Cantor–Schröder–Bernstein theorem also holds for ∞-groupoids
{{#cite Esc21}}. His generalization asserts that given two types that
[embed](foundation-core.embeddings.md) into each other, then the types are
[equivalent](foundation-core.equivalences.md).

In this file we present a fine-grained decomposition of the construction used in
the proof of this
[Cantor–Schröder–Bernstein-Escardó theorem](foundation.cantor-schroder-bernstein-escardo.md),
originally due to König {{#cite König1906}}, and use this deconstruction to give
the generalization of the theorem for
[decidable embeddings](foundation.decidable-embeddings.md) under the assumption
of the weak limited principle of omniscience.

## Construction

Given a pair of mutually converse maps `f : A → B` and `g : B → A` such that

1. the maps `f` and `g` satisfy double negation elimination on their fibers
2. `f` has double negation dense equality
3. `g` is injective
4. the [perfect image](foundation.perfect-images.md) of `g` relative to `f` is
   decidable

then `B` is a retract of `A`. If `f` moreover is injective, then this retract is
an equivalence.

This can be understood as an entirely constructive formulation of the
Cantor–Schröder–Bernstein theorem.

The reader may also note that under the additional assumption of
[function extensionality](foundation.function-extensionality.md), double
negation eliminating injections are double negation stable embeddings.

The underlying map `A → B` of the construction.

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  map-construction-Cantor-Schröder-Bernstein' :
    (x : A) → is-decidable (is-perfect-image f g x) → B
  map-construction-Cantor-Schröder-Bernstein' x (inl γ) =
    inverse-of-perfect-image x γ
  map-construction-Cantor-Schröder-Bernstein' x (inr nγ) =
    f x

  map-construction-Cantor-Schröder-Bernstein :
    (D : (x : A) → is-decidable (is-perfect-image f g x)) → A → B
  map-construction-Cantor-Schröder-Bernstein D x =
    map-construction-Cantor-Schröder-Bernstein' x (D x)
```

Computing the underlying map `A → B` of the construction.

```agda
  compute-map-construction-Cantor-Schröder-Bernstein' :
    (G' : is-injective g) →
    (y : B) →
    (γ : is-perfect-image f g (g y)) →
    (d : is-decidable (is-perfect-image f g (g y))) →
    map-construction-Cantor-Schröder-Bernstein'
      ( g y) d ＝
    y
  compute-map-construction-Cantor-Schröder-Bernstein' G' y γ (inl v') =
    is-retraction-inverse-of-perfect-image G' y v'
  compute-map-construction-Cantor-Schröder-Bernstein' G' y γ (inr v) =
    ex-falso (v γ)

  compute-map-construction-on-not-perfect-image-Cantor-Schröder-Bernstein :
    (G : is-double-negation-eliminating-map g)
    (G' : is-injective g)
    (F : is-double-negation-eliminating-map f)
    (F' : has-double-negation-dense-equality-map f) →
    (y : B) →
    (nγ : ¬ (is-perfect-image f g (g y))) →
    (d :
      is-decidable
        ( is-perfect-image f g
          ( element-has-not-perfect-fiber-is-not-perfect-image
              G G' F F' y nγ))) →
    map-construction-Cantor-Schröder-Bernstein'
      ( element-has-not-perfect-fiber-is-not-perfect-image G G' F F' y nγ)
      ( d) ＝
    y
  compute-map-construction-on-not-perfect-image-Cantor-Schröder-Bernstein
    G G' F F' y nγ (inl v) =
    ex-falso
      ( is-not-perfect-image-has-not-perfect-fiber-is-not-perfect-image
          G G' F F' y nγ v)
  compute-map-construction-on-not-perfect-image-Cantor-Schröder-Bernstein
    G G' F F' y nγ (inr _) =
    is-in-fiber-element-has-not-perfect-fiber-is-not-perfect-image
      G G' F F' y nγ
```

The underlying section `B → A` of the construction.

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (G : is-double-negation-eliminating-map g)
  (G' : is-injective g)
  (F : is-double-negation-eliminating-map f)
  (F' : has-double-negation-dense-equality-map f)
  where

  map-section-construction-Cantor-Schröder-Bernstein' :
    (y : B) → is-decidable (is-perfect-image f g (g y)) → A
  map-section-construction-Cantor-Schröder-Bernstein' y (inl _) =
    g y
  map-section-construction-Cantor-Schröder-Bernstein' y (inr nγ) =
    element-has-not-perfect-fiber-is-not-perfect-image G G' F F' y nγ

  map-section-construction-Cantor-Schröder-Bernstein :
    (D : (y : B) → is-decidable (is-perfect-image f g (g y))) →
    B → A
  map-section-construction-Cantor-Schröder-Bernstein D y =
    map-section-construction-Cantor-Schröder-Bernstein' y (D y)

  is-section-map-section-construction-Cantor-Schröder-Bernstein' :
    (y : B)
    (d : is-decidable (is-perfect-image f g (g y))) →
    (d' :
      is-decidable
        ( is-perfect-image f g
          ( map-section-construction-Cantor-Schröder-Bernstein' y d))) →
    map-construction-Cantor-Schröder-Bernstein'
      ( map-section-construction-Cantor-Schröder-Bernstein' y d)
      ( d') ＝
    y
  is-section-map-section-construction-Cantor-Schröder-Bernstein' y (inl γ) =
    compute-map-construction-Cantor-Schröder-Bernstein' G' y γ
  is-section-map-section-construction-Cantor-Schröder-Bernstein' y (inr nγ) =
    compute-map-construction-on-not-perfect-image-Cantor-Schröder-Bernstein
      G G' F F' y nγ

  is-section-map-section-construction-Cantor-Schröder-Bernstein :
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    is-section
      ( map-construction-Cantor-Schröder-Bernstein D)
      ( map-section-construction-Cantor-Schröder-Bernstein (D ∘ g))
  is-section-map-section-construction-Cantor-Schröder-Bernstein D y =
    is-section-map-section-construction-Cantor-Schröder-Bernstein' y
      ( D (g y))
      ( D (map-section-construction-Cantor-Schröder-Bernstein (D ∘ g) y))

  section-construction-Cantor-Schröder-Bernstein :
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    section (map-construction-Cantor-Schröder-Bernstein D)
  section-construction-Cantor-Schröder-Bernstein D =
    ( map-section-construction-Cantor-Schröder-Bernstein (D ∘ g) ,
      is-section-map-section-construction-Cantor-Schröder-Bernstein D)

  retract-construction-Cantor-Schröder-Bernstein :
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    B retract-of A
  retract-construction-Cantor-Schröder-Bernstein D =
    retract-section
      ( map-construction-Cantor-Schröder-Bernstein D)
      ( section-construction-Cantor-Schröder-Bernstein D)
```

Injectivity of the constructed map.

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (F' : is-injective f)
  where

  is-injective-map-construction-Cantor-Schröder-Bernstein' :
    {x x' : A}
    (d : is-decidable (is-perfect-image f g x))
    (d' : is-decidable (is-perfect-image f g x')) →
    map-construction-Cantor-Schröder-Bernstein' x d ＝
    map-construction-Cantor-Schröder-Bernstein' x' d' →
    x ＝ x'
  is-injective-map-construction-Cantor-Schröder-Bernstein'
    {x} {x'} (inl ρ) (inl ρ') p =
    ( inv (is-section-inverse-of-perfect-image x ρ)) ∙
    ( ap g p) ∙
    ( is-section-inverse-of-perfect-image x' ρ')
  is-injective-map-construction-Cantor-Schröder-Bernstein'
    {x} {x'} (inl ρ) (inr nρ') p =
    ex-falso (perfect-image-has-distinct-image x' x nρ' ρ (inv p))
  is-injective-map-construction-Cantor-Schröder-Bernstein'
    {x} {x'} (inr nρ) (inl ρ') p =
    ex-falso (perfect-image-has-distinct-image x x' nρ ρ' p)
  is-injective-map-construction-Cantor-Schröder-Bernstein'
    {x} {x'} (inr nρ) (inr nρ') p =
    F' p
```

Piecing it all together.

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (G : is-double-negation-eliminating-map g)
  (G' : is-injective g)
  (F : is-double-negation-eliminating-map f)
  (F'' : is-injective f)
  (D : (x : A) → is-decidable (is-perfect-image f g x))
  where

  is-equiv-map-construction-Cantor-Schröder-Bernstein :
    is-equiv (map-construction-Cantor-Schröder-Bernstein D)
  is-equiv-map-construction-Cantor-Schröder-Bernstein =
    is-equiv-is-injective
      ( section-construction-Cantor-Schröder-Bernstein G G' F
        ( has-double-negation-dense-equality-map-is-emb
          ( is-emb-is-injective-is-double-negation-eliminating-map F F''))
        ( D))
      ( λ {x} {x'} →
        is-injective-map-construction-Cantor-Schröder-Bernstein' F''
          ( D x)
          ( D x'))

  equiv-construction-Cantor-Schröder-Bernstein : A ≃ B
  equiv-construction-Cantor-Schröder-Bernstein =
    ( map-construction-Cantor-Schröder-Bernstein D ,
      is-equiv-map-construction-Cantor-Schröder-Bernstein)
```

## Theorem

It follows from the weak limited principle of omniscience that, for every pair
of mutual decidable embeddings `f : A ↪ B` and `g : B ↪ A`, it is decidable
for every element `x : A` whether `x` is a perfect image of `g` relative to `f`.
Applying this fact to the Cantor-Schröder-Bernstein construction, we conclude
with the main result.

```agda
module _
   {l1 l2 : Level} (wlpo : level-WLPO (l1 ⊔ l2))
   {A : UU l1} {B : UU l2}
  where

  abstract
    Cantor-Schröder-Bernstein-WLPO' :
      {f : A → B} {g : B → A} →
      is-decidable-emb g →
      is-decidable-emb f →
      A ≃ B
    Cantor-Schröder-Bernstein-WLPO' G F =
      equiv-construction-Cantor-Schröder-Bernstein
        ( is-double-negation-eliminating-map-is-decidable-emb G)
        ( is-injective-is-decidable-emb G)
        ( is-double-negation-eliminating-map-is-decidable-emb F)
        ( is-injective-is-decidable-emb F)
        ( is-decidable-is-perfect-image-WLPO wlpo
          ( G)
          ( is-decidable-map-is-decidable-emb F)
          ( has-double-negation-dense-equality-map-is-emb
            ( is-emb-is-decidable-emb F)))

    Cantor-Schröder-Bernstein-WLPO : (A ↪ᵈ B) → (B ↪ᵈ A) → A ≃ B
    Cantor-Schröder-Bernstein-WLPO (f , F) (g , G) =
      Cantor-Schröder-Bernstein-WLPO' G F
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

## External links

- See also the twin formalization in TypeTopology at
  [`CantorSchroederBernstein.CSB-WLPO`](https://martinescardo.github.io/TypeTopology/CantorSchroederBernstein.CSB-WLPO.html).
  There it is verified that the construction does not depend on any other axioms
  than WLPO, and the assumption that `f` has double negation dense equality on
  fibers is somewhat further weakened.

- The Cantor–Schröder–Bernstein theorem is the 25th theorem on
  [Freek Wiedijk's](http://www.cs.ru.nl/F.Wiedijk/) list of
  [100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.
