# Idempotent maps

```agda
module foundation.idempotent-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.homotopy-algebra
open import foundation.iterate-confluent-maps
open import foundation.pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sets
```

</details>

## Idea

An {{#concept "idempotent map" Disambiguation="of types" Agda=is-idempotent}} is
a map `f : A → A` [equipped](foundation.structure.md) with a
[homotopy](foundation-core.homotopies.md)

```text
  f ∘ f ~ f.
```

While this definition corresponds to the classical concept of an idempotent map
in [set](foundation-core.sets.md)-level mathematics, a homotopy `I : f ∘ f ~ f`
may fail to be coherent with itself in Homotopy Type Theory. For instance, one
may ask for a second-order coherence

```text
  J : f ·r I ~ I ·l f
```

giving the definition of a
[quasicoherently idempotent map](foundation.quasicoherently-idempotent-maps.md).

The situation may be compared against that of
[invertible maps](foundation-core.invertible-maps.md) vs.
[coherently invertible maps](foundation-core.coherently-invertible-maps.md).
Recall that an _invertible map_ is a map `f : A → B` equipped with a converse
map `g : B → A` and homotopies `S : f ∘ g ~ id` and `R : g ∘ f ~ id` witnessing
that `g` is an _inverse_ of `f`, while a _coherently invertible map_ has an
additional coherence `f ·r R ~ S ·l f`.

It is true that every invertible map is coherently invertible, but no such
construction preserves both of the homotopies `S` and `R`. Likewise, every
quasicoherently idempotent map is also coherently idempotent, although again the
coherence `J` is replaced as part of this construction. On the other hand, in
contrast to invertible maps, not every idempotent map can be made to be fully
coherent or even quasicoherent. For a counterexample see Section 4 of
{{#cite Shu17}}.

**Terminology.** Our definition of an _idempotent map_ corresponds to the
definition of a _preidempotent map_ in {{#reference Shu17}} and
{{#reference Shu14SplittingIdempotents}}, while their definition of an
_idempotent map_ corresponds in our terminology to a _coherently idempotent
map_.

## Definitions

### The structure on a map of idempotence

```agda
is-idempotent : {l : Level} {A : UU l} → (A → A) → UU l
is-idempotent f = f ∘ f ~ f
```

### The type of idempotent maps on a type

```agda
idempotent-map : {l : Level} → UU l → UU l
idempotent-map A = Σ (A → A) (is-idempotent)

module _
  {l : Level} {A : UU l} (f : idempotent-map A)
  where

  map-idempotent-map : A → A
  map-idempotent-map = pr1 f

  is-idempotent-idempotent-map :
    is-idempotent map-idempotent-map
  is-idempotent-idempotent-map = pr2 f
```

## Properties

### Being an idempotent operation on a set is a property

```agda
module _
  {l : Level} {A : UU l} (is-set-A : is-set A) (f : A → A)
  where

  is-prop-is-idempotent-is-set : is-prop (is-idempotent f)
  is-prop-is-idempotent-is-set =
    is-prop-Π (λ x → is-set-A (f (f x)) (f x))

  is-idempotent-is-set-Prop : Prop l
  is-idempotent-is-set-Prop =
    ( is-idempotent f , is-prop-is-idempotent-is-set)

module _
  {l : Level} (A : Set l) (f : type-Set A → type-Set A)
  where

  is-prop-is-idempotent-Set : is-prop (is-idempotent f)
  is-prop-is-idempotent-Set =
    is-prop-is-idempotent-is-set (is-set-type-Set A) f

  is-idempotent-prop-Set : Prop l
  is-idempotent-prop-Set =
    ( is-idempotent f , is-prop-is-idempotent-Set)
```

### If `i` and `r` is an inclusion-retraction pair, then `i ∘ r` is idempotent

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (i : B → A) (r : A → B) (H : is-retraction i r)
  where

  is-idempotent-inclusion-retraction : is-idempotent (i ∘ r)
  is-idempotent-inclusion-retraction = i ·l H ·r r
```

### Idempotence is preserved by homotopies

If a map `g` is homotopic to an idempotent map `f`, then `g` is also idempotent.

```agda
module _
  {l : Level} {A : UU l} {f g : A → A} (F : is-idempotent f)
  where

  is-idempotent-htpy : g ~ f → is-idempotent g
  is-idempotent-htpy H =
    horizontal-concat-htpy H H ∙h F ∙h inv-htpy H

  is-idempotent-inv-htpy : f ~ g → is-idempotent g
  is-idempotent-inv-htpy H =
    horizontal-concat-htpy (inv-htpy H) (inv-htpy H) ∙h F ∙h H
```

### Pullback presentation of idempotent maps

The type of idempotent maps on a type `A` is the pullback

```text
     ∙ -------------> (A → A)
     | ⌟                 |
     |                   | iterate 2 × id
     ∨                   ∨
  (A → A) -----> (A → A) × (A → A).
            Δ
```

```agda
module _
  {l : Level} {A : UU l}
  where

  cone-idempotent-map :
    cone (λ f → f , f ∘ f) (λ g → g , g) (idempotent-map A)
  cone-idempotent-map =
    cone-iterate-confluent-map 2 1

  abstract
    is-pullback-cone-idempotent-map :
      is-pullback (λ f → f , f ∘ f) (λ g → g , g) cone-idempotent-map
    is-pullback-cone-idempotent-map =
      is-pullback-cone-iterate-confluent-map 2 1
```

## See also

- [Quasicoherently idempotent maps](foundation.quasicoherently-idempotent-maps.md)
- [Split idempotent maps](foundation.split-idempotent-maps.md)

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
