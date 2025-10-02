# `K`-Equivalences

```agda
module orthogonal-factorization-systems.subuniverse-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.precomposition-functions-into-subuniverses
open import foundation.propositional-truncations
open import foundation.subuniverses
open import foundation.truncations
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universal-property-truncation
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

Given a [subuniverse](foundation.subuniverses.md) `K`, A map `f : A → B` is said
to be a
{{#concept "`K`-equivalence" Disambiguation="map of types" Agda=is-subuniverse-equiv}}
if it satisfies the
{{#concept "universal property" Disambiguation="subuniverse connected map of types"}}
of `K`-equivalences:

For every `K`-type `U`, the
[precomposition map](foundation-core.precomposition-functions.md)

```text
 - ∘ f : (B → U) → (A → U)
```

is an [equivalence](foundation-core.equivalences.md).

## Definition

```agda
is-subuniverse-equiv :
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) {A : UU l1} {B : UU l2} →
  (A → B) → UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4)
is-subuniverse-equiv K f =
  (U : type-subuniverse K) → is-equiv (precomp f (pr1 U))

subuniverse-equiv :
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) →
  UU l1 → UU l2 → UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4)
subuniverse-equiv K A B = Σ (A → B) (is-subuniverse-equiv K)

module _
  {l1 l2 l3 l4 : Level}
  (K : subuniverse l3 l4) {A : UU l1} {B : UU l2}
  (f : subuniverse-equiv K A B)
  where

  map-subuniverse-equiv : A → B
  map-subuniverse-equiv = pr1 f

  is-subuniverse-equiv-subuniverse-equiv :
    is-subuniverse-equiv K map-subuniverse-equiv
  is-subuniverse-equiv-subuniverse-equiv = pr2 f
```

## Properties

### Equivalences are `K`-equivalences for all `K`

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4)
  {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-subuniverse-equiv-is-equiv : is-equiv f → is-subuniverse-equiv K f
  is-subuniverse-equiv-is-equiv H U = is-equiv-precomp-is-equiv f H (pr1 U)
```

### The identity map is a `K`-equivalence for all `K`

```agda
is-subuniverse-equiv-id :
  {l1 l2 l3 : Level} (K : subuniverse l2 l3) {A : UU l1} →
  is-subuniverse-equiv K (id' A)
is-subuniverse-equiv-id K = is-subuniverse-equiv-is-equiv K id is-equiv-id
```

### The `K`-equivalences are closed under homotopies

```agda
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4)
  {A : UU l1} {B : UU l2} {f g : A → B}
  where

  is-subuniverse-equiv-htpy :
    f ~ g → is-subuniverse-equiv K g → is-subuniverse-equiv K f
  is-subuniverse-equiv-htpy H G U =
    is-equiv-htpy (precomp g (pr1 U)) (htpy-precomp H (pr1 U)) (G U)

  is-subuniverse-equiv-htpy' :
    f ~ g → is-subuniverse-equiv K f → is-subuniverse-equiv K g
  is-subuniverse-equiv-htpy' H G U =
    is-equiv-htpy' (precomp f (pr1 U)) (htpy-precomp H (pr1 U)) (G U)
```

### The `K`-equivalences are closed under composition

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l4 l5)
  {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-subuniverse-equiv-comp :
    (g : B → C) (f : A → B) →
    is-subuniverse-equiv K f →
    is-subuniverse-equiv K g →
    is-subuniverse-equiv K (g ∘ f)
  is-subuniverse-equiv-comp g f F G U =
    is-equiv-comp (precomp f (pr1 U)) (precomp g (pr1 U)) (G U) (F U)

  subuniverse-equiv-comp :
    subuniverse-equiv K B C →
    subuniverse-equiv K A B →
    subuniverse-equiv K A C
  pr1 (subuniverse-equiv-comp g f) =
    map-subuniverse-equiv K g ∘ map-subuniverse-equiv K f
  pr2 (subuniverse-equiv-comp g f) =
    is-subuniverse-equiv-comp
      ( map-subuniverse-equiv K g)
      ( map-subuniverse-equiv K f)
      ( is-subuniverse-equiv-subuniverse-equiv K f)
      ( is-subuniverse-equiv-subuniverse-equiv K g)
```

### The class of `K`-equivalences has the 3-for-2 property

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l4 l5)
  {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) (GF : is-subuniverse-equiv K (g ∘ f))
  where

  is-subuniverse-equiv-left-factor :
    is-subuniverse-equiv K f → is-subuniverse-equiv K g
  is-subuniverse-equiv-left-factor F U =
    is-equiv-right-factor (precomp f (pr1 U)) (precomp g (pr1 U)) (F U) (GF U)

  is-subuniverse-equiv-right-factor :
    is-subuniverse-equiv K g → is-subuniverse-equiv K f
  is-subuniverse-equiv-right-factor G U =
    is-equiv-left-factor (precomp f (pr1 U)) (precomp g (pr1 U)) (GF U) (G U)
```

### Sections of `K`-equivalences are `K`-equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-subuniverse-equiv-map-section :
    (K : subuniverse l3 l4) (s : section f) →
    is-subuniverse-equiv K f →
    is-subuniverse-equiv K (map-section f s)
  is-subuniverse-equiv-map-section K (s , h) =
    is-subuniverse-equiv-right-factor K f s
      ( is-subuniverse-equiv-is-equiv K (f ∘ s) (is-equiv-htpy-id h))
```

### Retractions of `K`-equivalences are `K`-equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-subuniverse-equiv-map-retraction :
    (K : subuniverse l3 l4) (r : retraction f) →
    is-subuniverse-equiv K f →
    is-subuniverse-equiv K (map-retraction f r)
  is-subuniverse-equiv-map-retraction K (r , h) =
    is-subuniverse-equiv-left-factor K r f
      ( is-subuniverse-equiv-is-equiv K (r ∘ f) (is-equiv-htpy-id h))
```

### Composing `K`-equivalences with equivalences

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l4 l5)
  {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-subuniverse-equiv-is-equiv-is-subuniverse-equiv :
    (g : B → C) (f : A → B) →
    is-subuniverse-equiv K g →
    is-equiv f →
    is-subuniverse-equiv K (g ∘ f)
  is-subuniverse-equiv-is-equiv-is-subuniverse-equiv g f eg ef =
    is-subuniverse-equiv-comp K g f
      ( is-subuniverse-equiv-is-equiv K f ef)
      ( eg)

  is-subuniverse-equiv-is-subuniverse-equiv-is-equiv :
    (g : B → C) (f : A → B) →
    is-equiv g →
    is-subuniverse-equiv K f →
    is-subuniverse-equiv K (g ∘ f)
  is-subuniverse-equiv-is-subuniverse-equiv-is-equiv g f eg ef =
    is-subuniverse-equiv-comp K g f
      ( ef)
      ( is-subuniverse-equiv-is-equiv K g eg)

  is-subuniverse-equiv-equiv-is-subuniverse-equiv :
    (g : B → C) (f : A ≃ B) →
    is-subuniverse-equiv K g →
    is-subuniverse-equiv K (g ∘ map-equiv f)
  is-subuniverse-equiv-equiv-is-subuniverse-equiv g (f , ef) eg =
    is-subuniverse-equiv-is-equiv-is-subuniverse-equiv g f eg ef

  is-subuniverse-equiv-is-subuniverse-equiv-equiv :
    (g : B ≃ C) (f : A → B) →
    is-subuniverse-equiv K f →
    is-subuniverse-equiv K (map-equiv g ∘ f)
  is-subuniverse-equiv-is-subuniverse-equiv-equiv (g , eg) f ef =
    is-subuniverse-equiv-is-subuniverse-equiv-is-equiv g f eg ef
```

### Being `K`-connected is invariant under `K`-equivalences

```text
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) {A : UU l1} {B : UU l2}
  where

  is-connected-is-subuniverse-equiv-is-connected :
    (f : A → B) → is-subuniverse-equiv K f →
    is-connected K B → is-connected K A
  is-connected-is-subuniverse-equiv-is-connected f e =
    is-contr-equiv (type-trunc K B) (map-trunc K f , e)

  is-connected-is-subuniverse-equiv-is-connected' :
    (f : A → B) → is-subuniverse-equiv K f →
    is-connected K A → is-connected K B
  is-connected-is-subuniverse-equiv-is-connected' f e =
    is-contr-equiv' (type-trunc K A) (map-trunc K f , e)

  is-connected-subuniverse-equiv-is-connected :
    subuniverse-equiv K A B → is-connected K B → is-connected K A
  is-connected-subuniverse-equiv-is-connected f =
    is-connected-is-subuniverse-equiv-is-connected
      ( map-subuniverse-equiv K f)
      ( is-subuniverse-equiv-subuniverse-equiv K f)

  is-connected-subuniverse-equiv-is-connected' :
    subuniverse-equiv K A B → is-connected K A → is-connected K B
  is-connected-subuniverse-equiv-is-connected' f =
    is-connected-is-subuniverse-equiv-is-connected'
      ( map-subuniverse-equiv K f)
      ( is-subuniverse-equiv-subuniverse-equiv K f)
```

### Every `ΣK`-equivalence is `K`-connected

This is a generalization of Proposition 2.30 in {{#cite CORS20}}.

```text
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-connected-map-is-succ-subuniverse-equiv :
    is-subuniverse-equiv (succ-𝕋 K) f → is-connected-map K f
  is-connected-map-is-succ-subuniverse-equiv e b =
    is-connected-subuniverse-equiv-is-connected
      ( subuniverse-equiv-fiber-map-trunc-fiber f b)
      ( is-connected-map-is-equiv e (unit-trunc b))
```

### A map is `K`-connected if and only if its `ΣK`-localization is

```text
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-connected-map-trunc-succ-is-succ-connected-domain :
    is-connected-map K f →
    is-connected-map K (map-trunc (succ-𝕋 K) f)
  is-connected-map-trunc-succ-is-succ-connected-domain cf t =
    apply-universal-property-trunc-Prop
      ( is-surjective-unit-trunc-succ t)
      ( is-connected-Prop K (fiber (map-trunc (succ-𝕋 K) f) t))
      ( λ (b , p) →
        tr
          ( λ s → is-connected K (fiber (map-trunc (succ-𝕋 K) f) s))
          ( p)
          ( is-connected-subuniverse-equiv-is-connected'
            ( subuniverse-equiv-fiber-map-trunc-fiber f b)
            ( cf b)))

  is-connected-map-is-connected-map-trunc-succ :
    is-connected-map K (map-trunc (succ-𝕋 K) f) →
    is-connected-map K f
  is-connected-map-is-connected-map-trunc-succ cf' b =
    is-connected-subuniverse-equiv-is-connected
      ( subuniverse-equiv-fiber-map-trunc-fiber f b)
      ( cf' (unit-trunc b))
```

### The codomain of a `K`-connected map is `ΣK`-connected if its domain is `ΣK`-connected

This follows part of the proof of Proposition 2.31 in {{#cite CORS20}}.

**Proof.** Let $f : A → B$ be a $K$-connected map on a $K+1$-connected domain.
To show that the codomain is $K+1$-connected it is enough to show that $f$ is a
$K+1$-equivalence, in other words, that $║f║ₖ₊₁$ is an equivalence. By previous
computations we know that $║f║ₖ₊₁$ is $K$-truncated since the domain is
$K+1$-connected, and that $║f║ₖ₊₁$ is $K$-connected since $f$ is $K$-connected,
so we are done. ∎

```text
module _
  {l1 l2 l3 l4 : Level} (K : subuniverse l3 l4) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-subuniverse-equiv-succ-is-succ-connected-domain-is-connected-map :
    is-connected-map K f →
    is-connected (succ-𝕋 K) A →
    is-subuniverse-equiv (succ-𝕋 K) f
  is-subuniverse-equiv-succ-is-succ-connected-domain-is-connected-map
    cf cA =
    is-equiv-is-connected-map-is-trunc-map
      ( is-trunc-map-trunc-succ-is-succ-connected-domain f cA)
      ( is-connected-map-trunc-succ-is-succ-connected-domain cf)

  is-succ-connected-codomain-is-succ-connected-domain-is-connected-map :
    is-connected-map K f →
    is-connected (succ-𝕋 K) A →
    is-connected (succ-𝕋 K) B
  is-succ-connected-codomain-is-succ-connected-domain-is-connected-map cf cA =
    is-connected-is-subuniverse-equiv-is-connected' f
      ( is-subuniverse-equiv-succ-is-succ-connected-domain-is-connected-map
        ( cf)
        ( cA))
      ( cA)
```

### If `g ∘ f` is `ΣK`-connected, then `f` is `K`-connected if and only if `g` is `ΣK`-connected

This is an instance of Proposition 2.31 in {{#cite CORS20}}.

**Proof.** If $g$ is $ΣK$-connected then by the cancellation property of
$ΣK$-equivalences, $f$ is a $K+1$-equivalence, and so in particular
$K$-connected.

Conversely, assume $f$ is $K$-connected. We want to show that the fibers of $g$
are $K+1$-connected, so let $c$ be an element of the codomain of $g$. The fibers
of the composite $g ∘ f$ compute as

$$
  \operatorname{fiber}_{g\circ f}(c) ≃
  \sum_{(b , p) : \operatorname{fiber}_{g}(c)}{\operatorname{fiber}_{f}(b)}.
$$

By the previous lemma, since $\operatorname{fiber}_{g\circ f}(c)$ is
$K+1$-connected, $\operatorname{fiber}_{g}(c)$ is $K+1$-connected if the first
projection map of this type is $K$-connected, and its fibers compute to the
fibers of $f$. ∎

```text
module _
  {l1 l2 l3 l4 l5 : Level} (K : subuniverse l4 l5) {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) (cgf : is-connected-map (succ-𝕋 K) (g ∘ f))
  where

  is-succ-subuniverse-equiv-right-factor-is-succ-connected-map-left-factor :
    is-connected-map (succ-𝕋 K) g → is-subuniverse-equiv (succ-𝕋 K) f
  is-succ-subuniverse-equiv-right-factor-is-succ-connected-map-left-factor
    cg =
    is-subuniverse-equiv-right-factor g f
      ( is-subuniverse-equiv-is-connected-map (g ∘ f) cgf)
      ( is-subuniverse-equiv-is-connected-map g cg)

  is-connected-map-right-factor-is-succ-connected-map-left-factor :
    is-connected-map (succ-𝕋 K) g → is-connected-map K f
  is-connected-map-right-factor-is-succ-connected-map-left-factor cg =
    is-connected-map-is-succ-subuniverse-equiv f
      ( is-succ-subuniverse-equiv-right-factor-is-succ-connected-map-left-factor
        ( cg))

  is-connected-map-right-factor-is-succ-connected-map-right-factor :
    is-connected-map K f → is-connected-map (succ-𝕋 K) g
  is-connected-map-right-factor-is-succ-connected-map-right-factor cf c =
    is-succ-connected-codomain-is-succ-connected-domain-is-connected-map
      ( pr1)
      ( λ p →
        is-connected-equiv
          ( equiv-fiber-pr1 (fiber f ∘ pr1) p)
          ( cf (pr1 p)))
      ( is-connected-equiv' (compute-fiber-comp g f c) (cgf c))
```

As a corollary, if $g ∘ f$ is $(K + 1)$-connected for some $g$, and $f$ is
$K$-connected, then $f$ is a $K+1$-equivalence.

```text
  is-succ-truncation-equiv-is-succ-connected-comp :
    is-connected-map K f → is-subuniverse-equiv (succ-𝕋 K) f
  is-succ-truncation-equiv-is-succ-connected-comp cf =
    is-succ-subuniverse-equiv-right-factor-is-succ-connected-map-left-factor
    ( is-connected-map-right-factor-is-succ-connected-map-right-factor cf)
```

### A `K`-equivalence with a section is `K`-connected

**Proof.** If $K ≐ -2$ notice that every map is $-2$-connected. So let
$K ≐ n + 1$ for some truncation level $n$ and let $f$ be our $K$-equivalence
with a section $s$. By assumption, we have a commuting triangle of maps

```text
        A
      ∧   \
   s /     \ f
    /       ∨
  B ======== B.
```

By the previous lemma, since the identity map is $K$-connected, it thus suffices
to show that $s$ is $n$-connected. But by the cancellation property of
$n+1$-equivalences $s$ is an $n+1$-equivalence and $n+1$-equivalences are in
particular $n$-connected. ∎

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-connected-map-section-is-subuniverse-equiv-succ :
    (K : subuniverse l3 l4) (s : section f) →
    is-subuniverse-equiv (succ-𝕋 K) f →
    is-connected-map K (map-section f s)
  is-connected-map-section-is-subuniverse-equiv-succ K (s , h) e =
    is-connected-map-is-succ-subuniverse-equiv s
      ( is-subuniverse-equiv-map-section (succ-𝕋 K) (s , h) e)

  is-connected-map-is-subuniverse-equiv-section :
    (K : subuniverse l3 l4) →
    section f → is-subuniverse-equiv K f → is-connected-map K f
  is-connected-map-is-subuniverse-equiv-section neg-two-𝕋 (s , h) e =
    is-neg-two-connected-map f
  is-connected-map-is-subuniverse-equiv-section (succ-𝕋 K) (s , h) e =
    is-connected-map-right-factor-is-succ-connected-map-right-factor f s
      ( is-connected-map-htpy-id h)
      ( is-connected-map-section-is-subuniverse-equiv-succ K (s , h) e)
```

## References

- The notion of `K`-equivalence is a special case of the notion of
  `L`-equivalence, where `L` is a reflective subuniverse. These were studied in
  {{#cite CORS20}}.
- The class of `K`-equivalences is
  [left orthogonal](orthogonal-factorization-systems.orthogonal-maps.md) to the
  class of `K`-étale maps. This was shown in {{#cite CR21}}.

{{#bibliography}}
