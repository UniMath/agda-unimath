# `k`-Equivalences

```agda
module foundation.truncation-equivalences where
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
open import foundation.precomposition-functions-into-subuniverses
open import foundation.propositional-truncations
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
open import foundation-core.precomposition-functions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A map `f : A → B` is said to be a
{{#concept "`k`-equivalence" Disambiguation="truncations of types" Agda=truncation-equivalence}}
if the map `map-trunc k f : trunc k A → trunc k B` is an
[equivalence](foundation-core.equivalences.md).

## Definition

```agda
is-truncation-equivalence :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-truncation-equivalence k f = is-equiv (map-trunc k f)

truncation-equivalence :
  {l1 l2 : Level} (k : 𝕋) → UU l1 → UU l2 → UU (l1 ⊔ l2)
truncation-equivalence k A B = Σ (A → B) (is-truncation-equivalence k)

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  (f : truncation-equivalence k A B)
  where

  map-truncation-equivalence : A → B
  map-truncation-equivalence = pr1 f

  is-truncation-equivalence-truncation-equivalence :
    is-truncation-equivalence k map-truncation-equivalence
  is-truncation-equivalence-truncation-equivalence = pr2 f

  map-trunc-truncation-equivalence : type-trunc k A → type-trunc k B
  map-trunc-truncation-equivalence = map-trunc k map-truncation-equivalence

  equiv-trunc-truncation-equivalence : type-trunc k A ≃ type-trunc k B
  equiv-trunc-truncation-equivalence =
    ( map-trunc-truncation-equivalence ,
      is-truncation-equivalence-truncation-equivalence)
```

## Properties

### A map `f : A → B` is a `k`-equivalence if and only if `- ∘ f : (B → X) → (A → X)` is an equivalence for every `k`-truncated type `X`

```agda
is-equiv-precomp-is-truncation-equivalence :
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-truncation-equivalence k f →
  (X : Truncated-Type l3 k) → is-equiv (precomp f (type-Truncated-Type X))
is-equiv-precomp-is-truncation-equivalence k f H X =
  is-equiv-bottom-is-equiv-top-square
    ( precomp unit-trunc (type-Truncated-Type X))
    ( precomp unit-trunc (type-Truncated-Type X))
    ( precomp (map-trunc k f) (type-Truncated-Type X))
    ( precomp f (type-Truncated-Type X))
    ( precomp-coherence-square-maps
      ( unit-trunc)
      ( f)
      ( map-trunc k f)
      ( unit-trunc)
      ( inv-htpy (coherence-square-map-trunc k f))
      ( type-Truncated-Type X))
    ( is-truncation-trunc X)
    ( is-truncation-trunc X)
    ( is-equiv-precomp-is-equiv (map-trunc k f) H (type-Truncated-Type X))

is-truncation-equivalence-is-equiv-precomp :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  ( (l : Level) (X : Truncated-Type l k) →
    is-equiv (precomp f (type-Truncated-Type X))) →
  is-truncation-equivalence k f
is-truncation-equivalence-is-equiv-precomp k {A} {B} f H =
  is-equiv-is-equiv-precomp-Truncated-Type k
    ( trunc k A)
    ( trunc k B)
    ( map-trunc k f)
    ( λ X →
      is-equiv-top-is-equiv-bottom-square
        ( precomp unit-trunc (type-Truncated-Type X))
        ( precomp unit-trunc (type-Truncated-Type X))
        ( precomp (map-trunc k f) (type-Truncated-Type X))
        ( precomp f (type-Truncated-Type X))
        ( precomp-coherence-square-maps
          ( unit-trunc)
          ( f)
          ( map-trunc k f)
          ( unit-trunc)
          ( inv-htpy (coherence-square-map-trunc k f))
          ( type-Truncated-Type X))
        ( is-truncation-trunc X)
        ( is-truncation-trunc X)
        ( H _ X))
```

### Equivalences are `k`-equivalences for all `k`

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncation-equivalence-is-equiv :
    is-equiv f → is-truncation-equivalence k f
  is-truncation-equivalence-is-equiv e = is-equiv-map-equiv-trunc k (f , e)
```

### The identity map is a `k`-equivalence for all `k`

```agda
is-truncation-equivalence-id :
  {l : Level} {k : 𝕋} {A : UU l} → is-truncation-equivalence k (id' A)
is-truncation-equivalence-id = is-truncation-equivalence-is-equiv id is-equiv-id
```

### The `k`-equivalences are closed under homotopies

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f g : A → B}
  where

  is-truncation-equivalence-htpy :
    f ~ g → is-truncation-equivalence k g → is-truncation-equivalence k f
  is-truncation-equivalence-htpy H =
    is-equiv-htpy (map-trunc k g) (htpy-trunc H)

  is-truncation-equivalence-htpy' :
    f ~ g → is-truncation-equivalence k f → is-truncation-equivalence k g
  is-truncation-equivalence-htpy' H =
    is-equiv-htpy' (map-trunc k f) (htpy-trunc H)
```

### Every `k`-connected map is a `k`-equivalence

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncation-equivalence-is-connected-map :
    is-connected-map k f → is-truncation-equivalence k f
  is-truncation-equivalence-is-connected-map c =
    is-truncation-equivalence-is-equiv-precomp k f
      ( λ l X → dependent-universal-property-is-connected-map k c (λ _ → X))
```

### The `k`-equivalences are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-truncation-equivalence-comp :
    (g : B → C) (f : A → B) →
    is-truncation-equivalence k f →
    is-truncation-equivalence k g →
    is-truncation-equivalence k (g ∘ f)
  is-truncation-equivalence-comp g f ef eg =
    is-equiv-htpy
      ( map-trunc k g ∘ map-trunc k f)
      ( preserves-comp-map-trunc k g f)
      ( is-equiv-comp (map-trunc k g) (map-trunc k f) ef eg)

  truncation-equivalence-comp :
    truncation-equivalence k B C →
    truncation-equivalence k A B →
    truncation-equivalence k A C
  pr1 (truncation-equivalence-comp g f) =
    map-truncation-equivalence k g ∘ map-truncation-equivalence k f
  pr2 (truncation-equivalence-comp g f) =
    is-truncation-equivalence-comp
      ( map-truncation-equivalence k g)
      ( map-truncation-equivalence k f)
      ( is-truncation-equivalence-truncation-equivalence k f)
      ( is-truncation-equivalence-truncation-equivalence k g)
```

### The class of `k`-equivalences has the 3-for-2 property

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) (e : is-truncation-equivalence k (g ∘ f))
  where

  is-truncation-equivalence-left-factor :
    is-truncation-equivalence k f → is-truncation-equivalence k g
  is-truncation-equivalence-left-factor =
    is-equiv-left-factor
      ( map-trunc k g)
      ( map-trunc k f)
      ( is-equiv-htpy'
        ( map-trunc k (g ∘ f))
        ( preserves-comp-map-trunc k g f)
        ( e))

  is-truncation-equivalence-right-factor :
    is-truncation-equivalence k g → is-truncation-equivalence k f
  is-truncation-equivalence-right-factor eg =
    is-equiv-right-factor
      ( map-trunc k g)
      ( map-trunc k f)
      ( eg)
      ( is-equiv-htpy'
        ( map-trunc k (g ∘ f))
        ( preserves-comp-map-trunc k g f)
        ( e))
```

### Sections of `k`-equivalences are `k`-equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-truncation-equivalence-map-section :
    (k : 𝕋) (s : section f) →
    is-truncation-equivalence k f →
    is-truncation-equivalence k (map-section f s)
  is-truncation-equivalence-map-section k (s , h) =
    is-truncation-equivalence-right-factor f s
      ( is-truncation-equivalence-is-equiv (f ∘ s) (is-equiv-htpy-id h))
```

### Retractions of `k`-equivalences are `k`-equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-truncation-equivalence-map-retraction :
    (k : 𝕋) (r : retraction f) →
    is-truncation-equivalence k f →
    is-truncation-equivalence k (map-retraction f r)
  is-truncation-equivalence-map-retraction k (r , h) =
    is-truncation-equivalence-left-factor r f
      ( is-truncation-equivalence-is-equiv (r ∘ f) (is-equiv-htpy-id h))
```

### Composing `k`-equivalences with equivalences

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-truncation-equivalence-is-equiv-is-truncation-equivalence :
    (g : B → C) (f : A → B) →
    is-truncation-equivalence k g →
    is-equiv f →
    is-truncation-equivalence k (g ∘ f)
  is-truncation-equivalence-is-equiv-is-truncation-equivalence g f eg ef =
    is-truncation-equivalence-comp g f
      ( is-truncation-equivalence-is-equiv f ef)
      ( eg)

  is-truncation-equivalence-is-truncation-equivalence-is-equiv :
    (g : B → C) (f : A → B) →
    is-equiv g →
    is-truncation-equivalence k f →
    is-truncation-equivalence k (g ∘ f)
  is-truncation-equivalence-is-truncation-equivalence-is-equiv g f eg ef =
    is-truncation-equivalence-comp g f
      ( ef)
      ( is-truncation-equivalence-is-equiv g eg)

  is-truncation-equivalence-equiv-is-truncation-equivalence :
    (g : B → C) (f : A ≃ B) →
    is-truncation-equivalence k g →
    is-truncation-equivalence k (g ∘ map-equiv f)
  is-truncation-equivalence-equiv-is-truncation-equivalence g f eg =
    is-truncation-equivalence-is-equiv-is-truncation-equivalence g
      ( map-equiv f)
      ( eg)
      ( is-equiv-map-equiv f)

  is-truncation-equivalence-is-truncation-equivalence-equiv :
    (g : B ≃ C) (f : A → B) →
    is-truncation-equivalence k f →
    is-truncation-equivalence k (map-equiv g ∘ f)
  is-truncation-equivalence-is-truncation-equivalence-equiv g f ef =
    is-truncation-equivalence-is-truncation-equivalence-is-equiv
      ( map-equiv g)
      ( f)
      ( is-equiv-map-equiv g)
      ( ef)
```

### The map on dependent pair types induced by the unit of the `(k+1)`-truncation is a `k`-equivalence

This is an instance of Lemma 2.27 in {{#cite CORS20}} listed below.

```agda
module _
  {l1 l2 : Level} {k : 𝕋}
  {X : UU l1} (P : (type-trunc (succ-𝕋 k) X) → UU l2)
  where

  map-Σ-map-base-unit-trunc :
    Σ X (P ∘ unit-trunc) → Σ (type-trunc (succ-𝕋 k) X) P
  map-Σ-map-base-unit-trunc = map-Σ-map-base unit-trunc P

  is-truncation-equivalence-map-Σ-map-base-unit-trunc :
    is-truncation-equivalence k map-Σ-map-base-unit-trunc
  is-truncation-equivalence-map-Σ-map-base-unit-trunc =
    is-truncation-equivalence-is-equiv-precomp k
      ( map-Σ-map-base-unit-trunc)
      ( λ l X →
        is-equiv-equiv
          ( equiv-ev-pair)
          ( equiv-ev-pair)
          ( refl-htpy)
          ( dependent-universal-property-trunc
            ( λ t →
              ( ( P t → type-Truncated-Type X) ,
                ( is-trunc-succ-is-trunc k
                  ( is-trunc-function-type k
                    ( is-trunc-type-Truncated-Type X)))))))
```

### There is a `k`-equivalence between the fiber of a map and the fiber of its `(k+1)`-truncation

This is an instance of Corollary 2.29 in {{#cite CORS20}}.

We consider the following composition of maps

```text
   fiber f b = Σ A (λ a → f a = b)
             → Σ A (λ a → ║f a ＝ b║)
             ≃ Σ A (λ a → |f a| = |b|)
             ≃ Σ A (λ a → ║f║ |a| = |b|)
             → Σ ║A║ (λ t → ║f║ t = |b|)
             = fiber ║f║ |b|
```

where the first and last maps are `k`-equivalences.

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  fiber-map-trunc-fiber :
    fiber f b → fiber (map-trunc (succ-𝕋 k) f) (unit-trunc b)
  fiber-map-trunc-fiber =
    ( map-Σ-map-base-unit-trunc
      ( λ t → map-trunc (succ-𝕋 k) f t ＝ unit-trunc b)) ∘
    ( tot
      ( λ a →
        ( concat (naturality-unit-trunc (succ-𝕋 k) f a) (unit-trunc b)) ∘
        ( map-effectiveness-trunc k (f a) b) ∘
        ( unit-trunc)))

  abstract
    is-truncation-equivalence-fiber-map-trunc-fiber :
      is-truncation-equivalence k fiber-map-trunc-fiber
    is-truncation-equivalence-fiber-map-trunc-fiber =
      is-truncation-equivalence-comp
        ( map-Σ-map-base-unit-trunc
          ( λ t → map-trunc (succ-𝕋 k) f t ＝ unit-trunc b))
        ( tot
          ( λ a →
            ( concat (naturality-unit-trunc (succ-𝕋 k) f a) (unit-trunc b)) ∘
            ( map-effectiveness-trunc k (f a) b) ∘
            ( unit-trunc)))
        ( is-truncation-equivalence-is-truncation-equivalence-equiv
          ( equiv-tot
            ( λ a →
              ( equiv-concat
                ( naturality-unit-trunc (succ-𝕋 k) f a)
                ( unit-trunc b)) ∘e
              ( effectiveness-trunc k (f a) b)))
          ( λ (a , p) → a , unit-trunc p)
          ( is-equiv-map-equiv (equiv-trunc-Σ k)))
        ( is-truncation-equivalence-map-Σ-map-base-unit-trunc
          ( λ t → map-trunc (succ-𝕋 k) f t ＝ unit-trunc b))

  truncation-equivalence-fiber-map-trunc-fiber :
    truncation-equivalence k
      ( fiber f b)
      ( fiber (map-trunc (succ-𝕋 k) f) (unit-trunc b))
  pr1 truncation-equivalence-fiber-map-trunc-fiber =
    fiber-map-trunc-fiber
  pr2 truncation-equivalence-fiber-map-trunc-fiber =
    is-truncation-equivalence-fiber-map-trunc-fiber

  equiv-trunc-fiber-map-trunc-fiber :
    type-trunc k (fiber f b) ≃
    type-trunc k (fiber (map-trunc (succ-𝕋 k) f) (unit-trunc b))
  equiv-trunc-fiber-map-trunc-fiber =
    equiv-trunc-truncation-equivalence k
      ( truncation-equivalence-fiber-map-trunc-fiber)
```

### Being `k`-connected is invariant under `k`-equivalences

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-is-truncation-equivalence-is-connected :
    (f : A → B) → is-truncation-equivalence k f →
    is-connected k B → is-connected k A
  is-connected-is-truncation-equivalence-is-connected f e =
    is-contr-equiv (type-trunc k B) (map-trunc k f , e)

  is-connected-is-truncation-equivalence-is-connected' :
    (f : A → B) → is-truncation-equivalence k f →
    is-connected k A → is-connected k B
  is-connected-is-truncation-equivalence-is-connected' f e =
    is-contr-equiv' (type-trunc k A) (map-trunc k f , e)

  is-connected-truncation-equivalence-is-connected :
    truncation-equivalence k A B → is-connected k B → is-connected k A
  is-connected-truncation-equivalence-is-connected f =
    is-connected-is-truncation-equivalence-is-connected
      ( map-truncation-equivalence k f)
      ( is-truncation-equivalence-truncation-equivalence k f)

  is-connected-truncation-equivalence-is-connected' :
    truncation-equivalence k A B → is-connected k A → is-connected k B
  is-connected-truncation-equivalence-is-connected' f =
    is-connected-is-truncation-equivalence-is-connected'
      ( map-truncation-equivalence k f)
      ( is-truncation-equivalence-truncation-equivalence k f)
```

### Every `(k+1)`-equivalence is `k`-connected

This is an instance of Proposition 2.30 in {{#cite CORS20}}.

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-connected-map-is-succ-truncation-equivalence :
    is-truncation-equivalence (succ-𝕋 k) f → is-connected-map k f
  is-connected-map-is-succ-truncation-equivalence e b =
    is-connected-truncation-equivalence-is-connected
      ( truncation-equivalence-fiber-map-trunc-fiber f b)
      ( is-connected-map-is-equiv e (unit-trunc b))
```

### A map is `k`-connected if and only if its `k+1`-truncation is

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-connected-map-trunc-succ-is-succ-connected-domain :
    is-connected-map k f →
    is-connected-map k (map-trunc (succ-𝕋 k) f)
  is-connected-map-trunc-succ-is-succ-connected-domain cf t =
    apply-universal-property-trunc-Prop
      ( is-surjective-unit-trunc-succ t)
      ( is-connected-Prop k (fiber (map-trunc (succ-𝕋 k) f) t))
      ( λ (b , p) →
        tr
          ( λ s → is-connected k (fiber (map-trunc (succ-𝕋 k) f) s))
          ( p)
          ( is-connected-truncation-equivalence-is-connected'
            ( truncation-equivalence-fiber-map-trunc-fiber f b)
            ( cf b)))

  is-connected-map-is-connected-map-trunc-succ :
    is-connected-map k (map-trunc (succ-𝕋 k) f) →
    is-connected-map k f
  is-connected-map-is-connected-map-trunc-succ cf' b =
    is-connected-truncation-equivalence-is-connected
      ( truncation-equivalence-fiber-map-trunc-fiber f b)
      ( cf' (unit-trunc b))
```

### The codomain of a `k`-connected map is `(k+1)`-connected if its domain is `(k+1)`-connected

This follows part of the proof of Proposition 2.31 in {{#cite CORS20}}.

**Proof.** Let $f : A → B$ be a $k$-connected map on a $k+1$-connected domain.
To show that the codomain is $k+1$-connected it is enough to show that $f$ is a
$k+1$-equivalence, in other words, that $║f║ₖ₊₁$ is an equivalence. By previous
computations we know that $║f║ₖ₊₁$ is $k$-truncated since the domain is
$k+1$-connected, and that $║f║ₖ₊₁$ is $k$-connected since $f$ is $k$-connected,
so we are done. ∎

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncation-equivalence-succ-is-succ-connected-domain-is-connected-map :
    is-connected-map k f →
    is-connected (succ-𝕋 k) A →
    is-truncation-equivalence (succ-𝕋 k) f
  is-truncation-equivalence-succ-is-succ-connected-domain-is-connected-map
    cf cA =
    is-equiv-is-connected-map-is-trunc-map
      ( is-trunc-map-trunc-succ-is-succ-connected-domain f cA)
      ( is-connected-map-trunc-succ-is-succ-connected-domain cf)

  is-succ-connected-codomain-is-succ-connected-domain-is-connected-map :
    is-connected-map k f →
    is-connected (succ-𝕋 k) A →
    is-connected (succ-𝕋 k) B
  is-succ-connected-codomain-is-succ-connected-domain-is-connected-map cf cA =
    is-connected-is-truncation-equivalence-is-connected' f
      ( is-truncation-equivalence-succ-is-succ-connected-domain-is-connected-map
        ( cf)
        ( cA))
      ( cA)
```

### If `g ∘ f` is `(k+1)`-connected, then `f` is `k`-connected if and only if `g` is `(k+1)`-connected

This is an instance of Proposition 2.31 in {{#cite CORS20}}.

**Proof.** If $g$ is $(k+1)$-connected then by the cancellation property of
$(k+1)$-equivalences, $f$ is a $k+1$-equivalence, and so in particular
$k$-connected.

Conversely, assume $f$ is $k$-connected. We want to show that the fibers of $g$
are $k+1$-connected, so let $c$ be an element of the codomain of $g$. The fibers
of the composite $g ∘ f$ compute as

$$
  \operatorname{fiber}_{g\circ f}(c) ≃
  \sum_{(b , p) : \operatorname{fiber}_{g}(c)}{\operatorname{fiber}_{f}(b)}.
$$

By the previous lemma, since $\operatorname{fiber}_{g\circ f}(c)$ is
$k+1$-connected, $\operatorname{fiber}_{g}(c)$ is $k+1$-connected if the first
projection map of this type is $k$-connected, and its fibers compute to the
fibers of $f$. ∎

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) (cgf : is-connected-map (succ-𝕋 k) (g ∘ f))
  where

  is-succ-truncation-equivalence-right-factor-is-succ-connected-map-left-factor :
    is-connected-map (succ-𝕋 k) g → is-truncation-equivalence (succ-𝕋 k) f
  is-succ-truncation-equivalence-right-factor-is-succ-connected-map-left-factor
    cg =
    is-truncation-equivalence-right-factor g f
      ( is-truncation-equivalence-is-connected-map (g ∘ f) cgf)
      ( is-truncation-equivalence-is-connected-map g cg)

  is-connected-map-right-factor-is-succ-connected-map-left-factor :
    is-connected-map (succ-𝕋 k) g → is-connected-map k f
  is-connected-map-right-factor-is-succ-connected-map-left-factor cg =
    is-connected-map-is-succ-truncation-equivalence f
      ( is-succ-truncation-equivalence-right-factor-is-succ-connected-map-left-factor
        ( cg))

  is-connected-map-right-factor-is-succ-connected-map-right-factor :
    is-connected-map k f → is-connected-map (succ-𝕋 k) g
  is-connected-map-right-factor-is-succ-connected-map-right-factor cf c =
    is-succ-connected-codomain-is-succ-connected-domain-is-connected-map
      ( pr1)
      ( λ p →
        is-connected-equiv
          ( equiv-fiber-pr1 (fiber f ∘ pr1) p)
          ( cf (pr1 p)))
      ( is-connected-equiv' (compute-fiber-comp g f c) (cgf c))
```

As a corollary, if $g ∘ f$ is $(k + 1)$-connected for some $g$, and $f$ is
$k$-connected, then $f$ is a $k+1$-equivalence.

```agda
  is-succ-truncation-equiv-is-succ-connected-comp :
    is-connected-map k f → is-truncation-equivalence (succ-𝕋 k) f
  is-succ-truncation-equiv-is-succ-connected-comp cf =
    is-succ-truncation-equivalence-right-factor-is-succ-connected-map-left-factor
    ( is-connected-map-right-factor-is-succ-connected-map-right-factor cf)
```

### A `k`-equivalence with a section is `k`-connected

**Proof.** If $k ≐ -2$ notice that every map is $-2$-connected. So let
$k ≐ n + 1$ for some truncation level $n$ and let $f$ be our $k$-equivalence
with a section $s$. By assumption, we have a commuting triangle of maps

```text
        A
      ∧   \
   s /     \ f
    /       ∨
  B ======== B.
```

By the previous lemma, since the identity map is $k$-connected, it thus suffices
to show that $s$ is $n$-connected. But by the cancellation property of
$n+1$-equivalences $s$ is an $n+1$-equivalence and $n+1$-equivalences are in
particular $n$-connected. ∎

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-connected-map-section-is-truncation-equivalence-succ :
    (k : 𝕋) (s : section f) →
    is-truncation-equivalence (succ-𝕋 k) f →
    is-connected-map k (map-section f s)
  is-connected-map-section-is-truncation-equivalence-succ k (s , h) e =
    is-connected-map-is-succ-truncation-equivalence s
      ( is-truncation-equivalence-map-section (succ-𝕋 k) (s , h) e)

  is-connected-map-is-truncation-equivalence-section :
    (k : 𝕋) →
    section f → is-truncation-equivalence k f → is-connected-map k f
  is-connected-map-is-truncation-equivalence-section neg-two-𝕋 (s , h) e =
    is-neg-two-connected-map f
  is-connected-map-is-truncation-equivalence-section (succ-𝕋 k) (s , h) e =
    is-connected-map-right-factor-is-succ-connected-map-right-factor f s
      ( is-connected-map-htpy-id h)
      ( is-connected-map-section-is-truncation-equivalence-succ k (s , h) e)
```

## References

- The notion of `k`-equivalence is a special case of the notion of
  `L`-equivalence, where `L` is a reflective subuniverse. These were studied in
  {{#cite CORS20}}.
- The class of `k`-equivalences is
  [left orthogonal](orthogonal-factorization-systems.orthogonal-maps.md) to the
  class of `k`-étale maps. This was shown in {{#cite CR21}}.

{{#bibliography}}
