# The pseudometric completion of a pseudometric space

```agda
module metric-spaces.pseudometric-completion-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
```

</details>

## Idea

The
{{#concept "pseudometric completion" Disambiguation="of a pseudometric space" Agda=pseudometric-completion-Pseudometric-Space}}
of a [pseudometric space](metric-spaces.pseudometric-spaces.md) `M` is the
pseudometric space of
[Cauchy approximations](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
in `M` where two Cauchy approximations `x` and `y` are in a
[`d`-neighborhood](metric-spaces.rational-neighborhood-relations.md) of one
another if for all `δ ε : ℚ⁺`, `x δ` and `y ε` are in a
`(δ + ε + d)`-neighborhood of one another in `M`.

Any Cauchy approximation in the pseudometric completion has a
[limit](metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces.md).

## Definition

### The pseudometric completion neighborhood relation on the type of Cauchy approximations in a pseudometric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  neighborhood-prop-pseudometric-completion-Pseudometric-Space :
    Rational-Neighborhood-Relation l2
      (cauchy-approximation-Pseudometric-Space M)
  neighborhood-prop-pseudometric-completion-Pseudometric-Space
    d x y =
      Π-Prop
        ( ℚ⁺)
        ( λ δ →
          Π-Prop
            ( ℚ⁺)
            ( λ ε →
              neighborhood-prop-Pseudometric-Space
                ( M)
                ( δ +ℚ⁺ ε +ℚ⁺ d)
                ( map-cauchy-approximation-Pseudometric-Space M x δ)
                ( map-cauchy-approximation-Pseudometric-Space M y ε)))

  neighborhood-pseudometric-completion-Pseudometric-Space :
    ℚ⁺ → Relation l2 (cauchy-approximation-Pseudometric-Space M)
  neighborhood-pseudometric-completion-Pseudometric-Space d x y =
    type-Prop
      ( neighborhood-prop-pseudometric-completion-Pseudometric-Space
        ( d)
        ( x)
        ( y))
```

## Properties

### The neighborhood relation is reflexive

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  abstract
    is-reflexive-neighborhood-pseudometric-completion-Pseudometric-Space :
      (d : ℚ⁺) (x : cauchy-approximation-Pseudometric-Space M) →
      neighborhood-pseudometric-completion-Pseudometric-Space M d x x
    is-reflexive-neighborhood-pseudometric-completion-Pseudometric-Space
      d x δ ε =
      let
        xδ = map-cauchy-approximation-Pseudometric-Space M x δ
        xε = map-cauchy-approximation-Pseudometric-Space M x ε
      in
        monotonic-neighborhood-Pseudometric-Space M xδ xε
          ( δ +ℚ⁺ ε)
          ( δ +ℚ⁺ ε +ℚ⁺ d)
          ( le-right-add-rational-ℚ⁺ _ d)
          ( is-cauchy-approximation-map-cauchy-approximation-Pseudometric-Space
            ( M)
            ( x)
            ( δ)
            ( ε))
```

### The neighborhood relation is symmetric

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

    abstract
      is-symmetric-neighborhood-pseudometric-completion-Pseudometric-Space :
        (d : ℚ⁺) (x y : cauchy-approximation-Pseudometric-Space M) →
        neighborhood-pseudometric-completion-Pseudometric-Space M d x y →
        neighborhood-pseudometric-completion-Pseudometric-Space M d y x
      is-symmetric-neighborhood-pseudometric-completion-Pseudometric-Space
        d x y Ndxy δ ε =
        let
          xε = map-cauchy-approximation-Pseudometric-Space M x ε
          yδ = map-cauchy-approximation-Pseudometric-Space M y δ
        in
          tr
            ( λ d' → neighborhood-Pseudometric-Space M d' yδ xε)
            ( ap (_+ℚ⁺ d) (commutative-add-ℚ⁺ ε δ))
            ( symmetric-neighborhood-Pseudometric-Space M _ xε yδ (Ndxy ε δ))
```

### The neighborhood relation is triangular

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  abstract
    is-triangular-neighborhood-pseudometric-completion-Pseudometric-Space :
      (x y z : cauchy-approximation-Pseudometric-Space M) →
      (dxy dyz : ℚ⁺) →
      neighborhood-pseudometric-completion-Pseudometric-Space M dyz y z →
      neighborhood-pseudometric-completion-Pseudometric-Space M dxy x y →
      neighborhood-pseudometric-completion-Pseudometric-Space
        ( M)
        ( dxy +ℚ⁺ dyz)
        ( x)
        ( z)
    is-triangular-neighborhood-pseudometric-completion-Pseudometric-Space
      x y z dxy dyz Ndyz Ndxy δ ε =
        let
          xδ = map-cauchy-approximation-Pseudometric-Space M x δ
          zε = map-cauchy-approximation-Pseudometric-Space M z ε
        in
        saturated-neighborhood-Pseudometric-Space
          ( M)
          ( δ +ℚ⁺ ε +ℚ⁺ (dxy +ℚ⁺ dyz))
          ( xδ)
          ( zε)
          ( λ θ →
            let
              (θ₂ , θ₂+θ₂<θ) = bound-double-le-ℚ⁺ θ
              (θa , θb , θa+θb=θ₂) = split-ℚ⁺ θ₂
              yθa = map-cauchy-approximation-Pseudometric-Space M y θa
            in
              monotonic-neighborhood-Pseudometric-Space
                ( M)
                ( xδ)
                ( zε)
                ( (δ +ℚ⁺ θa +ℚ⁺ dxy +ℚ⁺ θb) +ℚ⁺ (θa +ℚ⁺ ε +ℚ⁺ dyz +ℚ⁺ θb))
                ( δ +ℚ⁺ ε +ℚ⁺ (dxy +ℚ⁺ dyz) +ℚ⁺ θ)
                ( tr
                  ( λ q → le-ℚ⁺ q (δ +ℚ⁺ ε +ℚ⁺ (dxy +ℚ⁺ dyz) +ℚ⁺ θ))
                  ( equational-reasoning
                    ((δ +ℚ⁺ ε) +ℚ⁺ (dxy +ℚ⁺ dyz)) +ℚ⁺ (θ₂ +ℚ⁺ θ₂)
                    ＝
                      ((δ +ℚ⁺ dxy) +ℚ⁺ (ε +ℚ⁺ dyz)) +ℚ⁺
                      ((θa +ℚ⁺ θb) +ℚ⁺ (θa +ℚ⁺ θb))
                      by
                        ap-add-ℚ⁺
                          ( interchange-law-add-add-ℚ⁺ δ ε dxy dyz)
                          ( inv (ap-add-ℚ⁺ θa+θb=θ₂ θa+θb=θ₂))
                    ＝
                      ((δ +ℚ⁺ dxy) +ℚ⁺ (θa +ℚ⁺ θb)) +ℚ⁺
                      ((ε +ℚ⁺ dyz) +ℚ⁺ (θa +ℚ⁺ θb))
                      by interchange-law-add-add-ℚ⁺ _ _ _ _
                    ＝
                      ((δ +ℚ⁺ θa) +ℚ⁺ (dxy +ℚ⁺ θb)) +ℚ⁺
                      ((ε +ℚ⁺ θa) +ℚ⁺ (dyz +ℚ⁺ θb))
                      by
                        ap-add-ℚ⁺
                          ( interchange-law-add-add-ℚ⁺ _ _ _ _)
                          ( interchange-law-add-add-ℚ⁺ _ _ _ _)
                    ＝
                      (δ +ℚ⁺ θa +ℚ⁺ dxy +ℚ⁺ θb) +ℚ⁺
                      ((θa +ℚ⁺ ε) +ℚ⁺ (dyz +ℚ⁺ θb))
                      by
                        ap-add-ℚ⁺
                          ( inv (associative-add-ℚ⁺ _ _ _))
                          ( ap-add-ℚ⁺ (commutative-add-ℚ⁺ _ _) refl)
                    ＝ (δ +ℚ⁺ θa +ℚ⁺ dxy +ℚ⁺ θb) +ℚ⁺ (θa +ℚ⁺ ε +ℚ⁺ dyz +ℚ⁺ θb)
                      by ap-add-ℚ⁺ refl (inv (associative-add-ℚ⁺ _ _ _)))
                  ( preserves-le-right-add-ℚ
                    ( rational-ℚ⁺ (δ +ℚ⁺ ε +ℚ⁺ (dxy +ℚ⁺ dyz)))
                    ( rational-ℚ⁺ (θ₂ +ℚ⁺ θ₂))
                    ( rational-ℚ⁺ θ)
                    ( θ₂+θ₂<θ)))
                ( triangular-neighborhood-Pseudometric-Space M xδ yθa zε
                  ( δ +ℚ⁺ θa +ℚ⁺ dxy +ℚ⁺ θb)
                  ( θa +ℚ⁺ ε +ℚ⁺ dyz +ℚ⁺ θb)
                  ( monotonic-neighborhood-Pseudometric-Space M yθa zε
                    ( θa +ℚ⁺ ε +ℚ⁺ dyz)
                    ( θa +ℚ⁺ ε +ℚ⁺ dyz +ℚ⁺ θb)
                    ( le-left-add-ℚ⁺ (θa +ℚ⁺ ε +ℚ⁺ dyz) θb)
                    ( Ndyz θa ε))
                  ( monotonic-neighborhood-Pseudometric-Space M xδ yθa
                    ( δ +ℚ⁺ θa +ℚ⁺ dxy)
                    ( δ +ℚ⁺ θa +ℚ⁺ dxy +ℚ⁺ θb)
                    ( le-left-add-ℚ⁺ (δ +ℚ⁺ θa +ℚ⁺ dxy) θb)
                    ( Ndxy δ θa))))
```

### The neighborhood relation is saturated

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  abstract
    is-saturated-neighborhood-pseudometric-completion-Pseudometric-Space :
      ( ε : ℚ⁺) (x y : cauchy-approximation-Pseudometric-Space M) →
      ( (δ : ℚ⁺) →
        neighborhood-pseudometric-completion-Pseudometric-Space
          ( M)
          ( ε +ℚ⁺ δ)
          ( x)
          ( y)) →
      neighborhood-pseudometric-completion-Pseudometric-Space M ε x y
    is-saturated-neighborhood-pseudometric-completion-Pseudometric-Space
      d x y H δ ε =
        let
          xδ = map-cauchy-approximation-Pseudometric-Space M x δ
          yε = map-cauchy-approximation-Pseudometric-Space M y ε
        in
          saturated-neighborhood-Pseudometric-Space M
            ( δ +ℚ⁺ ε +ℚ⁺ d)
            ( xδ)
            ( yε)
            ( λ θ →
              tr
                ( λ η → neighborhood-Pseudometric-Space M η xδ yε)
                ( inv (associative-add-ℚ⁺ _ _ _))
                ( H θ δ ε))
```

### The pseudometric completion of a pseudometric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  pseudometric-completion-Pseudometric-Space :
    Pseudometric-Space (l1 ⊔ l2) l2
  pseudometric-completion-Pseudometric-Space =
    ( cauchy-approximation-Pseudometric-Space M ,
      neighborhood-prop-pseudometric-completion-Pseudometric-Space M ,
      is-reflexive-neighborhood-pseudometric-completion-Pseudometric-Space M ,
      is-symmetric-neighborhood-pseudometric-completion-Pseudometric-Space M ,
      is-triangular-neighborhood-pseudometric-completion-Pseudometric-Space M ,
      is-saturated-neighborhood-pseudometric-completion-Pseudometric-Space M)
```

### The isometry from a pseudometric space to its pseudometric completion

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  map-pseudometric-completion-Pseudometric-Space :
    type-Pseudometric-Space M → cauchy-approximation-Pseudometric-Space M
  map-pseudometric-completion-Pseudometric-Space =
    const-cauchy-approximation-Pseudometric-Space M

  abstract
    preserves-neighborhood-map-pseudometric-completion-Pseudometric-Space :
      (d : ℚ⁺) (x y : type-Pseudometric-Space M) →
      neighborhood-Pseudometric-Space M d x y →
      neighborhood-pseudometric-completion-Pseudometric-Space
        ( M)
        ( d)
        ( map-pseudometric-completion-Pseudometric-Space x)
        ( map-pseudometric-completion-Pseudometric-Space y)
    preserves-neighborhood-map-pseudometric-completion-Pseudometric-Space
      d x y Nxy δ ε =
      monotonic-neighborhood-Pseudometric-Space M x y d (δ +ℚ⁺ ε +ℚ⁺ d)
        ( le-right-add-ℚ⁺ (δ +ℚ⁺ ε) d)
        ( Nxy)

    reflects-neighborhood-map-pseudometric-completion-Pseudometric-Space :
      (d : ℚ⁺) (x y : type-Pseudometric-Space M) →
      neighborhood-pseudometric-completion-Pseudometric-Space
        ( M)
        ( d)
        ( map-pseudometric-completion-Pseudometric-Space x)
        ( map-pseudometric-completion-Pseudometric-Space y) →
      neighborhood-Pseudometric-Space M d x y
    reflects-neighborhood-map-pseudometric-completion-Pseudometric-Space
      d x y Nxy =
      saturated-neighborhood-Pseudometric-Space M d x y
        ( λ δ →
          let
            (δ₁ , δ₂ , δ₁+δ₂=δ) = split-ℚ⁺ δ
          in
            tr
              ( λ ε → neighborhood-Pseudometric-Space M ε x y)
              ( commutative-add-ℚ⁺ _ _ ∙ ap (d +ℚ⁺_) δ₁+δ₂=δ)
              ( Nxy δ₁ δ₂))

    is-isometry-map-pseudometric-completion-Pseudometric-Space :
      is-isometry-Pseudometric-Space
        ( M)
        ( pseudometric-completion-Pseudometric-Space M)
        ( map-pseudometric-completion-Pseudometric-Space)
    is-isometry-map-pseudometric-completion-Pseudometric-Space d x y =
      ( ( preserves-neighborhood-map-pseudometric-completion-Pseudometric-Space
          ( d)
          ( x)
          ( y)) ,
        (reflects-neighborhood-map-pseudometric-completion-Pseudometric-Space
          ( d)
          ( x)
          ( y)))

  isometry-pseudometric-completion-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( M)
      ( pseudometric-completion-Pseudometric-Space M)
  isometry-pseudometric-completion-Pseudometric-Space =
    ( map-pseudometric-completion-Pseudometric-Space ,
      is-isometry-map-pseudometric-completion-Pseudometric-Space)
```

### Any Cauchy approximation in the pseudometric completion of a pseudometric space has a limit

```agda
module _
  { l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  ( U :
    cauchy-approximation-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space M))
  where

  map-cauchy-approximation-pseudometric-completion-Pseudometric-Space :
    ℚ⁺ → ℚ⁺ → type-Pseudometric-Space M
  map-cauchy-approximation-pseudometric-completion-Pseudometric-Space ε =
    map-cauchy-approximation-Pseudometric-Space M
      ( map-cauchy-approximation-Pseudometric-Space
        ( pseudometric-completion-Pseudometric-Space M)
        ( U)
        ( ε))

  is-cauchy-map-cauchy-approximation-pseudometric-completion-Pseudometric-Space :
    (δ ε d₁ d₂ : ℚ⁺) →
    neighborhood-Pseudometric-Space
      ( M)
      ( d₁ +ℚ⁺ d₂ +ℚ⁺ (δ +ℚ⁺ ε))
      ( map-cauchy-approximation-pseudometric-completion-Pseudometric-Space
        ( δ)
        ( d₁))
      ( map-cauchy-approximation-pseudometric-completion-Pseudometric-Space
        ( ε)
        ( d₂))
  is-cauchy-map-cauchy-approximation-pseudometric-completion-Pseudometric-Space
    =
    is-cauchy-approximation-map-cauchy-approximation-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space M)
      ( U)

  map-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space :
    ℚ⁺ → type-Pseudometric-Space M
  map-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space d =
    let
      (d₁ , d₂ , _) = split-ℚ⁺ d
    in
      map-cauchy-approximation-pseudometric-completion-Pseudometric-Space d₂ d₁

  is-cauchy-map-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space :
    is-cauchy-approximation-Pseudometric-Space
      ( M)
      ( map-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space)
  is-cauchy-map-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
    δ ε =
    let
      (δ₁ , δ₂ , δ₁+δ₂=δ) = split-ℚ⁺ δ
      (ε₁ , ε₂ , ε₁+ε₂=ε) = split-ℚ⁺ ε

      lemma-δ+ε :
        (δ₁ +ℚ⁺ ε₁ +ℚ⁺ (δ₂ +ℚ⁺ ε₂)) ＝ δ +ℚ⁺ ε
      lemma-δ+ε =
        ( interchange-law-add-add-ℚ⁺
          ( δ₁)
          ( ε₁)
          ( δ₂)
          ( ε₂)) ∙
        ( ap-binary
          ( add-ℚ⁺)
          ( δ₁+δ₂=δ)
          ( ε₁+ε₂=ε))
    in
      tr
        ( is-upper-bound-dist-Pseudometric-Space
          ( M)
          ( map-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
            ( δ))
          ( map-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
            ( ε)))
        ( lemma-δ+ε)
        ( is-cauchy-map-cauchy-approximation-pseudometric-completion-Pseudometric-Space
          _ _ _ _)

  lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space M
  lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space =
    ( map-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space ,
      is-cauchy-map-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space)

  is-limit-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space :
    is-limit-cauchy-approximation-Pseudometric-Space
      ( pseudometric-completion-Pseudometric-Space M)
      ( U)
      ( lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space)
  is-limit-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
    δ ε η θ =
    let
      (θ₁ , θ₂ , θ₁+θ₂=θ) = split-ℚ⁺ θ

      lemma-η+θ+δ :
        ( η +ℚ⁺ θ₁ +ℚ⁺ (δ +ℚ⁺ θ₂)) ＝ η +ℚ⁺ θ +ℚ⁺ δ
      lemma-η+θ+δ =
        ( interchange-law-add-add-ℚ⁺ η θ₁ δ θ₂) ∙
        ( ap
          ( add-ℚ⁺ (η +ℚ⁺ δ))
          ( θ₁+θ₂=θ)) ∙
        ( associative-add-ℚ⁺ η δ θ) ∙
        ( ap
          ( add-ℚ⁺ η)
          ( commutative-add-ℚ⁺ δ θ)) ∙
        ( inv (associative-add-ℚ⁺ η θ δ))

      lemma-lim :
        neighborhood-Pseudometric-Space M
          ( η +ℚ⁺ θ +ℚ⁺ δ)
          ( map-cauchy-approximation-pseudometric-completion-Pseudometric-Space
            ( δ)
            ( η))
          ( map-cauchy-approximation-pseudometric-completion-Pseudometric-Space
            ( θ₂)
            ( θ₁))
      lemma-lim =
        tr
          ( is-upper-bound-dist-Pseudometric-Space M
            ( map-cauchy-approximation-pseudometric-completion-Pseudometric-Space
              ( δ)
              ( η))
            ( map-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
              ( θ)))
          ( lemma-η+θ+δ)
          ( is-cauchy-map-cauchy-approximation-pseudometric-completion-Pseudometric-Space
            _ _ _ _)
    in
      tr
        ( is-upper-bound-dist-Pseudometric-Space M
          ( map-cauchy-approximation-pseudometric-completion-Pseudometric-Space
            ( δ)
            ( η))
          ( map-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
            ( θ)))
        ( associative-add-ℚ⁺
          ( η +ℚ⁺ θ)
          ( δ)
          ( ε))
        ( monotonic-neighborhood-Pseudometric-Space M
          ( map-cauchy-approximation-pseudometric-completion-Pseudometric-Space
            ( δ)
            ( η))
          ( map-lim-cauchy-approximation-pseudometric-completion-Pseudometric-Space
            ( θ))
          ( η +ℚ⁺ θ +ℚ⁺ δ)
          ( η +ℚ⁺ θ +ℚ⁺ δ +ℚ⁺ ε)
          ( le-left-add-ℚ⁺ ( η +ℚ⁺ θ +ℚ⁺ δ) ε)
          ( lemma-lim))
```
