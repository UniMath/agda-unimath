# Codiagonals of maps

```agda
module synthetic-homotopy-theory.codiagonals-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.unit-type
open import foundation.commuting-squares-of-maps
open import foundation.action-on-identifications-functions

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.suspension-structures
```

</details>

## Idea

The **codiagonal** of a map `f : A → B` is the unique map `∇ f : B ⊔_A B → B`
equipped with [homotopies](foundation-core.homotopies.md)

```text
  H : ∇ f ∘ inl ~ id
  K : ∇ f ∘ inr ~ id
  L : (H ·r f) ~ (∇ f ·l glue) ∙h (K ·r f)
```

The [fibers](foundation-core.fibers-of-maps.md) of the codiagonal are equivalent
to the [suspensions](synthetic-homotopy-theory.suspensions-of-types.md) of the
fibers of `f`.

## Definitions

### The codiagonal of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  cocone-codiagonal-map : cocone f f B
  pr1 cocone-codiagonal-map = id
  pr1 (pr2 cocone-codiagonal-map) = id
  pr2 (pr2 cocone-codiagonal-map) = refl-htpy

  codiagonal-map : pushout f f → B
  codiagonal-map = cogap f f cocone-codiagonal-map

  compute-inl-codiagonal-map :
    codiagonal-map ∘ inl-pushout f f ~ id
  compute-inl-codiagonal-map =
    compute-inl-cogap f f cocone-codiagonal-map

  compute-inr-codiagonal-map :
    codiagonal-map ∘ inr-pushout f f ~ id
  compute-inr-codiagonal-map =
    compute-inr-cogap f f cocone-codiagonal-map

  compute-glue-codiagonal-map :
    statement-coherence-htpy-cocone f f
      ( cocone-map f f (cocone-pushout f f) codiagonal-map)
      ( cocone-codiagonal-map)
      ( compute-inl-codiagonal-map)
      ( compute-inr-codiagonal-map)
  compute-glue-codiagonal-map =
    compute-glue-cogap f f cocone-codiagonal-map
```

### The codiagonal is the fiberwise suspension

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  private
    P : pushout f f → UU l2
    P x = codiagonal-map f x ＝ b

    c : cocone f f (pushout f f)
    c = cocone-pushout f f

  pushout-1 : {l : Level} →
              universal-property-pushout l
                ( vertical-map-span-flattening-pushout P f f c)
                ( horizontal-map-span-flattening-pushout P f f c)
                ( cocone-flattening-pushout P f f c)
  pushout-1 =
    flattening-lemma-pushout P f f
      ( c)
      ( dependent-up-pushout f f)

  private
    vs = vertical-map-span-flattening-pushout P f f c
    hs = horizontal-map-span-flattening-pushout P f f c
```



```text
                               hs
 Σ A (λ a → P (inl (f a))) --------->  Σ B (λ y → P (inr y))
              |                                 |
              |                                 |
          vs  |                                 |  vc
              |                    ⌜            |
              v                                 v
 Σ B (λ y → P (inl y))     --------->  fiber codiagonal-map b ≡ Σ (pushout f f) P
                               hc
```

```text
                  ϕ
  fiber f b -------------> Σ A (λ a → P (inl (f a)))
     |            ≃                 |
     |                              |
     |                              | vs
     |                              |
     v            ≃                 v
   unit     --------------> Σ B (λ y → P (inl y))
                  ψ
```

```agda
  private
    fiber-is-top-left : fiber f b ≃ Σ A (λ a → P (inl-pushout f f (f a)))
    fiber-is-top-left =
      equiv-tot
        ( λ a → equiv-concat (compute-inl-codiagonal-map f (f a)) b)

    ϕ : fiber f b → Σ A (λ a → P (inl-pushout f f (f a)))
    ϕ = map-equiv fiber-is-top-left

    is-equiv-ϕ : is-equiv ϕ
    is-equiv-ϕ = is-equiv-map-equiv fiber-is-top-left

    is-contr-bottom-left : is-contr (Σ B (λ y → P (inl-pushout f f y)))
    is-contr-bottom-left =
      is-contr-equiv
        ( Σ B (λ y → y ＝ b))
        ( equiv-tot
          ( λ y →
            equiv-concat (inv (compute-inl-codiagonal-map f y)) b))
        ( is-contr-total-path' b)

    bottom-left-is-unit : Σ B (λ y → P (inl-pushout f f y)) ≃ unit
    bottom-left-is-unit =
      terminal-map , is-equiv-terminal-map-is-contr is-contr-bottom-left

    ψ : unit → Σ B (λ y → P (inl-pushout f f y))
    ψ = map-inv-equiv bottom-left-is-unit

    is-equiv-ψ : is-equiv ψ
    is-equiv-ψ = is-equiv-map-inv-equiv bottom-left-is-unit

  left-cocone : cocone terminal-map ϕ (Σ B (λ y → P (inl-pushout f f y)))
  left-cocone =
    ψ , vs ,
    ( λ _ → eq-is-prop (is-prop-is-contr is-contr-bottom-left))

  pushout-2 : {l : Level} →
              universal-property-pushout l
                ( terminal-map)
                ( ϕ)
                ( left-cocone)
  pushout-2 =
    universal-property-pushout-is-equiv'
      ( terminal-map)
      ( ϕ)
      ( left-cocone)
      ( is-equiv-ϕ)
      ( is-equiv-ψ)

  private
    hc = horizontal-map-cocone-flattening-pushout P f f c
    vc = vertical-map-cocone-flattening-pushout P f f c
    c' : cocone terminal-map (hs ∘ ϕ) (Σ (pushout f f) P)
    c' = hc ∘ ψ ,
         vc ,
         ( λ x → concat (foo x) ((vc ∘ hs ∘ ϕ) x)
                             (coherence-square-cocone-flattening-pushout P f f c (ϕ x)))
      where
        foo : (x : fiber f b) →
              ((hc ∘ ψ) ∘ terminal-map) x ＝ (hc ∘ vs) (ϕ x)
        foo x = ap hc (eq-is-prop (is-prop-is-contr is-contr-bottom-left))
    c'' : cocone vs hs (Σ (pushout f f) P)
    c'' = cocone-flattening-pushout P f f c

  pushout-3 : {l : Level} →
              universal-property-pushout l
                ( terminal-map)
                ( hs ∘ ϕ)
                c'
  pushout-3 =
    universal-property-pushout-rectangle-universal-property-pushout-right
      ( terminal-map)
      ( ϕ)
      ( horizontal-map-span-flattening-pushout P f f c)
      ( left-cocone)
      ( cocone-flattening-pushout P f f c)
      pushout-2
      pushout-1
```

{-
    S : UU (l1 ⊔ l2)
    S = Σ A (λ a → P (inl-pushout f f (f a)))

    U : UU l2
    U = Σ B (λ y → P (inl-pushout f f y))

    V : UU l2
    V = Σ B (λ y → P (inr-pushout f f y))

    W : UU (l1 ⊔ l2)
    W = fiber (codiagonal-map f) b

    vms : S → U
    vms = vertical-map-span-flattening-pushout P f f c

    hms : S → V
    hms = horizontal-map-span-flattening-pushout P f f c

    cl : U → W
    cl = horizontal-map-cocone-flattening-pushout P f f c

    cr : V → W
    cr = vertical-map-cocone-flattening-pushout P f f c

    compute-cl : ((y , p) : U) → (inl-pushout f f y , p) ＝ cl (y , p)
    compute-cl (y , p) = refl

    compute-cr : ((y , p) : V) → (inr-pushout f f y , p) ＝ cr (y , p)
    compute-cr (y , p) = refl

  pushout-1 : {l : Level} →
                universal-property-pushout l
                sl
                sr
                (cocone-flattening-pushout P f f c)
  pushout-1 =
    flattening-lemma-pushout P f f
      ( c)
      ( dependent-up-pushout f f)

  private
    S' : UU (l1 ⊔ l2)
    S' = fiber f b



  left-square : cocone {!!} {!!} {!!}
  left-square = {!!}
-}
{-

       S
sl    / \   sr
     /   \
    U     V
     \   /
cl    \ /  cr
       W

-}

{-
  private
    S' : UU (l1 ⊔ l2)
    S' = fiber f b

    U' : UU
    U' = unit

    V' : UU
    V' = unit

    W' : UU (l1 ⊔ l2)
    W' = fiber (codiagonal-map f) b

    sl' : S' → U'
    sl' = terminal-map

    sr' : S' → V'
    sr' = terminal-map

    cl' : U' → W'
    cl' = point ((inl-pushout f f b) , (compute-inl-codiagonal-map f b)) -- point (cl (b , compute-inl-codiagonal-map f b))

    cr' : V' → W'
    cr' = point (cr (b , compute-inr-codiagonal-map f b))

    hS : S → S'
    hS (a , p) = a , concat (inv (compute-inl-codiagonal-map f (f a))) b p

    hU : U → U'
    hU = terminal-map

    hV : V → V'
    hV = terminal-map

    hW : W → W'
    hW = id

    top : coherence-square-maps sr sl cr cl
    top = coherence-square-cocone-flattening-pushout P f f c

    back-left : coherence-square-maps sl hS hU sl'
    back-left = refl-htpy

    back-right : coherence-square-maps sr hS hV sr'
    back-right = refl-htpy

    front-left : coherence-square-maps cl hU hW cl'
    front-left (y , p) = eq-Eq-fiber (codiagonal-map f) b {!!} {!!}
     -- cl (b , ...) ＝ cl (y , p)

    front-right : coherence-square-maps cr hV hW cr'
    front-right (y , p) = {!!}

    bottom : coherence-square-maps sr' sl' cr' cl'
    bottom = {!!}

  pushout-2 : {l : Level} →
    universal-property-pushout l
      terminal-map
      terminal-map
      {!!}
  pushout-2 =
    universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv
      sr'
      sl'
      cl'
      cr'
      sl
      sr
      cl
      cr
      hS
      hU
      hV
      hW
      top
      back-left
      back-right
      front-left
      front-right
      bottom
      {!!}
      {!!}
      {!!}
      {!!}
      {!!}
      pushout-1
-}

{-
       S'
sl'   / \   sr'
     /   \
    U'    V'
     \   /
cl'   \ /  cr'
       W'
-}

{-

  note-1 : Σ A (P ∘ inl-pushout f f ∘ f) →
           Σ B (P ∘ inr-pushout f f)
  note-1 = horizontal-map-span-flattening-pushout P f f c

  bottom-right : UU (l1 ⊔ l2)
  bottom-right = fiber (codiagonal-map f) b

  correct-cocone' : cocone (vertical-map-span-flattening-pushout P f f c) (horizontal-map-span-flattening-pushout P f f c) bottom-right
  correct-cocone' = cocone-flattening-pushout P f f c

  bottom-left : UU l2
  bottom-left = Σ B (λ y → P (inl-pushout f f y))

  top-right : UU l2
  top-right = Σ B (λ y → P (inr-pushout f f y))

  top-left : UU (l1 ⊔ l2)
  top-left = Σ A (λ a → P (inl-pushout f f (f a)))

  horizontal-span : top-left → top-right
  horizontal-span = horizontal-map-span-flattening-pushout P f f c

  horizontal-cocone : bottom-left → bottom-right
  horizontal-cocone = horizontal-map-cocone-flattening-pushout P f f c

  equiv-top-left : fiber f b ≃ top-left
  equiv-top-left = equiv-tot (λ a → equiv-concat (compute-inl-codiagonal-map f (f a)) b)

  equiv-top-right : unit ≃ top-right
  equiv-top-right = (point (b , compute-inr-codiagonal-map f b)) , {!!}

{- terminal-map , (is-equiv-terminal-map-is-contr (is-contr-equiv (Σ B (λ y → y ＝ b)) (equiv-tot (λ y → equiv-concat (compute-inr-codiagonal-map f y)) b) (is-contr-total-path' b))) -}

  equiv-bottom-left : unit ≃ bottom-left
  equiv-bottom-left = (point (b , compute-inl-codiagonal-map f b)) , {!!}
  {- terminal-map , (is-equiv-terminal-map-is-contr (is-contr-equiv (Σ B (λ y → y ＝ b)) (equiv-tot (λ y → equiv-concat (inv (compute-inl-codiagonal-map f y)) b)) (is-contr-total-path' b))) -}

  coh : fiber f b →
        (inl-pushout f f b , compute-inl-codiagonal-map f b) ＝
        (inr-pushout f f b , compute-inr-codiagonal-map f b)
  coh (a , p) = {!!}

  suspension-structure-fiber : suspension-structure (fiber f b) (Σ (pushout f f) P)
  suspension-structure-fiber =
    ((inl-pushout f f b , compute-inl-codiagonal-map f b) ,
    (inr-pushout f f b , compute-inr-codiagonal-map f b) ,
    {!!})

-}

--  bottom-right-equiv : bottom-right ≃
--  bottom-right-equiv = {!equiv-tot!}
```

{-
  private
    S' : UU (l1 ⊔ l2)
    S' = fiber f b

    U' : UU l2
    U' = Σ B (λ y → y ＝ b)

    V' : UU l2
    V' = Σ B (λ y → y ＝ b)

    W' : UU (l1 ⊔ l2)
    W' = fiber (codiagonal-map f) b

    sl' : S' → U'
    sl' (a , p) = (f a , p) -- terminal-map

    sr' : S' → V'
    sr' (a , p) = (f a , p) -- terminal-map

    cl' : U' → W'
    cl' (y , p) = (inl-pushout f f y , compute-inl-codiagonal-map f y ∙ p) -- point (inl-pushout f f b , compute-inl-codiagonal-map f b)

    cr' : V' → W'
    cr' (y , p) = (inr-pushout f f y , compute-inr-codiagonal-map f y ∙ p) -- point (inr-pushout f f b , compute-inr-codiagonal-map f b)

    hS : S → S'
    hS (a , p) = a , concat (inv (compute-inl-codiagonal-map f (f a))) b p

    hU : U → U'
    hU (y , p) = y , concat (inv (compute-inl-codiagonal-map f y)) b p -- terminal-map

    hV : V → V'
    hV (y , p) = y , concat (inv (compute-inr-codiagonal-map f y)) b p -- terminal-map

    hW : W → W'
    hW = id

    top : coherence-square-maps sr sl cr cl
    top = coherence-square-cocone-flattening-pushout P f f c

    back-left : coherence-square-maps sl hS hU sl'
    back-left = {!!}

    back-right : coherence-square-maps sr hS hV sr'
    back-right = {!!}

    front-left : coherence-square-maps cl hU hW cl'
    front-left (y , p) = {!!}
-}
