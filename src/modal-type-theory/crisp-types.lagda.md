# Crisp types

```agda
module modal-type-theory.crisp-types where
```

## Idea

In cohesive type theory, and more generally spatial type theory, one endows
types with an additional structure of cohesion, as modeled by
[cohesive topoi](https://ncatlab.org/nlab/show/cohesive+topos) and
[local topoi](https://ncatlab.org/nlab/show/local+geometric+morphism#LocalTopos)
respectively. Examples include endowing types with real topological structure
{{#cite Shu18}} and endowing types with symmetric simplicial structure
{{#cite Mye21}}.

One starts by introducing two modes of hypotheses: _cohesive_ and _crisp_. A
{{#concept "cohesive" Disambiguation="hypothesis"}} hypothesis is the standard
mode of hypothesis. In formalizations in the agda-unimath library made outside
of this module, every hypothesis may be understood to be a cohesive hypothesis.
These hypotheses come with the implicit assumption that their construction is
respectful of the cohesive structure of the context. Cohesive hypotheses have no
restrictions on the contexts in which they may be formed.

{{#concept "Crisp" Disambiguation="hypothesis"}} hypotheses are, in contrast,
hypotheses that are "indifferent" to the cohesive structure on types, and may
only be judged in contexts made entirely out of crisp hypotheses, called _crisp
contexts_. The indifference to cohesion is made concrete by the
[flat](modal-type-theory.flat-modality.md) and
[sharp](modal-type-theory.sharp-modality.md) modalities.

For instance, in the framework of real-cohesive type theory, where every type is
endowed with real topological structure, a cohesive variable is understood as
one which varies _continuously_ with the real topology of its type. A crisp
variable on the other hand, is one that may vary _discontinuously_ with respect
to this topology.

In Agda, we state that an assumption is crisp by prepending the symbol `@♭` to
the hypothesis. For instance, to hypothesize two elements of an arbitrary type,
one which is crisp and one which is cohesive, we may in a type signature write

```text
  (@♭ l : Level) (@♭ A : UU l) (@♭ x : A) (y : A).
```

Observe that for us to be able to assume `x` is crisp at all, we must also
assume that the type `A` and the universe level `l` are crisp, following the
rule that crisp hypotheses may only be formed in crisp contexts.

So what does it mean for `A` to be a {{#concept "crisp type"}}? Since the
universe of types is itself a type, and every type comes equipped with cohesive
structure, it means that the definition of `A` is indifferent to the cohesive
structure on the universe.

Note that saying a type is crisp is very different to saying that the cohesive
structure of the type is trivial, which one could in one way informally state as
"it consists of only crisp elements". Crisp types whose cohesive structure is
trivial in this sense is captured by
[flat discrete crisp types](modal-type-theory.flat-discrete-crisp-types.md).

## See also

- [Crisp function types](modal-type-theory.crisp-function-types.md)
- [The flat modality](modal-type-theory.flat-modality.md)

## References

{{#bibliography}}

## External links

- [Flat Modality](https://agda.readthedocs.io/en/latest/language/flat.html) on
  the Agda documentation pages.
- [spatial type theory](https://ncatlab.org/nlab/show/spatial+type+theory) at
  $n$Lab.
