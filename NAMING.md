# Naming conventions

A good naming convention is essential for being able to navigate and maintain
the library, and for being able to make progress with your formalization
project. Good names provide coincise descriptions of an entry's purpose, and
help making the code in the library readable.

The library contains, for example, an entry `is-iso-hom-Ring` for the predicate
that a ring homomorphism is an isomorphsim. The most significant aspect of this
predicate is the assertion that something is an isomorphism. Furthermore, we
make this assertion about ring homomorphisms. The name `is-iso-hom-Ring` is
therefore a logical name for the predicate that a ring homomorphism is an
isomorphism.

In our naming scheme we strive for a direct correspondence between a
constructions's name and its type. Take, for example, the proof that the
successor function on integers is an equivalence. It has the type
`is-equiv succ-ℤ`, so we name it `is-equiv-succ-ℤ`.

We may also reflect the type of hypotheses used in the construction within the
name. If we wish to do so, we name the hypotheses after we have named the type
of the construction. For instance, `is-equiv-is-contr-map` is a function of type
`is-contr-map f → is-equiv f`, where `f` is a given function. Notice how the
term `is-equiv-is-contr-map H` places the descriptor `is-contr-map` right next
to the variable `H` it refers to. Another advantage is that the name says
immediately what it constructs.

In general, our naming scheme follows the following pattern:

```text
  [name]-[type]-[hypotheses]-[Important-Concept]
```

In this naming scheme all parts are optional, but the order of the different
parts of the name must be respected.

We saw, for example, that the prediate `is-iso-hom-Ring` has the part `Ring`
capitalized. This signifies that the predicate is about rings. This name follows
the scheme `[name]-[hypotheses]-[Important-Concept]`. Note that there is also
the entry `is-iso-prop-hom-Ring`. This is a predicate that returns for each ring
homomorphism the _proposition_ that it is an isomorphism, and therefore it
follows the scheme `[name]-[type]-[hypotheses]-[Important-Concept]`. Now we can
guess what a construction named `hom-iso-Ring` should be about: It should be a
construction that constructs the underlying homomorphism of an isomorphisms of
rings. This name follows the pattern `[type]-[hypotheses]-[Important-Concept]`.

We should also mention that, while abbreviations might seem like a good way to
shorten names, we use them sparingly. They might save a couple of keystrokes for
the author, but in the grand scheme of things, they will likely compromise
readability and maintainability, especially for newcomers and maintainers. We
aim for clarity, not brevity.

## Overview of our naming conventions

- Names are unique; we steer clear of namespace overloading.

- Names should accurately convey the concept of its construction.

- We use US English spelling of words in names.

- When an entry is predominantly about objects of an important concept, the
  names of these concepts can be capitalized. Usually, these are categories like
  `Prop`, `Set`, `Semigroup`, `Monoid`, `Group`, `Preorder`, `Poset`,
  `Precategory`, `Category`, `Directed-Graph`, `Undirected-Graph`, and so on.

- As a general rule of thumb, names should start out with an all lowercase
  portion with words separated by hyphens, and may have a capitalized portion at
  the end that describes which larger mathematical framework the definition
  takes place in -- for instance, if it is constructed internally to a certain
  subuniverse or category of mathematical objects.

- The start of a name describes the object that is being constructed. For some
  theorems, the latter part of a name describes the hypotheses.

- We use Unicode symbols sparingly and only when they align with established
  mathematical practice.

- Just as we do with abbreviations, we use special symbols sparingly in names.

- If a symbol is not available, we describe the concept concisely in words.

- We prioritize the readability of the code and avoid subtly different
  variations of the same symbol. An important exception is the use of the
  [full width equals sign](https://codepoints.net/U+ff1d) for the identity type,
  as the standard equals sign is a reserved symbol in Agda.

If you are unsure about what to name your entry, ask us on the Univalent Agda
discord server. One of the most commonly asked questions is what to name a
certain thing.

## Naming conventions we try to avoid

- Using Unicode characters in names is entirely permissible, but we recommend
  restraint to maintain readability. Just a few well-placed symbols can often
  express a lot.

- To enhance conceptual clarity, we suggest names of constructions avoid
  referring to variable names. This makes code more understandable, even at a
  glance, and easier to work with in subsequent code.

- Using the projection functions `pr1` and `pr2`, particularly their
  compositions, can lead to short code, but we recommend to avoid doing so. When
  constructions contain a lot of projections throughout their definition, the
  projections reveal little of what is going on in that part of the projections.
  We therefore prefer naming the projections. When a type of the form `Σ A B` is
  given a name, naming its projections too can enhance readability and will
  provide more informative responses when jumping to the definition.
  Furthermore, it makes it easier to change the definition later on.

- Lastly, we recommend not naming constructions after infix notation of
  operations included in them. Preferring primary prefix notation over infix
  notation can help keep our code consistent. For example, it's preferred to use
  `commutative-prod` instead of `commutative-×` for denoting the commutativity
  of cartesian products.

- Names never reference variables.